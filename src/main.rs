#![feature(mixed_integer_ops)]
#![feature(let_chains)]
#![recursion_limit = "100000000000"]
#![allow(warnings)]

use rlimit::{setrlimit, Resource, INFINITY};
use std::cmp::max;
use std::collections::{BTreeMap, HashMap};
use std::env;
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::path::PathBuf;

use structopt::clap::arg_enum;
use structopt::StructOpt;

mod lean;
//mod lru;
mod phony_rec;
mod term;
mod zk;

#[derive(Debug, StructOpt)]
struct Options {
    /// Input file
    #[structopt(parse(from_os_str), name = "PATH")]
    path: PathBuf,

    #[structopt(name = "COMMAND")]
    command: Command,

    #[structopt()]
    theorem: Option<String>,

    #[structopt(long, use_delimiter = true)]
    sizes: Option<Vec<usize>>,
}

arg_enum! {
    #[derive(PartialEq, Eq, Debug)]
    pub enum Command {
        Prove,
        Sim,
        Export,
        Count,
        List,
    }
}

// TODO: make non-io error...
fn main() -> io::Result<()> {
    env_logger::init();

    let options = Options::from_args();
    let path_buf = options.path.clone();

    let res = setrlimit(Resource::STACK, INFINITY, INFINITY);
    //println!("got: {:?}", res);
    //panic!("");
    //
    let mut file = File::open(options.path)?;
    let mut buf = Vec::new();
    file.read_to_end(&mut buf);
    let mut encoding = lean::LeanEncoding::parse(std::str::from_utf8(&buf).unwrap()).unwrap();

    let names = encoding.theorem_names();
    let mut size_cache = Some(hashconsing::hash_coll::HConMap::default());
    let mut term_cache = Some(HashMap::new());
    let mut smallest = vec![];
    let mut failed_to_export = 0;
    let mut fails = vec![];
    let mut failed_sim: Vec<String> = vec![];

    // number of theorem that use quot
    let mut num_quot = 0;

    if matches!(options.command, Command::List) {
        for name in &names {
            println!("{}", name);
        }
        //for (i, name) in names.iter().enumerate() {
        //    let mut inductives = HashMap::new();
        //    let mut axioms = HashMap::new();
        //    //27269/97903
        //    //for (i, name) in names.iter().enumerate() {
        //    //println!("[{}/{}] Exporting: {}", i, names.len(), name);
        //    match encoding.export_theorem(&name, &mut axioms, &mut inductives, &mut term_cache) {
        //        Ok(theorem) => {
        //            println!("[{}/{}] Getting: {}", i, names.len(), name);
        //            let size = theorem.size(&mut size_cache);
        //            println!("...size {}", size);
        //            smallest.push((name, size));
        //        }
        //        Err(err) => {
        //            if err.contains("quot") {
        //                num_quot += 1;
        //            }
        //            println!("Failed to export {}: {}", name, err);
        //            failed_to_export += 1;
        //        }
        //    }
        //}

        //println!("PRINTING:");
        //// print them comma separated
        //smallest.sort_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap());

        //for (name, size) in smallest {
        //    println!("{},{}", name, size);
        //}
        return Ok(());
    }

    if let Some(definition_name) = options.theorem {
        let mut inductives = HashMap::new();
        let mut axioms = HashMap::new();
        let exported = encoding
            .export_theorem(
                &definition_name,
                &mut axioms,
                &mut inductives,
                &mut term_cache,
            )
            .unwrap();
        match options.command {
            Command::Prove => {
                println!(
                    "proving theorem {}... (estimated size {})",
                    definition_name,
                    exported.size(&mut size_cache)
                );
                exported.prove().unwrap();
            }

            Command::Sim => {
                zk::Exporter::simulate(exported.clone()).unwrap();
                println!("Success!");
            }
            Command::Export => {
                println!(
                    "{}",
                    zk::Exporter::export(exported.clone()).unwrap().serialize()
                );
            }
            Command::Count => {
                let zk_in = zk::Exporter::export(exported.clone()).unwrap();
                println!(
                    "{},{},{},{},{},{},{},{},{},{}",
                    max(zk_in.rules.len(), 1),
                    max(zk_in.terms.len(), 1),
                    max(zk_in.contexts.nodes.len(), 1),
                    max(zk_in.lifts.len(), 1),
                    max(zk_in.inductives.len(), 1),
                    max(zk_in.public_terms.len(), 1),
                    max(zk_in.ind_rules.nodes.len(), 1),
                    max(zk_in.ind_nnrs.nodes.len(), 1),
                    max(zk_in.ind_nrs.nodes.len(), 1),
                    max(zk_in.axioms.len(), 1),
                );
            }
            Command::List => {
                panic!("Cannot list with specific theorem")
            }
        }
        return Ok(());
    } else {
        for (i, name) in names.iter().enumerate() {
            let mut inductives = HashMap::new();
            let mut axioms = HashMap::new();
            //27269/97903
            //for (i, name) in names.iter().enumerate() {
            println!("[{}/{}] Exporting: {}", i, names.len(), name);
            match encoding.export_theorem(&name, &mut axioms, &mut inductives, &mut term_cache) {
                Ok(theorem) => {
                    //println!("[{}/{}] Getting: {}", i, names.len(), name);
                    let size = theorem.size(&mut size_cache);
                    println!("...size {}", size);
                    smallest.push((name, size));
                }
                Err(err) => {
                    if err.contains("quot") {
                        num_quot += 1;
                    }
                    println!("Failed to export {}: {}", name, err);
                    failed_to_export += 1;
                }
            }
        }

        smallest.sort_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap());
        //println!("sorted: {:?}", &smallest[..]);

        let mut skipped_typing_eval_elim = 0;
        let mut skipped_simplify_eval_elim = 0;
        // prove theorems one by one...
        for (i, (name, size)) in smallest.iter().enumerate() {
            let mut inductives = HashMap::new();
            let mut axioms = HashMap::new();
            // skip ones that are just very large constants...
            // we can't handle the size
            if name.contains("max_steps")
                || name.contains("std_range")
                || name.contains("std.priority.max")
                || name.contains("unsigned_sz")
                || name.contains("unsigned")
                || name.contains("name.below")
                || name.contains("name.ibelow")
            {
                println!("skipping {}", name);
                continue;
            }
            if let Ok(theorem) = encoding.export_theorem(
                &name,
                &mut axioms,
                &mut inductives,
                &mut Some(HashMap::new()),
            ) {
                //if !name.starts_with("mz") {
                //    continue;
                //}
                println!("[{}/{}] Proving: {}, size: {}", i, names.len(), name, size);
                //println!("term: {:?} :: {:?}", theorem.val, theorem.ty);
                //println!("theorem: {:?}", theorem);
                if let Err(e) = theorem.prove() {
                    if e.contains("eval eliminator") {
                        println!("error: {}", e);
                        if e.contains("Simplify Type error") {
                            println!("Simplify eval elim skip");
                            skipped_simplify_eval_elim += 1;
                        } else {
                            println!("Typing eval elim skip...");
                            skipped_typing_eval_elim += 1;
                        }
                    } else {
                        fails.push(name);
                        println!("Failed! Error: {}", e);
                        //panic!("{}", e);
                        //continue;
                    }
                }
                println!("proven!");
                println!("doing zk sim...");
                let sim_res = zk::Exporter::simulate(theorem).unwrap();
                //if sim_res.is_ok() {
                //    println!("proven in sim!");
                //} else {
                //    println!("failed in sim!, got {:?}", sim_res);
                //    failed_sim.push(name.to_string());
                //};
            }
        }

        println!(
            "failed to export {}/{} thms",
            failed_to_export,
            names.len() + failed_to_export
        );
        println!(
            "proved {}/{} thms",
            names.len() - skipped_typing_eval_elim - skipped_simplify_eval_elim,
            names.len()
        );
        println!(
            "skipped simplify elim (not an issue): {}/{} thms",
            skipped_simplify_eval_elim,
            names.len()
        );
        println!(
            "skipped typing eval elim (is an issue): {}/{} thms",
            skipped_typing_eval_elim,
            names.len()
        );
        println!("real fail: {}/{} thms", fails.len(), names.len());
        println!("fails: {:?}", fails);
        println!("failed sim: {:?}", failed_sim);
        println!("quots: {:?}", num_quot);
    }

    Ok(())
}
