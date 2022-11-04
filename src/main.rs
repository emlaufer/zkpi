#![feature(mixed_integer_ops)]
#![feature(let_chains)]
#![recursion_limit = "100000000000"]

use std::collections::{BTreeMap, HashMap};
use std::env;
use std::fs::File;
use std::io;
use std::io::prelude::*;

mod lean;
//mod lru;
mod phony_rec;
mod term;
mod zk;

// TODO: make non-io error...
fn main() -> io::Result<()> {
    env_logger::init();

    let args: Vec<String> = env::args().collect();
    if args.len() < 2 || args.len() > 3 {
        println!("Usage: crabpi [lean.out] [name]");
        return Ok(());
    }

    let mut file = File::open(&args[1])?;
    let mut buf = Vec::new();
    file.read_to_end(&mut buf);
    let mut encoding = lean::LeanEncoding::parse(std::str::from_utf8(&buf).unwrap()).unwrap();

    println!("got: {:?}", encoding.theorem_names());
    let names = encoding.theorem_names();
    let mut size_cache = Some(hashconsing::hash_coll::HConMap::default());
    let mut term_cache = Some(HashMap::new());
    //let mut smallest = vec![];
    let mut failed_to_export = 0;
    let mut fails = vec![];
    let mut failed_sim: Vec<String> = vec![];

    // number of theorem that use quot
    let mut num_quot = 0;

    if let Some(definition_name) = args.get(2) {
        let mut inductives = HashMap::new();
        let mut axioms = HashMap::new();
        let exported = encoding
            .export_theorem(
                definition_name,
                &mut axioms,
                &mut inductives,
                &mut term_cache,
            )
            .unwrap();
        println!(
            "proving theorem {}... (estimated size {})",
            definition_name,
            exported.size(&mut size_cache)
        );
        exported.prove().unwrap();
        println!("Proven!");
        //println!("doing zk sim...");
        //println!("exported inds: {:?}", exported);
        //let sim_res = zk::Exporter::simulate(exported);
        //if sim_res.is_ok() {
        //    println!("proven in sim!");
        //} else {
        //    println!("failed in sim!, got {:?}", sim_res);
        //};
    } else {
        //for (i, name) in names.iter().enumerate() {
        //    let mut inductives = HashMap::new();
        //    let mut axioms = HashMap::new();
        //    //27269/97903
        //    //for (i, name) in names.iter().enumerate() {
        //    println!("[{}/{}] Exporting: {}", i, names.len(), name);
        //    match encoding.export_theorem(&name, &mut axioms, &mut inductives, &mut term_cache) {
        //        Ok(theorem) => {
        //            //println!("[{}/{}] Getting: {}", i, names.len(), name);
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

        //smallest.sort_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap());
        //println!("sorted: {:?}", &smallest[..]);

        let mut skipped_typing_eval_elim = 0;
        let mut skipped_simplify_eval_elim = 0;
        // prove theorems one by one...
        for (i, name) in names.iter().enumerate() {
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
                println!(
                    "[{}/{}] Proving: {}, size: {}",
                    i,
                    names.len(),
                    name,
                    0 //size
                );
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
                //println!("doing zk sim...");
                //let sim_res = zk::Exporter::simulate(theorem);
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

    //let mut axioms = BTreeMap::new();
    //let mut inductives = HashMap::new();
    //let exported = encoding
    //    .export_theorem("nat.le_succ_of_le", &mut axioms, &mut inductives, &mut None)
    //    //.export_theorem("nat.find_x", &mut axioms, &mut inductives, &mut None)
    //    .unwrap();

    //println!("inductives: {:?}", inductives);
    //println!("axioms: {:?}", inductives);

    //// TODO: And comm doesn't prove properly, some issue
    ////       Might be due to universe params and or non-prop motive on and.rec?
    ////let exported = encoding
    ////    .export_theorem("and.comm", &mut axioms, &mut inductives)
    ////    .unwrap();
    ////println!("got: {:?}", exported);
    ////println!("axioms: {:?}", axioms);
    ////println!("inductives: {:?}", inductives);
    //println!("proving...");
    //exported.prove().unwrap();
    //println!("Proven!");

    Ok(())
}
