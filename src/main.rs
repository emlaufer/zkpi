#![feature(mixed_integer_ops)]
#![feature(let_chains)]

use std::collections::{BTreeMap, HashMap};
use std::env;
use std::fs::File;
use std::io;
use std::io::prelude::*;

mod lean;
mod term;

// TODO: make non-io error...
fn main() -> io::Result<()> {
    env_logger::init();

    let args: Vec<String> = env::args().collect();
    if args.len() > 3 {
        println!("Usage: crabpi [lean.out] [name]");
        return Ok(());
    }

    let mut file = File::open(&args[1])?;
    let mut buf = Vec::new();
    file.read_to_end(&mut buf);
    let encoding = lean::LeanEncoding::parse(std::str::from_utf8(&buf).unwrap()).unwrap();

    println!("got: {:?}", encoding.theorem_names());
    let names = encoding.theorem_names();
    let mut inductives = HashMap::new();
    let mut axioms = BTreeMap::new();
    let mut size_cache = Some(hashconsing::hash_coll::HConMap::default());
    let mut term_cache = Some(HashMap::new());
    let mut smallest = vec![];
    let mut failed_to_export = 0;
    let mut fails = vec![];

    if let Some(definition_name) = args.get(2) {
        let exported = encoding
            .export_theorem(definition_name, &mut axioms, &mut inductives, &mut None)
            .unwrap();
        println!("proving theorem {}...", definition_name);
        exported.prove().unwrap();
        println!("Proven!");
    } else {
        for (i, name) in names.iter().enumerate() {
            //for (i, name) in names.iter().enumerate() {
            match encoding.export_theorem(&name, &mut axioms, &mut inductives, &mut term_cache) {
                Ok(theorem) => {
                    println!("[{}/{}] Getting: {}", i, names.len(), name);
                    let size = theorem.size(&mut size_cache);
                    println!("...size {}", size);
                    smallest.push((name, size));
                }
                Err(err) => {
                    if err == "Cannot export a theorem that accepts universe parameters!" {
                        println!("Def {} not a theorem, skipping...", name);
                        continue;
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
        for (i, (name, size)) in smallest[..].iter().enumerate() {
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
                    smallest.len(),
                    name,
                    size
                );
                if size > &1000000 {
                    println!("skipping big for now...");
                    continue;
                }
                //println!("theorem: {:?}", theorem);
                if let Err(e) = theorem.prove() {
                    panic!("HI");
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
                        continue;
                        //panic!("{}", e);
                    }
                }
                println!("proven!");
            }
        }

        println!(
            "failed to export {}/{} thms",
            failed_to_export,
            smallest.len() + failed_to_export
        );
        println!(
            "proved {}/{} thms",
            smallest.len() - skipped_typing_eval_elim - skipped_simplify_eval_elim,
            smallest.len()
        );
        println!(
            "skipped simplify elim (not an issue): {}/{} thms",
            skipped_simplify_eval_elim,
            smallest.len()
        );
        println!(
            "skipped typing eval elim (is an issue): {}/{} thms",
            skipped_typing_eval_elim,
            smallest.len()
        );
        println!("real fail: {}/{} thms", fails.len(), smallest.len());
        println!("fails: {:?}", fails);
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
