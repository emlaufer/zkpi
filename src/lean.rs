use log::debug;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{digit1, space0, space1},
    combinator::{map_res, recognize},
    multi::{many0, many_m_n, separated_list0},
    sequence::{terminated, tuple},
    IResult,
};
use nom_unicode::complete::alphanumeric1;

use std::cmp::{max, min};
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::term::{self, Inductive, InductiveRule, Term, Theorem};

fn parse_usize(input: &str) -> IResult<&str, usize> {
    map_res(digit1, str::parse)(input)
}

fn identifier(input: &str) -> IResult<&str, &str> {
    recognize(many0(alt((alphanumeric1, tag("_")))))(input)
}

use nom::{error::ParseError, Parser};
fn spaced<'a, E: ParseError<&'a str>, O, P: Parser<&'a str, O, E>>(
    parser: P,
) -> impl FnMut(&'a str) -> IResult<&'a str, O, E> {
    terminated(parser, space0)
}

#[derive(Debug)]
struct Name {
    prior: usize,
    string: String,
}

fn parse_name(input: &str) -> IResult<&str, Name> {
    let (rest, _) = spaced(alt((tag("#NS"), tag("#NI"))))(input)?;
    let (rest, prior) = spaced(parse_usize)(rest)?;
    let (rest, string) = identifier(rest)?;
    Ok((
        rest,
        Name {
            prior,
            string: string.to_string(),
        },
    ))
}

#[derive(Debug)]
enum Universe {
    US(usize),
    UM(usize, usize),
    UIM(usize, usize),
    UP(usize),
}

fn parse_universe(input: &str) -> IResult<&str, Universe> {
    alt((parse_us, parse_um, parse_uim, parse_up))(input)
}

fn parse_us(input: &str) -> IResult<&str, Universe> {
    let (rest, _) = spaced(tag("#US"))(input)?;
    let (rest, level) = parse_usize(rest)?;
    Ok((rest, Universe::US(level)))
}

fn parse_um(input: &str) -> IResult<&str, Universe> {
    let (rest, _) = spaced(tag("#UM"))(input)?;
    let (rest, i) = spaced(parse_usize)(rest)?;
    let (rest, j) = parse_usize(rest)?;
    Ok((rest, Universe::UM(i, j)))
}

fn parse_uim(input: &str) -> IResult<&str, Universe> {
    let (rest, _) = spaced(tag("#UIM"))(input)?;
    let (rest, i) = spaced(parse_usize)(rest)?;
    let (rest, j) = parse_usize(rest)?;
    Ok((rest, Universe::UIM(i, j)))
}

fn parse_up(input: &str) -> IResult<&str, Universe> {
    let (rest, _) = spaced(tag("#UP"))(input)?;
    let (rest, name) = parse_usize(rest)?;
    Ok((rest, Universe::UP(name)))
}

#[derive(Debug)]
enum BindNotation {
    BD,
    BI,
    BS,
    BC,
}

fn parse_bind_notation(input: &str) -> IResult<&str, BindNotation> {
    match alt((tag("#BD"), tag("#BI"), tag("#BS"), tag("#BC")))(input)? {
        (rest, "#BD") => Ok((rest, BindNotation::BD)),
        (rest, "#BI") => Ok((rest, BindNotation::BI)),
        (rest, "#BS") => Ok((rest, BindNotation::BS)),
        (rest, "#BC") => Ok((rest, BindNotation::BC)),
        _ => panic!("Impossible!"),
    }
}

#[derive(Debug)]
enum Expression {
    EV {
        index: usize,
    },
    ES {
        index: usize,
    },
    EC {
        name: usize,
        universes: Vec<usize>,
    },
    EA {
        e1: usize,
        e2: usize,
    },
    EL {
        bind_not: BindNotation,
        name: usize,
        domain: usize,
        body: usize,
    },
    EP {
        bind_not: BindNotation,
        name: usize,
        domain: usize,
        body: usize,
    },
    EZ {
        name: usize,
        val: usize,
        ty: usize,
        body: usize,
    },
}

fn parse_expression(input: &str) -> IResult<&str, Expression> {
    alt((
        parse_ev, parse_es, parse_ec, parse_ea, parse_el, parse_ep, parse_ez,
    ))(input)
}

fn parse_ev(input: &str) -> IResult<&str, Expression> {
    let (rest, _) = spaced(tag("#EV"))(input)?;
    let (rest, index) = parse_usize(rest)?;
    Ok((rest, Expression::EV { index }))
}

fn parse_es(input: &str) -> IResult<&str, Expression> {
    let (rest, _) = spaced(tag("#ES"))(input)?;
    let (rest, index) = parse_usize(rest)?;
    Ok((rest, Expression::ES { index }))
}

fn parse_ec(input: &str) -> IResult<&str, Expression> {
    let (rest, _) = spaced(tag("#EC"))(input)?;
    let (rest, name) = spaced(parse_usize)(rest)?;
    let (rest, universes) = many0(spaced(parse_usize))(rest)?;
    Ok((rest, Expression::EC { name, universes }))
}

fn parse_ea(input: &str) -> IResult<&str, Expression> {
    let (rest, _) = spaced(tag("#EA"))(input)?;
    let (rest, e1) = spaced(parse_usize)(rest)?;
    let (rest, e2) = parse_usize(rest)?;
    Ok((rest, Expression::EA { e1, e2 }))
}

fn parse_ez(input: &str) -> IResult<&str, Expression> {
    let (rest, _) = spaced(tag("#EZ"))(input)?;
    let (rest, name) = spaced(parse_usize)(rest)?;
    let (rest, val) = spaced(parse_usize)(rest)?;
    let (rest, ty) = spaced(parse_usize)(rest)?;
    let (rest, body) = parse_usize(rest)?;
    Ok((
        rest,
        Expression::EZ {
            name,
            val,
            ty,
            body,
        },
    ))
}

fn parse_el(input: &str) -> IResult<&str, Expression> {
    let (rest, _) = spaced(tag("#EL"))(input)?;
    let (rest, bind_not) = spaced(parse_bind_notation)(rest)?;
    let (rest, name) = spaced(parse_usize)(rest)?;
    let (rest, domain) = spaced(parse_usize)(rest)?;
    let (rest, body) = parse_usize(rest)?;
    Ok((
        rest,
        Expression::EL {
            bind_not,
            name,
            domain,
            body,
        },
    ))
}

fn parse_ep(input: &str) -> IResult<&str, Expression> {
    let (rest, _) = spaced(tag("#EP"))(input)?;
    let (rest, bind_not) = spaced(parse_bind_notation)(rest)?;
    let (rest, name) = spaced(parse_usize)(rest)?;
    let (rest, domain) = spaced(parse_usize)(rest)?;
    let (rest, body) = parse_usize(rest)?;
    Ok((
        rest,
        Expression::EP {
            bind_not,
            name,
            domain,
            body,
        },
    ))
}

#[derive(Debug)]
enum Definition {
    Def {
        name: usize,
        ty: usize,
        val: usize,
        universe_params: Vec<usize>,
    },
    Axiom {
        name: usize,
        ty: usize,
        universe_params: Vec<usize>,
    },
    Inductive {
        name: usize,
        num_params: usize, // number of (global) params to this inductive type
        ty: usize,
        intros: Vec<(usize, usize)>,
        universe_params: Vec<usize>,
    },
}

impl Definition {
    fn name(&self) -> usize {
        match self {
            Definition::Def { name, .. }
            | Definition::Axiom { name, .. }
            | Definition::Inductive { name, .. } => *name,
        }
    }

    fn universe_params(&self) -> &[usize] {
        match self {
            Definition::Def {
                universe_params, ..
            }
            | Definition::Axiom {
                universe_params, ..
            }
            | Definition::Inductive {
                universe_params, ..
            } => &universe_params,
        }
    }
}

fn parse_definition(input: &str) -> IResult<&str, Definition> {
    alt((parse_def, parse_axiom, parse_inductive))(input)
}

fn parse_def(input: &str) -> IResult<&str, Definition> {
    let (rest, _) = spaced(tag("#DEF"))(input)?;
    let (rest, name) = spaced(parse_usize)(rest)?;
    let (rest, ty) = spaced(parse_usize)(rest)?;
    let (rest, val) = spaced(parse_usize)(rest)?;
    let (rest, universe_params) = separated_list0(space1, parse_usize)(rest)?;
    Ok((
        rest,
        Definition::Def {
            name,
            ty,
            val,
            universe_params,
        },
    ))
}

fn parse_axiom(input: &str) -> IResult<&str, Definition> {
    let (rest, _) = spaced(tag("#AX"))(input)?;
    let (rest, name) = spaced(parse_usize)(rest)?;
    let (rest, ty) = spaced(parse_usize)(rest)?;
    let (rest, universe_params) = separated_list0(space1, parse_usize)(rest)?;
    Ok((
        rest,
        Definition::Axiom {
            name,
            ty,
            universe_params,
        },
    ))
}

/// #IND <num> <nidx> <eidx> <num_intros> <intro>* <nidx*>
fn parse_inductive(input: &str) -> IResult<&str, Definition> {
    let (rest, _) = spaced(tag("#IND"))(input)?;
    let (rest, num_params) = spaced(parse_usize)(rest)?;
    let (rest, name) = spaced(parse_usize)(rest)?;
    let (rest, ty) = spaced(parse_usize)(rest)?;
    let (rest, num_intros) = spaced(parse_usize)(rest)?;
    let (rest, intros) = many_m_n(
        num_intros,
        num_intros,
        tuple((spaced(parse_usize), spaced(parse_usize))),
    )(rest)?;
    let (rest, universe_params) = separated_list0(space1, parse_usize)(rest)?;
    Ok((
        rest,
        Definition::Inductive {
            name,
            num_params,
            ty,
            intros,
            universe_params,
        },
    ))
}

#[derive(Debug)]
enum Instruction {
    IName(Name),
    IUniverse(Universe),
    IExpression(Expression),
    IDefinition(Definition),
}

fn parse_name_instr(input: &str) -> IResult<&str, Instruction> {
    let (rest, index) = spaced(parse_usize)(input)?;
    let (rest, name) = parse_name(rest)?;
    Ok((rest, Instruction::IName(name)))
}
fn parse_universe_instr(input: &str) -> IResult<&str, Instruction> {
    let (rest, index) = spaced(parse_usize)(input)?;
    let (rest, universe) = parse_universe(rest)?;
    Ok((rest, Instruction::IUniverse(universe)))
}
fn parse_expression_instr(input: &str) -> IResult<&str, Instruction> {
    let (rest, index) = spaced(parse_usize)(input)?;
    let (rest, expression) = parse_expression(rest)?;
    Ok((rest, Instruction::IExpression(expression)))
}
fn parse_definition_instr(input: &str) -> IResult<&str, Instruction> {
    let (rest, definition) = parse_definition(input)?;
    Ok((rest, Instruction::IDefinition(definition)))
}

impl Instruction {
    fn parse(input: &str) -> IResult<&str, Instruction> {
        alt((
            parse_name_instr,
            parse_universe_instr,
            parse_expression_instr,
            parse_definition_instr,
        ))(input)
    }
}

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
fn btreemap_hash(map: &BTreeMap<usize, usize>) -> u64 {
    let mut s = DefaultHasher::new();
    map.hash(&mut s);
    s.finish()
}

pub struct LeanEncoding {
    names: Vec<Name>,
    expressions: Vec<Expression>,
    universes: Vec<Universe>,
    definitions: Vec<Definition>,

    /// Map from a name index to a definition index
    name_to_def: BTreeMap<usize, usize>,

    name_to_name_idx: BTreeMap<String, usize>,

    /// Map from a rules name index to its inductive definition index and
    /// inner rule index
    name_to_ind_and_rule: BTreeMap<usize, (usize, usize)>,
}

impl LeanEncoding {
    fn new() -> Self {
        LeanEncoding {
            names: Vec::new(),
            expressions: Vec::new(),
            universes: Vec::new(),
            definitions: Vec::new(),
            name_to_def: BTreeMap::new(),
            name_to_name_idx: BTreeMap::new(),
            name_to_ind_and_rule: BTreeMap::new(),
        }
    }

    pub fn parse(input: &str) -> Result<LeanEncoding, String> {
        let mut res = LeanEncoding::new();
        for line in input.lines() {
            if let Ok((_, instr)) = Instruction::parse(line) {
                match instr {
                    Instruction::IName(name) => res.names.push(name),
                    Instruction::IUniverse(universe) => res.universes.push(universe),
                    Instruction::IExpression(expression) => res.expressions.push(expression),
                    Instruction::IDefinition(definition) => {
                        res.name_to_def
                            .insert(definition.name(), res.definitions.len());

                        // insert each inductive rule into the rule mapping cache
                        if let Definition::Inductive {
                            name,
                            ty: _,
                            ref intros,
                            ..
                        } = definition
                        {
                            for (i, (name, _)) in intros.iter().enumerate() {
                                res.name_to_ind_and_rule
                                    .insert(*name, (res.definitions.len(), i));
                            }
                        }

                        res.definitions.push(definition);
                    }
                }
                //println!("instr: {:?}", instr);
            } else {
                println!("bad parse, skipping: {:?}", line);
            }
        }

        for i in 0..res.names.len() + 1 {
            let name_string = res.resolve_name(i);
            res.name_to_name_idx.insert(name_string, i);
        }

        Ok(res)
    }

    fn resolve_name(&self, index: usize) -> String {
        if index == 0 {
            return "".to_string();
        }

        let name = &self.names[index - 1];
        if name.prior == 0 {
            return name.string.clone();
        } else {
            let prior_str = self.resolve_name(name.prior);
            return prior_str + "." + &name.string;
        }
    }

    fn lookup_definition(&self, name: &str) -> Result<&Definition, String> {
        let name = self
            .name_to_name_idx
            .get(name)
            .ok_or(format!("Failed to lookup name {}!", name))?;
        self.lookup_definition_usize(*name)
    }

    fn lookup_definition_usize(&self, name: usize) -> Result<&Definition, String> {
        let def_idx = self.name_to_def.get(&name).cloned().ok_or(format!(
            "Failed to find definition indexed {} (name: {})!",
            name,
            self.resolve_name(name)
        ))?;
        //println!("defs: {:?}", self.definitions.len());
        Ok(&self.definitions[def_idx])
    }

    /// Just def for now
    pub fn export_theorem(
        &self,
        name: &str,
        axioms: &mut BTreeMap<String, Term>,
        inductives: &mut HashMap<String, Inductive>,
        cache: &mut Option<HashMap<(usize, u64), Term>>,
    ) -> Result<Theorem, String> {
        debug!("Exporting theorem: {}", name);
        let def = self.lookup_definition(name)?;
        match def {
            Definition::Def {
                name,
                val,
                ty,
                universe_params: universes,
            } => {
                if universes.len() != 0 {
                    return Err(format!(
                        "Cannot export a theorem that accepts universe parameters!"
                    ));
                }
                // TODO: only include inds and axs used
                let val_term =
                    self.export_expr(*val, axioms, inductives, &BTreeMap::new(), cache)?;
                let ty_term = self.export_expr(*ty, axioms, inductives, &BTreeMap::new(), cache)?;
                Ok(Theorem::new(val_term, ty_term, axioms, inductives))
            }
            _ => Err(format!("Definition named {} is not a theorem!", name)),
        }
    }

    pub fn theorem_names(&self) -> Vec<String> {
        let mut res = Vec::new();
        for (name, def) in &self.name_to_def {
            if let Definition::Def { .. } = self.definitions[*def] {
                let name_string = self.resolve_name(*name);
                res.push(name_string);
            }
        }
        res
    }

    /// TODO: Should resolve universe params first, then we dont need the
    ///       hashmap garbage. But would require another IR or something...
    ///       annoying...
    fn export_expr(
        &self,
        index: usize,
        axioms: &mut BTreeMap<String, Term>,
        inductives: &mut HashMap<String, Inductive>,
        universes: &BTreeMap<usize, usize>,
        cache: &mut Option<HashMap<(usize, u64), Term>>,
    ) -> Result<Term, String> {
        // TODO: fix caching...
        debug!("Export expr: {}", index);
        if let Some(term) = cache
            .as_ref()
            .map(|c| c.get(&(index, btreemap_hash(universes))))
            .flatten()
        {
            debug!("{} cached!", index);
            return Ok(term.clone());
        }

        let expr = &self.expressions[index];
        let res = match expr {
            Expression::EV { index } => term::bound(*index),
            Expression::ES { index } => {
                let universe = self.export_universe(*index, universes)?;
                term::sort(universe)
            }
            Expression::EC {
                name,
                universes: universe_instantiation,
            } => self.export_constant(
                *name,
                universe_instantiation,
                axioms,
                inductives,
                universes,
                cache,
            )?,
            Expression::EA { e1, e2 } => {
                let e1_term = self.export_expr(*e1, axioms, inductives, universes, cache)?;
                let e2_term = self.export_expr(*e2, axioms, inductives, universes, cache)?;
                term::app(e1_term, e2_term)
            }
            Expression::EL {
                bind_not,
                name,
                domain,
                body,
            } => {
                let domain_term =
                    self.export_expr(*domain, axioms, inductives, universes, cache)?;
                let body_term = self.export_expr(*body, axioms, inductives, universes, cache)?;
                term::lam(domain_term, body_term)
            }
            Expression::EP {
                bind_not,
                name,
                domain,
                body,
            } => {
                let domain_term =
                    self.export_expr(*domain, axioms, inductives, universes, cache)?;
                let body_term = self.export_expr(*body, axioms, inductives, universes, cache)?;
                term::pi(domain_term, body_term)
            }
            Expression::EZ {
                name,
                val,
                ty,
                body,
            } => {
                return Err("Let expression unsupported!".to_string());
            }
        };
        cache
            .as_mut()
            .map(|c| c.insert((index, btreemap_hash(universes)), res.clone()));
        Ok(res)
    }

    fn export_universe(
        &self,
        index: usize,
        universes: &BTreeMap<usize, usize>,
    ) -> Result<usize, String> {
        debug!("Exporting universe {}", index);
        if index == 0 {
            return Ok(0);
        }

        let univ = &self.universes[index - 1];
        let level = match univ {
            Universe::US(prior) => 1 + self.export_universe(*prior, universes)?,
            Universe::UM(i, j) => max(
                self.export_universe(*i, universes)?,
                self.export_universe(*j, universes)?,
            ),
            Universe::UIM(i, j) => term::imax(
                self.export_universe(*i, universes)?,
                self.export_universe(*j, universes)?,
            ),
            Universe::UP(name) => *universes.get(&name).ok_or(format!(
                "Unmapped universe param {} (idx: {}) (have: {:?})",
                self.resolve_name(*name),
                *name,
                universes
            ))?,
        };
        Ok(level)
    }

    /// Instantiates universe params within the given universe context
    fn instantiate_universes(
        &self,
        def: &Definition,
        universes: &BTreeMap<usize, usize>,
        universe_instantiation: &[usize],
    ) -> Result<BTreeMap<usize, usize>, String> {
        let mut res = universes.clone();
        let universe_params = def.universe_params();
        //println!(
        //    "instantiating {:?} in {:?} for def {}",
        //    universe_instantiation,
        //    universes,
        //    self.resolve_name(def.name())
        //);
        //let universe_mapping = universe_params.iter().zip(
        //    universe_instantiation
        //        .iter()
        //        .map(|u| self.export_universe(*u, universes))
        //        .collect::<Result<Vec<usize>, _>>()?,
        //);
        //println!("old map: {:?}", universes);
        for i in 0..min(universe_params.len(), universe_instantiation.len()) {
            let resolved_universe = self.export_universe(universe_instantiation[i], &res)?;
            //println!("mapping {} to {}", universe_params[i], resolved_universe);
            //res.entry(universe_params[i]).or_insert(resolved_universe);
            res.insert(universe_params[i], resolved_universe);
        }
        //println!("new map: {:?}", res);
        Ok(res)
    }

    fn export_constant(
        &self,
        name: usize,
        universe_instantiation: &[usize],
        axioms: &mut BTreeMap<String, Term>,
        inductives: &mut HashMap<String, Inductive>,
        universes: &BTreeMap<usize, usize>,
        cache: &mut Option<HashMap<(usize, u64), Term>>,
    ) -> Result<Term, String> {
        debug!("Exported const: {}", name);
        // TODO: const cache

        // cleanup time...
        // 1. universe_instantiation should immediately go into universe_param map...
        // 2.

        // TODO: clean this up
        // TODO: resolve name ambiguity...e.g.
        //       universes vs universe_params vs universe_instantiation vs ...
        //
        // TODO: rename
        let name_string = self.resolve_name(name);

        if let Some((ind, rule)) = self.name_to_ind_and_rule.get(&name) {
            let def = &self.definitions[*ind];
            if let Definition::Inductive { name, .. } = def {
                // add the inductive type to inductives...
                self.export_constant(
                    *name,
                    universe_instantiation,
                    axioms,
                    inductives,
                    universes,
                    cache,
                )
                .unwrap();
            }

            let universe_params = self.definitions[*ind].universe_params();
            //println!("1");
            let universes = self.instantiate_universes(def, universes, universe_instantiation)?;
            let universe_inst_string = universe_params
                .iter()
                .map(|p| universes.get(p).unwrap().to_string())
                .collect::<Vec<_>>()
                .join(",");
            let name_string = name_string + ".{" + &universe_inst_string + "}";

            // TODO: fix...
            return Ok(term::axiom(name_string));
        }

        // if const is an induction eliminator...
        if name_string.ends_with(".rec") {
            //println!(
            //    "exporting rec: {} {:?}",
            //    name_string, universe_instantiation
            //);
            // TODO: handle different recursion motives
            // TODO: if this is a prop type, we need to handle this different
            // convert universes u0,u1,...,un to a string {u0,u1,...,un}
            //println!("Exporting rec: {}", name_string);
            // TODO: can push off lookup...
            let inductive_name = name_string.trim_end_matches(".rec");
            let inductive_name = inductive_name.trim_end_matches(|c| {
                c == '{' || c == '}' || c == ',' || c == '.' || char::is_numeric(c)
            });
            let def = self.lookup_definition(inductive_name)?;
            // if we are passing a universe param to rec, skip the first uparam for the def
            let def_universe_instantiation =
                if def.universe_params().len() + 1 == universe_instantiation.len() {
                    &universe_instantiation[1..]
                } else {
                    &universe_instantiation
                };
            let universes =
                self.instantiate_universes(def, universes, def_universe_instantiation)?;

            let universe_instantiation = universe_instantiation
                .iter()
                .map(|u| self.export_universe(*u, &universes).unwrap())
                .collect::<Vec<_>>();
            let motive_universe_level =
                if def.universe_params().len() + 1 == universe_instantiation.len() {
                    universe_instantiation[0]
                } else {
                    0
                };
            let universe_instantiation =
                if def.universe_params().len() + 1 == universe_instantiation.len() {
                    &universe_instantiation[1..]
                } else {
                    &universe_instantiation
                };

            //println!(
            //    "instantiating universes for rec {}: {:?}",
            //    name_string, universes
            //);
            let universe_inst_string = def
                .universe_params()
                .iter()
                .map(|p| {
                    universes
                        .get(p)
                        .ok_or(format!("failed to get universe for {}", name_string))
                        .map(|p| p.to_string())
                })
                .collect::<Result<Vec<_>, _>>()?
                .join(",");

            let rec_name = format!(
                "{}.{{{}}}.rec.{{{}}}",
                inductive_name.to_owned(),
                &universe_inst_string,
                motive_universe_level,
            );

            //println!(
            //    "exporting def with rec: {:?}, {:?}",
            //    name_string, inductive_name
            //);
            if axioms.contains_key(&rec_name) {
                //println!("rec cached!");
                return Ok(term::axiom(rec_name));
            }
            //println!("got name {}", inductive_name);
            //println!("2");
            //let universes =
            //    self.instantiate_universes(def, &BTreeMap::new(), universe_instantiation)?;
            let universes = self.instantiate_universes(def, &universes, universe_instantiation)?;
            self.export_definition(
                def,
                universe_instantiation,
                axioms,
                inductives,
                &universes,
                cache,
            )
            .unwrap();
            // Fully qualified name of the inductive type
            let instantiated_ind_name = format!("{}.{{{}}}", inductive_name, universe_inst_string);
            let ind = inductives.get_mut(&instantiated_ind_name).expect(&format!(
                "Failed to look up inductive {}!",
                instantiated_ind_name
            ));
            //println!("axioms: {:?}", axioms);
            //println!("inds: {:?}", inductives);
            //println!("adding recursion principle: {}", rec_name);
            axioms.insert(rec_name.clone(), ind.elim(motive_universe_level));
            //println!("Exporting rec: {}", name_string);
            return Ok(term::axiom(rec_name));
        }

        let def = self.lookup_definition_usize(name)?;
        let universes = self.instantiate_universes(def, universes, universe_instantiation)?;
        self.export_definition(
            def,
            universe_instantiation,
            axioms,
            inductives,
            &universes,
            cache,
        )
    }

    fn export_definition(
        &self,
        def: &Definition,
        universe_instantiation: &[usize], // TODO: remove if possible, only used for resolving ind
        // name
        axioms: &mut BTreeMap<String, Term>,
        inductives: &mut HashMap<String, Inductive>,
        universes: &BTreeMap<usize, usize>,
        cache: &mut Option<HashMap<(usize, u64), Term>>,
    ) -> Result<Term, String> {
        debug!("Exported def: {}", self.resolve_name(def.name()));
        match def {
            Definition::Def {
                name,
                ty,
                val,
                universe_params,
            } => {
                // TODO: ensure it type checks
                //let ty_term = self.export_expr(ty, axioms, inductives, combined_univs)?;
                self.export_expr(*val, axioms, inductives, &universes, cache)
            }
            Definition::Axiom {
                name,
                ty,
                universe_params,
            } => {
                // TODO: ensure it type checks
                //let ty_term = self.export_expr(ty, axioms, inductives, combined_univs)?;
                let name_string = self.resolve_name(*name);
                let ty_term = self.export_expr(*ty, axioms, inductives, &universes, cache)?;
                axioms.insert(name_string.clone(), ty_term);
                Ok(term::axiom(name_string))
            }
            Definition::Inductive {
                name,
                num_params,
                ty,
                intros,
                universe_params,
            } => {
                // TODO: fix this...

                //println!(
                //    "universe_params: {:?}, universes: {:?}",
                //    universe_params, universes
                //);
                // if we have already seen this inductive, skip
                let universe_inst_string = universe_params
                    .iter()
                    .map(|p| {
                        universes
                            .get(p)
                            .ok_or(format!(
                                "failed to get universe for {}",
                                self.resolve_name(*name)
                            ))
                            .map(|p| p.to_string())
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .join(",");
                let name_string = self.resolve_name(*name) + ".{" + &universe_inst_string + "}";
                //println!(
                //    "name_string: {:?}, univ_params: {:?}, universes: {:?}",
                //    name_string, universe_params, universes
                //);
                if inductives.contains_key(&name_string) {
                    return Ok(term::axiom(name_string));
                }

                //println!("getting ty for {} (universes {:?})", name_string, universes);
                let ty_term = self.export_expr(*ty, axioms, inductives, &universes, cache)?;
                //println!("got ty {:?} for {}", ty_term, name_string);

                // TODO: maybe not best design... Insert a placeholder to prevent
                //       infinite recursion when resolving the types of the induction
                //       rules
                let ind = Inductive::new(&name_string, *num_params, ty_term.clone(), &[]);
                inductives.insert(name_string.clone(), ind);

                let mut rules = Vec::new();
                for (name, ty) in intros {
                    let rule_name = self.resolve_name(*name) + ".{" + &universe_inst_string + "}";
                    //println!(
                    //    "exporting rule {} for {} with univs: {:?}",
                    //    rule_name, name_string, universes
                    //);
                    let rule_ty = self.export_expr(*ty, axioms, inductives, &universes, cache)?;
                    rules.push(InductiveRule::new(&rule_name, rule_ty));
                }

                let ind = Inductive::new(&name_string, *num_params, ty_term, &rules);
                inductives.insert(name_string.clone(), ind);
                Ok(term::axiom(name_string))
            }
        }
    }
}
