use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::PathBuf;

const SCHEMA: &str = "slr-role-transition-v1";

#[derive(Clone, Debug)]
struct Config { parser: PathBuf, graph: PathBuf }
#[derive(Clone, Debug)]
struct Token { ordinal: usize, head: usize, text: String, lemma: String, dep: String }
#[derive(Clone, Debug)]
struct Sentence { id: usize, tokens: Vec<Token> }
#[derive(Clone, Debug)]
struct Boundary { sentence: usize, rank: usize, split: usize, anchor: String, projection: String, pareto: String }

fn usage() -> ! {
    eprintln!("usage: slr-role-transition --parser parser.tsv --graph discourse-graph.tsv");
    std::process::exit(2)
}
fn args() -> Config {
    let a: Vec<String> = env::args().skip(1).collect();
    let (mut parser, mut graph) = (None, None);
    let mut i = 0;
    while i < a.len() {
        match a[i].as_str() {
            "--parser" => { i += 1; parser = a.get(i).map(PathBuf::from); }
            "--graph" => { i += 1; graph = a.get(i).map(PathBuf::from); }
            _ => usage(),
        }
        i += 1;
    }
    Config { parser: parser.unwrap_or_else(|| usage()), graph: graph.unwrap_or_else(|| usage()) }
}

fn parse_parser(text: &str) -> Result<HashMap<usize, Sentence>, String> {
    let mut out = HashMap::new();
    let mut cur: Option<Sentence> = None;
    for (ln, l) in text.lines().enumerate() {
        let p: Vec<&str> = l.split('\t').collect();
        match p.first().copied().unwrap_or("") {
            "S" => {
                if let Some(s) = cur.take() { out.insert(s.id, s); }
                if p.len() < 4 { return Err(format!("bad S {}", ln + 1)); }
                cur = Some(Sentence { id: p[1].parse().map_err(|_| "sentence")?, tokens: vec![] });
            }
            "T" => {
                if p.len() < 10 { return Err(format!("bad T {}", ln + 1)); }
                let s = cur.as_mut().ok_or("T before S")?;
                s.tokens.push(Token {
                    ordinal: p[1].parse().map_err(|_| "ordinal")?,
                    head: p[4].parse().map_err(|_| "head")?,
                    text: p[5].to_string(),
                    lemma: p[6].to_lowercase(),
                    dep: p[9].to_string(),
                });
            }
            "E" => {
                if let Some(s) = cur.take() { out.insert(s.id, s); }
            }
            _ => {}
        }
    }
    if let Some(s) = cur { out.insert(s.id, s); }
    Ok(out)
}

fn parse_graph(text: &str) -> Result<Vec<Boundary>, String> {
    let mut ls = text.lines();
    let h = ls.next().ok_or("empty graph")?;
    let c: Vec<&str> = h.split('\t').collect();
    let ix = |n: &str| c.iter().position(|x| *x == n).ok_or_else(|| format!("missing {n}"));
    let is = ix("sentence")?; let ir = ix("within_sentence_rank")?; let isp = ix("split")?;
    let ia = ix("anchor")?; let ip = ix("projection")?; let ifr = ix("pareto_fibres")?;
    let mut out = vec![];
    for l in ls {
        let p: Vec<&str> = l.split('\t').collect();
        if p.len() < c.len() { continue; }
        out.push(Boundary {
            sentence: p[is].parse().map_err(|_| "sentence")?,
            rank: p[ir].parse().map_err(|_| "rank")?,
            split: p[isp].parse().map_err(|_| "split")?,
            anchor: p[ia].to_string(), projection: p[ip].to_string(), pareto: p[ifr].to_string(),
        });
    }
    Ok(out)
}

fn crosses(t: &Token, split: usize) -> bool { t.head != t.ordinal && ((t.ordinal < split) != (t.head < split)) }
fn role(dep: &str) -> &'static str {
    match dep {
        "nsubj" | "nsubjpass" | "csubj" | "csubjpass" => "actor",
        "obj" | "dobj" | "iobj" | "pobj" => "patient",
        "ccomp" | "xcomp" | "advcl" | "acl" | "relcl" => "clause",
        "cc" | "conj" => "coordination",
        "aux" | "auxpass" => "predicate-aux",
        "ROOT" => "predicate-root",
        _ => "other",
    }
}
fn side_has(tokens: &[Token], split: usize, left: bool, deps: &[&str]) -> bool {
    tokens.iter().any(|t| ((t.ordinal < split) == left) && deps.contains(&t.dep.as_str()))
}
fn esc(s: &str) -> String { s.replace('\t', " ").replace('\n', " ") }

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let c = args();
    let ps = parse_parser(&fs::read_to_string(&c.parser)?).map_err(|e| format!("parser: {e}"))?;
    let bs = parse_graph(&fs::read_to_string(&c.graph)?).map_err(|e| format!("graph: {e}"))?;
    eprintln!("SLR_ROLE_TRANSITION_RECEIPT schema={} parser={} graph={} role_change_is_speaker_change=false candidate_only=true", SCHEMA, c.parser.display(), c.graph.display());
    println!("schema\tboundary_id\tsentence\trank\tsplit\tanchor\tprojection\tpareto_fibres\tcrossing_roles\tactor_crossing\tpatient_crossing\tclause_crossing\tcoordination_crossing\tpredicate_aux_crossing\tleft_has_subject\tright_has_subject\tleft_has_modal\tright_has_modal\tleft_has_negation\tright_has_negation\trole_change_is_speaker_change\tcandidate_only");
    for b in bs {
        let Some(s) = ps.get(&b.sentence) else { continue };
        let cross = s.tokens.iter().filter(|t| crosses(t, b.split)).collect::<Vec<_>>();
        let mut roles = cross.iter().map(|t| role(&t.dep)).collect::<Vec<_>>();
        roles.sort(); roles.dedup();
        let ac = cross.iter().any(|t| role(&t.dep) == "actor");
        let pc = cross.iter().any(|t| role(&t.dep) == "patient");
        let cc = cross.iter().any(|t| role(&t.dep) == "clause");
        let co = cross.iter().any(|t| role(&t.dep) == "coordination");
        let pa = cross.iter().any(|t| role(&t.dep) == "predicate-aux");
        let lhs = side_has(&s.tokens, b.split, true, &["nsubj", "nsubjpass", "csubj", "csubjpass"]);
        let rhs = side_has(&s.tokens, b.split, false, &["nsubj", "nsubjpass", "csubj", "csubjpass"]);
        let lm = s.tokens.iter().any(|t| t.ordinal < b.split && matches!(t.lemma.as_str(), "can"|"could"|"may"|"might"|"must"|"shall"|"should"|"will"|"would"));
        let rm = s.tokens.iter().any(|t| t.ordinal >= b.split && matches!(t.lemma.as_str(), "can"|"could"|"may"|"might"|"must"|"shall"|"should"|"will"|"would"));
        let ln = s.tokens.iter().any(|t| t.ordinal < b.split && (t.dep == "neg" || t.lemma == "not" || t.lemma == "n't"));
        let rn = s.tokens.iter().any(|t| t.ordinal >= b.split && (t.dep == "neg" || t.lemma == "not" || t.lemma == "n't"));
        println!("{}\tb{}-{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\tfalse\ttrue",
            SCHEMA, b.sentence, b.split, b.sentence, b.rank, b.split, esc(&b.anchor), b.projection, b.pareto,
            roles.join(","), ac, pc, cc, co, pa, lhs, rhs, lm, rm, ln, rn);
    }
    Ok(())
}
