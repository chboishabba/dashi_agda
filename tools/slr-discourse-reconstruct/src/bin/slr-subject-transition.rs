use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::PathBuf;

const SCHEMA: &str = "slr-subject-transition-v1";

#[derive(Clone, Debug)]
struct Config { parser: PathBuf, graph: PathBuf }
#[derive(Clone, Debug)]
struct Token { ordinal: usize, head: usize, text: String, dep: String }
#[derive(Clone, Debug)]
struct Sentence { id: usize, tokens: Vec<Token> }
#[derive(Clone, Debug)]
struct Boundary { sentence: usize, rank: usize, split: usize, anchor: String, projection: String, pareto: String }

fn usage() -> ! {
    eprintln!("usage: slr-subject-transition --parser parser.tsv --graph discourse-graph.tsv");
    std::process::exit(2)
}
fn args() -> Config {
    let a: Vec<String> = env::args().skip(1).collect();
    let (mut parser, mut graph) = (None, None); let mut i = 0;
    while i < a.len() { match a[i].as_str() {
        "--parser" => { i += 1; parser = a.get(i).map(PathBuf::from); }
        "--graph" => { i += 1; graph = a.get(i).map(PathBuf::from); }
        _ => usage(),
    } i += 1; }
    Config { parser: parser.unwrap_or_else(|| usage()), graph: graph.unwrap_or_else(|| usage()) }
}
fn parse_parser(text: &str) -> Result<HashMap<usize, Sentence>, String> {
    let mut out = HashMap::new(); let mut cur: Option<Sentence> = None;
    for (ln, line) in text.lines().enumerate() {
        let p: Vec<&str> = line.split('\t').collect();
        match p.first().copied().unwrap_or("") {
            "S" => { if let Some(s)=cur.take(){out.insert(s.id,s);} if p.len()<4{return Err(format!("bad S row {}",ln+1));} cur=Some(Sentence{id:p[1].parse().map_err(|_|"sentence")?,tokens:vec![]}); }
            "T" => { if p.len()<10{return Err(format!("bad T row {}",ln+1));} let s=cur.as_mut().ok_or("T before S")?; s.tokens.push(Token{ordinal:p[1].parse().map_err(|_|"ordinal")?,head:p[4].parse().map_err(|_|"head")?,text:p[5].to_string(),dep:p[9].to_string()}); }
            "E" => if let Some(s)=cur.take(){out.insert(s.id,s)},
            _ => {}
        }
    }
    if let Some(s)=cur{out.insert(s.id,s)} Ok(out)
}
fn parse_graph(text:&str)->Result<Vec<Boundary>,String>{
    let mut ls=text.lines(); let h=ls.next().ok_or("empty graph")?; let c:Vec<&str>=h.split('\t').collect();
    let ix=|n:&str| c.iter().position(|x|*x==n).ok_or_else(||format!("missing {n}"));
    let is=ix("sentence")?; let ir=ix("within_sentence_rank")?; let isp=ix("split")?; let ia=ix("anchor")?; let ip=ix("projection")?; let ifr=ix("pareto_fibres")?;
    let mut out=vec![]; for l in ls { let p:Vec<&str>=l.split('\t').collect(); if p.len()<c.len(){continue} out.push(Boundary{sentence:p[is].parse().map_err(|_|"sentence")?,rank:p[ir].parse().map_err(|_|"rank")?,split:p[isp].parse().map_err(|_|"split")?,anchor:p[ia].to_string(),projection:p[ip].to_string(),pareto:p[ifr].to_string()}); } Ok(out)
}
fn is_subject(dep:&str)->bool { matches!(dep,"nsubj"|"nsubjpass"|"csubj"|"csubjpass") }
fn local_subjects(tokens:&[Token], split:usize, left:bool)->Vec<String>{
    tokens.iter().filter(|t| is_subject(&t.dep) && ((t.ordinal < split)==left) && ((t.head < split)==left)).map(|t|t.text.clone()).collect()
}
fn crossing_subjects(tokens:&[Token], split:usize)->Vec<String>{
    tokens.iter().filter(|t| is_subject(&t.dep) && t.head!=t.ordinal && ((t.ordinal < split)!=(t.head < split))).map(|t|t.text.clone()).collect()
}
fn transition(tokens:&[Token], split:usize)->(&'static str,Vec<String>,Vec<String>,Vec<String>){
    let crossing=crossing_subjects(tokens,split); let left=local_subjects(tokens,split,true); let right=local_subjects(tokens,split,false);
    let kind=if !crossing.is_empty(){"predicate-continuation"}
      else if !left.is_empty() && !right.is_empty(){"subject-change-or-addition"}
      else if left.is_empty() && !right.is_empty(){"subject-introduction"}
      else if !left.is_empty() && right.is_empty(){"subject-preserved-left"}
      else {"no-local-subject-evidence"};
    (kind,left,right,crossing)
}
fn esc(s:&str)->String{s.replace('\t'," ").replace('\n'," ")}
fn main()->Result<(),Box<dyn std::error::Error>>{
    let cfg=args(); let ps=parse_parser(&fs::read_to_string(&cfg.parser)?).map_err(|e|format!("parser: {e}"))?; let bs=parse_graph(&fs::read_to_string(&cfg.graph)?).map_err(|e|format!("graph: {e}"))?;
    eprintln!("SLR_SUBJECT_TRANSITION_RECEIPT schema={} parser={} graph={} subject_change_is_speaker_change=false candidate_only=true",SCHEMA,cfg.parser.display(),cfg.graph.display());
    println!("schema\tboundary_id\tsentence\trank\tsplit\tanchor\tprojection\tpareto_fibres\tsubject_transition\tleft_local_subjects\tright_local_subjects\tcrossing_subjects\tsubject_change_is_speaker_change\tcandidate_only");
    for b in bs { let Some(s)=ps.get(&b.sentence) else {continue}; let (k,l,r,x)=transition(&s.tokens,b.split); println!("{}\tb{}-{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\tfalse\ttrue",SCHEMA,b.sentence,b.split,b.sentence,b.rank,b.split,esc(&b.anchor),b.projection,b.pareto,k,l.join(","),r.join(","),x.join(",")); }
    Ok(())
}
