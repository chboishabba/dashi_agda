use std::collections::{BTreeMap, HashMap};
use std::env;
use std::fs;
use std::path::PathBuf;

const SCHEMA: &str = "slr-discourse-manifold-v1";

#[derive(Clone, Debug)]
struct Config { cuts: PathBuf, parser: PathBuf, source: PathBuf, pnf: Option<PathBuf>, max_rank: usize, top: usize }
#[derive(Clone, Debug)]
struct Token { lemma: String, text: String, start: usize, end: usize }
#[derive(Clone, Debug)]
struct Sentence { id: usize, start: usize, end: usize, tokens: Vec<Token> }
#[derive(Clone, Debug)]
struct Cut {
    sentence: usize, rank: usize, split: usize, anchor: String, cut_score: i32,
    dep_content: usize, punctuation: i32, discourse_marker: bool, perspective_shift: bool,
    sentiment_delta: f64, left_profile: String, right_profile: String,
    left_profile_score: i32, right_profile_score: i32, profile_shift: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Fibre { Speaker, Quote, Nesting, Asr, Rhetorical }
#[derive(Clone, Debug)]
struct Point { fibre: Fibre, syntax: i32, pnf: i32, attribution: i32, speaker: i32, world: i32, asr: i32, rhetorical: i32 }

fn usage() -> ! {
    eprintln!("usage: slr-discourse-manifold --cuts discourse-cuts.tsv --parser parser.tsv --source source.txt [--pnf pnf.stdout] [--max-rank 3] [--top 1000]");
    std::process::exit(2)
}
fn args() -> Config {
    let a: Vec<String> = env::args().skip(1).collect();
    let (mut cuts, mut parser, mut source, mut pnf) = (None, None, None, None);
    let (mut max_rank, mut top) = (3usize, 1000usize);
    let mut i=0; while i<a.len() { match a[i].as_str() {
        "--cuts" => {i+=1; cuts=a.get(i).map(PathBuf::from)},
        "--parser" => {i+=1; parser=a.get(i).map(PathBuf::from)},
        "--source" => {i+=1; source=a.get(i).map(PathBuf::from)},
        "--pnf" => {i+=1; pnf=a.get(i).map(PathBuf::from)},
        "--max-rank" => {i+=1; max_rank=a.get(i).and_then(|x|x.parse().ok()).unwrap_or(3)},
        "--top" => {i+=1; top=a.get(i).and_then(|x|x.parse().ok()).unwrap_or(1000)},
        _ => usage(), } i+=1; }
    Config{cuts:cuts.unwrap_or_else(||usage()),parser:parser.unwrap_or_else(||usage()),source:source.unwrap_or_else(||usage()),pnf,max_rank,top}
}
fn boolv(s:&str)->bool { matches!(s,"true"|"True"|"1") }
fn parser(text:&str)->Result<HashMap<usize,Sentence>,String>{
    let mut out=HashMap::new(); let mut cur:Option<Sentence>=None;
    for (ln,line) in text.lines().enumerate(){ let p:Vec<&str>=line.split('\t').collect(); match p.first().copied().unwrap_or(""){
        "S"=>{ if let Some(s)=cur.take(){out.insert(s.id,s);} if p.len()<4{return Err(format!("bad S {}",ln+1))}; cur=Some(Sentence{id:p[1].parse().map_err(|_|"bad id")?,start:p[2].parse().map_err(|_|"bad start")?,end:p[3].parse().map_err(|_|"bad end")?,tokens:vec![]});},
        "T"=>{ if p.len()<10{return Err(format!("bad T {}",ln+1))}; let s=cur.as_mut().ok_or("T before S")?; s.tokens.push(Token{start:p[2].parse().map_err(|_|"bad token start")?,end:p[3].parse().map_err(|_|"bad token end")?,text:p[5].to_string(),lemma:p[6].to_lowercase()});},
        "E"=>{if let Some(s)=cur.take(){out.insert(s.id,s);}}, _=>{} }} if let Some(s)=cur{out.insert(s.id,s)} Ok(out)
}
fn cuts(text:&str)->Result<Vec<Cut>,String>{
    let mut ls=text.lines(); let h=ls.next().ok_or("empty cuts")?; let c:Vec<&str>=h.split('\t').collect();
    let ix=|n:&str| c.iter().position(|x|*x==n).ok_or_else(||format!("missing {n}"));
    let is=ix("sentence")?;let ir=ix("within_sentence_rank")?;let isp=ix("split")?;let ia=ix("anchor")?;let ic=ix("cut_score")?;let id=ix("dep_crossings_content")?;let ip=ix("punctuation")?;let im=ix("discourse_marker")?;let ips=ix("perspective_shift")?;let isd=ix("sentiment_delta")?;let ilp=ix("left_profile")?;let ilps=ix("left_profile_score")?;let irp=ix("right_profile")?;let irps=ix("right_profile_score")?;let ipf=ix("profile_shift")?;
    let mut out=vec![]; for line in ls {let p:Vec<&str>=line.split('\t').collect(); if p.len()<c.len(){continue} out.push(Cut{sentence:p[is].parse().map_err(|_|"sentence")?,rank:p[ir].parse().map_err(|_|"rank")?,split:p[isp].parse().map_err(|_|"split")?,anchor:p[ia].to_string(),cut_score:p[ic].parse().map_err(|_|"cut")?,dep_content:p[id].parse().map_err(|_|"dep")?,punctuation:p[ip].parse().map_err(|_|"punc")?,discourse_marker:boolv(p[im]),perspective_shift:boolv(p[ips]),sentiment_delta:p[isd].parse().map_err(|_|"sent")?,left_profile:p[ilp].to_string(),left_profile_score:p[ilps].parse().map_err(|_|"lps")?,right_profile:p[irp].to_string(),right_profile_score:p[irps].parse().map_err(|_|"rps")?,profile_shift:boolv(p[ipf])});} Ok(out)
}
fn residuals(text:&str)->BTreeMap<usize,usize>{ let mut m=BTreeMap::new(); for l in text.lines(){let p:Vec<&str>=l.split('\t').collect(); if p.first()==Some(&"R")&&p.len()>=3{if let(Ok(s),Ok(r))=(p[1].parse(),p[2].parse()){m.insert(s,r);}}} m }
fn cmap(s:&str)->Vec<usize>{let mut v=s.char_indices().map(|(i,_)|i).collect::<Vec<_>>();v.push(s.len());v}
fn cslice<'a>(s:&'a str,m:&[usize],a:usize,b:usize)->&'a str{&s[m[a.min(m.len()-1)]..m[b.min(m.len()-1)]]}
fn has(t:&str,xs:&[&str])->bool{let z=t.to_lowercase();xs.iter().any(|x|z.contains(x))}
fn points(c:&Cut,s:&Sentence,src:&str,cm:&[usize],res:usize)->Vec<Point>{
    let split=c.split.min(s.tokens.len()); let le=s.tokens[..split].last().map(|t|t.end).unwrap_or(s.start); let rs=s.tokens[split..].first().map(|t|t.start).unwrap_or(s.end);
    let left=cslice(src,cm,s.start,le); let right=cslice(src,cm,rs,s.end); let whole=cslice(src,cm,s.start,s.end);
    let attrib=has(whole,&["according to"," said "," says "," told "," believes"," reported"," argues"," concluded"," asked"," replied"]);
    let quoteish=attrib&&(c.perspective_shift||has(right,&[" i "," we "," i'm "," we're "," our "]));
    let adversative=c.discourse_marker&&has(right,&["but","however","although","yet","well"]);
    let repeat=s.tokens.windows(2).any(|w|w[0].lemma==w[1].lemma&&w[0].lemma.chars().any(|x|x.is_alphabetic()));
    let stable=!c.left_profile.is_empty()&&c.left_profile==c.right_profile&&c.left_profile_score>0&&c.right_profile_score>0;
    let shift=c.profile_shift&&c.left_profile_score>0&&c.right_profile_score>0;
    let syntax=match c.dep_content{0=>3,1=>2,2=>1,3=>0,_=>-2};
    let pnf=match res{0..=4=>2,5..=10=>1,11..=18=>0,_=>-1};
    let world_shift=if shift{3}else if stable{-2}else{0};
    vec![
      Point{fibre:Fibre::Speaker,syntax,pnf,attribution:if quoteish{-2}else{0},speaker:(if c.perspective_shift{2}else{0})+(if shift{3}else{0}),world:world_shift,asr:if repeat{-1}else{0},rhetorical:if adversative{-1}else{0}},
      Point{fibre:Fibre::Quote,syntax:if c.punctuation>0{1}else{0},pnf,attribution:(if attrib{3}else{0})+(if quoteish{2}else{0}),speaker:if c.perspective_shift{1}else{0},world:if shift{1}else{0},asr:0,rhetorical:0},
      Point{fibre:Fibre::Nesting,syntax:0,pnf,attribution:if attrib{4}else{-1},speaker:if shift{-1}else{0},world:0,asr:0,rhetorical:if adversative{1}else{0}},
      Point{fibre:Fibre::Asr,syntax:if c.dep_content>=5{2}else{0},pnf:if res>=10{2}else{0},attribution:0,speaker:0,world:0,asr:(if repeat{4}else{0})+(if c.dep_content>=5{1}else{0}),rhetorical:0},
      Point{fibre:Fibre::Rhetorical,syntax:if c.dep_content<=1{1}else{0},pnf,attribution:if attrib{-1}else{0},speaker:if stable{2}else{0},world:if shift{-2}else{0},asr:if repeat{-1}else{0},rhetorical:(if adversative{4}else{0})+(if c.sentiment_delta>=0.5{1}else{0})},
    ]
}
fn dominates(a:&Point,b:&Point)->bool{
    let av=[a.syntax,a.pnf,a.attribution,a.speaker,a.world,a.asr,a.rhetorical]; let bv=[b.syntax,b.pnf,b.attribution,b.speaker,b.world,b.asr,b.rhetorical];
    av.iter().zip(bv.iter()).all(|(x,y)|x>=y)&&av.iter().zip(bv.iter()).any(|(x,y)|x>y)
}
fn fname(f:Fibre)->&'static str{match f{Fibre::Speaker=>"speaker",Fibre::Quote=>"quote",Fibre::Nesting=>"nesting",Fibre::Asr=>"asr",Fibre::Rhetorical=>"rhetorical"}}
fn main()->Result<(),Box<dyn std::error::Error>>{
    let cfg=args(); let src=fs::read_to_string(&cfg.source)?; let p=parser(&fs::read_to_string(&cfg.parser)?).map_err(|e|format!("parser: {e}"))?; let cs=cuts(&fs::read_to_string(&cfg.cuts)?).map_err(|e|format!("cuts: {e}"))?; let rs=cfg.pnf.as_ref().map(|x|fs::read_to_string(x).map(|z|residuals(&z))).transpose()?.unwrap_or_default(); let cm=cmap(&src);
    eprintln!("SLR_DISCOURSE_MANIFOLD_RECEIPT schema={} scalar_selection=false pareto_front=true residual_retained=true pnf_role=coordinate source={} cuts={}",SCHEMA,cfg.source.display(),cfg.cuts.display());
    println!("schema\tsentence\twithin_sentence_rank\tsplit\tanchor\tfibre\tsyntax\tpnf_residual\tattribution\tspeaker\tworld_model\tasr\trhetorical\tpareto_front\tlegacy_cut_score\tresidual_count\tcandidate_only");
    let mut n=0usize; for c in cs.iter().filter(|x|x.rank<=cfg.max_rank){let Some(s)=p.get(&c.sentence)else{continue};let pts=points(c,s,&src,&cm,*rs.get(&c.sentence).unwrap_or(&0)); for (i,pt) in pts.iter().enumerate(){let front=!pts.iter().enumerate().any(|(j,q)|i!=j&&dominates(q,pt)); println!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\ttrue",SCHEMA,c.sentence,c.rank,c.split,c.anchor,fname(pt.fibre),pt.syntax,pt.pnf,pt.attribution,pt.speaker,pt.world,pt.asr,pt.rhetorical,front,c.cut_score,rs.get(&c.sentence).copied().unwrap_or(0)); n+=1;if n>=cfg.top{return Ok(())}}} Ok(())
}
