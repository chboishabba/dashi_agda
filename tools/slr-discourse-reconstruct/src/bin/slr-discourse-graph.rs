use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::PathBuf;

const SCHEMA:&str="slr-discourse-graph-v1";
#[derive(Clone,Debug)] struct Config{manifold:PathBuf}
#[derive(Clone,Debug)] struct Row{sentence:usize,rank:usize,split:usize,anchor:String,fibre:String,front:bool,residual:usize}
fn usage()->!{eprintln!("usage: slr-discourse-graph --manifold discourse-manifold.tsv");std::process::exit(2)}
fn args()->Config{let a:Vec<String>=env::args().skip(1).collect();let mut m=None;let mut i=0;while i<a.len(){match a[i].as_str(){"--manifold"=>{i+=1;m=a.get(i).map(PathBuf::from)},_=>usage()}i+=1}Config{manifold:m.unwrap_or_else(||usage())}}
fn parse(text:&str)->Result<Vec<Row>,String>{let mut ls=text.lines();let h=ls.next().ok_or("empty manifold")?;let c:Vec<&str>=h.split('\t').collect();let ix=|n:&str|c.iter().position(|x|*x==n).ok_or_else(||format!("missing {n}"));let is=ix("sentence")?;let ir=ix("within_sentence_rank")?;let isp=ix("split")?;let ia=ix("anchor")?;let ifi=ix("fibre")?;let iff=ix("pareto_front")?;let ire=ix("residual_count")?;let mut out=vec![];for l in ls{let p:Vec<&str>=l.split('\t').collect();if p.len()<c.len(){continue}out.push(Row{sentence:p[is].parse().map_err(|_|"sentence")?,rank:p[ir].parse().map_err(|_|"rank")?,split:p[isp].parse().map_err(|_|"split")?,anchor:p[ia].to_string(),fibre:p[ifi].to_string(),front:matches!(p[iff],"true"|"True"|"1"),residual:p[ire].parse().unwrap_or(0)});}Ok(out)}
fn main()->Result<(),Box<dyn std::error::Error>>{let cfg=args();let rows=parse(&fs::read_to_string(&cfg.manifold)?).map_err(|e|format!("manifold: {e}"))?;let mut groups:BTreeMap<(usize,usize,usize,String),(Vec<String>,usize)>=BTreeMap::new();for r in rows{let e=groups.entry((r.sentence,r.rank,r.split,r.anchor)).or_insert((vec![],r.residual));if r.front{e.0.push(r.fibre)}}
 eprintln!("SLR_DISCOURSE_GRAPH_RECEIPT schema={} manifold={} projection_rule=singleton-pareto-only residual_retained=true candidate_only=true",SCHEMA,cfg.manifold.display());
 println!("schema\tnode_id\tsentence\twithin_sentence_rank\tsplit\tanchor\tpareto_fibres\tprojection\tresidual_fibres\tpnf_residual_count\tcandidate_only");
 for((s,r,sp,a),(mut front,res))in groups{front.sort();front.dedup();let projection=if front.len()==1{front[0].clone()}else{"unresolved".into()};let all=["speaker","quote","nesting","asr","rhetorical"];let residuals=all.iter().filter(|x|!front.iter().any(|f|f==**x)).copied().collect::<Vec<_>>().join(",");println!("{}\tb{}-{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\ttrue",SCHEMA,s,sp,s,r,sp,a,front.join(","),projection,residuals,res)} Ok(())}
