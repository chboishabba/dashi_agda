use std::collections::{BTreeMap, HashMap};
use std::env;
use std::fs;
use std::path::PathBuf;

const SCHEMA: &str = "slr-discourse-spans-v1";

#[derive(Clone, Debug)]
struct Config { graph: PathBuf, parser: PathBuf, source: PathBuf, ledger: PathBuf, reconstructed: PathBuf }
#[derive(Clone, Debug)]
struct Sentence { id: usize, start: usize, end: usize, token_starts: Vec<usize> }
#[derive(Clone, Debug)]
struct Boundary { rank: usize, split: usize, projection: String, pareto: String, residual: String, anchor: String }

fn usage() -> ! {
    eprintln!("usage: slr-discourse-spans --graph discourse-graph.tsv --parser parser.tsv --source source.txt --ledger spans.tsv --reconstructed reconstructed.txt");
    std::process::exit(2)
}
fn args() -> Config {
    let a: Vec<String> = env::args().skip(1).collect();
    let (mut graph, mut parser, mut source, mut ledger, mut reconstructed) = (None,None,None,None,None);
    let mut i=0;
    while i<a.len() {
        match a[i].as_str() {
            "--graph" => {i+=1; graph=a.get(i).map(PathBuf::from)},
            "--parser" => {i+=1; parser=a.get(i).map(PathBuf::from)},
            "--source" => {i+=1; source=a.get(i).map(PathBuf::from)},
            "--ledger" => {i+=1; ledger=a.get(i).map(PathBuf::from)},
            "--reconstructed" => {i+=1; reconstructed=a.get(i).map(PathBuf::from)},
            _ => usage(),
        }
        i+=1;
    }
    Config {
        graph: graph.unwrap_or_else(||usage()), parser: parser.unwrap_or_else(||usage()),
        source: source.unwrap_or_else(||usage()), ledger: ledger.unwrap_or_else(||usage()),
        reconstructed: reconstructed.unwrap_or_else(||usage()),
    }
}

fn parse_parser(text:&str)->Result<Vec<Sentence>,String>{
    let mut out=Vec::new(); let mut cur:Option<Sentence>=None;
    for (ln,line) in text.lines().enumerate(){
        let p:Vec<&str>=line.split('\t').collect();
        match p.first().copied().unwrap_or("") {
            "S"=>{
                if let Some(s)=cur.take(){out.push(s)}
                if p.len()<4{return Err(format!("bad S row {}",ln+1))}
                cur=Some(Sentence{id:p[1].parse().map_err(|_|"bad sentence id")?,start:p[2].parse().map_err(|_|"bad sentence start")?,end:p[3].parse().map_err(|_|"bad sentence end")?,token_starts:Vec::new()});
            }
            "T"=>{
                if p.len()<4{return Err(format!("bad T row {}",ln+1))}
                let s=cur.as_mut().ok_or("T before S")?;
                s.token_starts.push(p[2].parse().map_err(|_|"bad token start")?);
            }
            "E"=>if let Some(s)=cur.take(){out.push(s)},
            _=>{}
        }
    }
    if let Some(s)=cur{out.push(s)}
    Ok(out)
}

fn parse_graph(text:&str)->Result<HashMap<usize,Vec<Boundary>>,String>{
    let mut lines=text.lines(); let h=lines.next().ok_or("empty graph")?; let c:Vec<&str>=h.split('\t').collect();
    let ix=|n:&str|c.iter().position(|x|*x==n).ok_or_else(||format!("missing {n}"));
    let is=ix("sentence")?; let ir=ix("within_sentence_rank")?; let isp=ix("split")?;
    let ia=ix("anchor")?; let ip=ix("projection")?; let ifr=ix("pareto_fibres")?; let ire=ix("residual_fibres")?;
    let mut out:HashMap<usize,Vec<Boundary>>=HashMap::new();
    for line in lines {
        let p:Vec<&str>=line.split('\t').collect(); if p.len()<c.len(){continue}
        let sid:usize=p[is].parse().map_err(|_|"bad sentence")?;
        out.entry(sid).or_default().push(Boundary{rank:p[ir].parse().map_err(|_|"bad rank")?,split:p[isp].parse().map_err(|_|"bad split")?,anchor:p[ia].to_string(),projection:p[ip].to_string(),pareto:p[ifr].to_string(),residual:p[ire].to_string()});
    }
    Ok(out)
}

fn char_to_byte_map(s:&str)->Vec<usize>{let mut v=s.char_indices().map(|(i,_)|i).collect::<Vec<_>>();v.push(s.len());v}
fn char_slice<'a>(s:&'a str,m:&[usize],a:usize,b:usize)->&'a str{&s[m[a.min(m.len()-1)]..m[b.min(m.len()-1)]]}

fn main()->Result<(),Box<dyn std::error::Error>>{
    let cfg=args();
    let source=fs::read_to_string(&cfg.source)?;
    let cmap=char_to_byte_map(&source);
    let sentences=parse_parser(&fs::read_to_string(&cfg.parser)?).map_err(|e|format!("parser: {e}"))?;
    let graph=parse_graph(&fs::read_to_string(&cfg.graph)?).map_err(|e|format!("graph: {e}"))?;

    let mut ledger=String::from("schema\tspan_id\tsentence\tsegment_index\tchar_start\tchar_end\tboundary_before\tboundary_projection\tpareto_fibres\tresidual_fibres\tcandidate_only\n");
    let mut reconstructed=String::new();
    let mut span_count=0usize; let mut hard_cut_count=0usize; let mut unresolved_count=0usize;

    for s in sentences {
        let mut cuts:BTreeMap<usize,Boundary>=BTreeMap::new();
        if let Some(bs)=graph.get(&s.id) {
            for b in bs {
                if b.rank==1 && (b.projection=="speaker" || b.projection=="quote") && b.split>0 && b.split<s.token_starts.len() {
                    cuts.insert(b.split,b.clone());
                } else if b.rank==1 && b.projection=="unresolved" {
                    unresolved_count+=1;
                }
            }
        }
        let mut starts=vec![(0usize,s.start,None::<Boundary>)];
        for (split,b) in cuts { starts.push((split,s.token_starts[split],Some(b))); hard_cut_count+=1; }
        starts.sort_by_key(|x|x.1);
        for idx in 0..starts.len() {
            let (_tok,start,before)=&starts[idx];
            let end=if idx+1<starts.len(){starts[idx+1].1}else{s.end};
            if *end<=*start {continue}
            let text=char_slice(&source,&cmap,*start,*end).trim(); if text.is_empty(){continue}
            if !reconstructed.is_empty(){reconstructed.push('\n')}
            reconstructed.push_str(text);
            let (proj,pareto,residual,anchor)=match before {
                Some(b)=>(b.projection.as_str(),b.pareto.as_str(),b.residual.as_str(),b.anchor.as_str()),
                None=>("original-sentence-start","","","")
            };
            ledger.push_str(&format!("{}\ts{}-{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\ttrue\n",SCHEMA,s.id,idx,s.id,idx,start,end,anchor,proj,pareto,residual));
            span_count+=1;
        }
    }
    fs::write(&cfg.ledger,ledger)?;
    fs::write(&cfg.reconstructed,reconstructed)?;
    eprintln!("SLR_DISCOURSE_SPAN_RECEIPT schema={} graph={} spans={} hard_candidate_cuts={} unresolved_rank1={} hard_cut_rule=rank1-singleton-speaker-or-quote candidate_only=true source_preserved=true",SCHEMA,cfg.graph.display(),span_count,hard_cut_count,unresolved_count);
    Ok(())
}
