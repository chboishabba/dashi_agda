use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::env;
use std::fs;
use std::path::PathBuf;

const SCHEMA: &str = "slr-discourse-spans-v4";

#[derive(Clone, Debug)]
struct Config { graph: PathBuf, roles: PathBuf, parser: PathBuf, source: PathBuf, ledger: PathBuf, reconstructed: PathBuf }
#[derive(Clone, Debug)]
struct Sentence { id: usize, start: usize, end: usize, token_starts: Vec<usize> }
#[derive(Clone, Debug, Default)]
struct RoleTopology {
    crossing_roles: String,
    actor_crossing: bool,
    patient_crossing: bool,
    clause_crossing: bool,
    coordination_crossing: bool,
    predicate_aux_crossing: bool,
}
#[derive(Clone, Debug)]
struct Boundary {
    rank: usize,
    split: usize,
    projection: String,
    pareto: String,
    residual: String,
    anchor: String,
    pnf_subject_crossings: usize,
    pnf_object_crossings: usize,
    pnf_clause_crossings: usize,
    pnf_coordination_crossings: usize,
    roles: RoleTopology,
}

fn usage() -> ! {
    eprintln!("usage: slr-discourse-spans --graph discourse-graph.tsv --roles role-transitions.tsv --parser parser.tsv --source source.txt --ledger spans.tsv --reconstructed reconstructed.txt");
    std::process::exit(2)
}
fn args() -> Config {
    let a: Vec<String> = env::args().skip(1).collect();
    let (mut graph, mut roles, mut parser, mut source, mut ledger, mut reconstructed) = (None,None,None,None,None,None);
    let mut i=0;
    while i<a.len() {
        match a[i].as_str() {
            "--graph" => {i+=1; graph=a.get(i).map(PathBuf::from)},
            "--roles" => {i+=1; roles=a.get(i).map(PathBuf::from)},
            "--parser" => {i+=1; parser=a.get(i).map(PathBuf::from)},
            "--source" => {i+=1; source=a.get(i).map(PathBuf::from)},
            "--ledger" => {i+=1; ledger=a.get(i).map(PathBuf::from)},
            "--reconstructed" => {i+=1; reconstructed=a.get(i).map(PathBuf::from)},
            _ => usage(),
        }
        i+=1;
    }
    Config {
        graph: graph.unwrap_or_else(||usage()), roles: roles.unwrap_or_else(||usage()),
        parser: parser.unwrap_or_else(||usage()), source: source.unwrap_or_else(||usage()),
        ledger: ledger.unwrap_or_else(||usage()), reconstructed: reconstructed.unwrap_or_else(||usage()),
    }
}

fn boolv(s:&str)->bool { matches!(s,"true"|"True"|"1") }

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

fn parse_roles(text:&str)->Result<HashMap<(usize,usize),RoleTopology>,String>{
    let mut lines=text.lines(); let h=lines.next().ok_or("empty roles")?; let c:Vec<&str>=h.split('\t').collect();
    let ix=|n:&str|c.iter().position(|x|*x==n).ok_or_else(||format!("missing role column {n}"));
    let is=ix("sentence")?; let isp=ix("split")?; let ir=ix("crossing_roles")?;
    let ia=ix("actor_crossing")?; let ip=ix("patient_crossing")?; let ic=ix("clause_crossing")?;
    let ico=ix("coordination_crossing")?; let ipa=ix("predicate_aux_crossing")?;
    let mut out=HashMap::new();
    for line in lines { let p:Vec<&str>=line.split('\t').collect(); if p.len()<c.len(){continue}
        let sid=p[is].parse().map_err(|_|"bad role sentence")?; let split=p[isp].parse().map_err(|_|"bad role split")?;
        out.insert((sid,split),RoleTopology{crossing_roles:p[ir].to_string(),actor_crossing:boolv(p[ia]),patient_crossing:boolv(p[ip]),clause_crossing:boolv(p[ic]),coordination_crossing:boolv(p[ico]),predicate_aux_crossing:boolv(p[ipa])});
    }
    Ok(out)
}

fn parse_graph(text:&str, roles:&HashMap<(usize,usize),RoleTopology>)->Result<HashMap<usize,Vec<Boundary>>,String>{
    let mut lines=text.lines(); let h=lines.next().ok_or("empty graph")?; let c:Vec<&str>=h.split('\t').collect();
    let ix=|n:&str|c.iter().position(|x|*x==n).ok_or_else(||format!("missing {n}"));
    let is=ix("sentence")?; let ir=ix("within_sentence_rank")?; let isp=ix("split")?;
    let ia=ix("anchor")?; let ip=ix("projection")?; let ifr=ix("pareto_fibres")?; let ire=ix("residual_fibres")?;
    let isu=ix("pnf_subject_crossings")?; let iob=ix("pnf_object_crossings")?;
    let icl=ix("pnf_clause_crossings")?; let ico=ix("pnf_coordination_crossings")?;
    let mut out:HashMap<usize,Vec<Boundary>>=HashMap::new();
    for line in lines {
        let p:Vec<&str>=line.split('\t').collect(); if p.len()<c.len(){continue}
        let sid:usize=p[is].parse().map_err(|_|"bad sentence")?; let split:usize=p[isp].parse().map_err(|_|"bad split")?;
        let role=roles.get(&(sid,split)).cloned().ok_or_else(||format!("missing role topology for sentence={sid} split={split}"))?;
        out.entry(sid).or_default().push(Boundary{
            rank:p[ir].parse().map_err(|_|"bad rank")?, split,
            anchor:p[ia].to_string(), projection:p[ip].to_string(), pareto:p[ifr].to_string(), residual:p[ire].to_string(),
            pnf_subject_crossings:p[isu].parse().unwrap_or(0), pnf_object_crossings:p[iob].parse().unwrap_or(0),
            pnf_clause_crossings:p[icl].parse().unwrap_or(0), pnf_coordination_crossings:p[ico].parse().unwrap_or(0), roles:role,
        });
    }
    Ok(out)
}

// Consumer-specific role compatibility. Coordination and uncategorised modifier
// crossings are retained as observations rather than hard vetoes.
fn speaker_role_safe(b:&Boundary)->bool {
    !b.roles.actor_crossing && !b.roles.patient_crossing && !b.roles.predicate_aux_crossing && !b.roles.clause_crossing
}
fn quote_role_safe(b:&Boundary)->bool {
    // Reporter -> quoted-content may cross a clause attachment, but not an
    // actor/patient or auxiliary-predicate continuation.
    !b.roles.actor_crossing && !b.roles.patient_crossing && !b.roles.predicate_aux_crossing
}
fn hard_cut_admissible(b:&Boundary)->bool {
    if b.rank!=1 {return false}
    match b.projection.as_str() {
        "speaker" => speaker_role_safe(b),
        "quote" => quote_role_safe(b),
        _ => false,
    }
}

fn char_to_byte_map(s:&str)->Vec<usize>{let mut v=s.char_indices().map(|(i,_)|i).collect::<Vec<_>>();v.push(s.len());v}
fn char_slice<'a>(s:&'a str,m:&[usize],a:usize,b:usize)->&'a str{&s[m[a.min(m.len()-1)]..m[b.min(m.len()-1)]]}

fn render_projection(source: &str, cmap: &[usize], hard_cut_positions: &BTreeSet<usize>) -> String {
    let mut out = String::with_capacity(source.len() + hard_cut_positions.len());
    let mut last_byte = 0usize;
    for char_pos in hard_cut_positions {
        let byte = cmap[(*char_pos).min(cmap.len().saturating_sub(1))];
        if byte < last_byte || byte > source.len() { continue; }
        out.push_str(&source[last_byte..byte]);
        if !out.ends_with('\n') { out.push('\n'); }
        last_byte = byte;
    }
    out.push_str(&source[last_byte..]);
    out
}

fn main()->Result<(),Box<dyn std::error::Error>>{
    let cfg=args();
    let source=fs::read_to_string(&cfg.source)?;
    let cmap=char_to_byte_map(&source);
    let sentences=parse_parser(&fs::read_to_string(&cfg.parser)?).map_err(|e|format!("parser: {e}"))?;
    let role_map=parse_roles(&fs::read_to_string(&cfg.roles)?).map_err(|e|format!("roles: {e}"))?;
    let graph=parse_graph(&fs::read_to_string(&cfg.graph)?,&role_map).map_err(|e|format!("graph: {e}"))?;

    let mut ledger=String::from("schema\tspan_id\tsentence\tsegment_index\tchar_start\tchar_end\tboundary_before\tboundary_projection\tpareto_fibres\tresidual_fibres\tcrossing_roles\tactor_crossing\tpatient_crossing\tclause_crossing\tcoordination_crossing\tpredicate_aux_crossing\tpnf_subject_crossings\tpnf_object_crossings\tpnf_clause_crossings\tpnf_coordination_crossings\tcandidate_only\n");
    let mut hard_cut_positions:BTreeSet<usize>=BTreeSet::new();
    let mut span_count=0usize; let mut hard_cut_count=0usize; let mut unresolved_count=0usize; let mut role_blocked_count=0usize;

    for s in sentences {
        let mut cuts:BTreeMap<usize,Boundary>=BTreeMap::new();
        if let Some(bs)=graph.get(&s.id) {
            for b in bs {
                if hard_cut_admissible(b) && b.split>0 && b.split<s.token_starts.len() {
                    cuts.insert(b.split,b.clone());
                } else if b.rank==1 && (b.projection=="speaker" || b.projection=="quote") && !hard_cut_admissible(b) {
                    role_blocked_count+=1;
                } else if b.rank==1 && b.projection=="unresolved" {
                    unresolved_count+=1;
                }
            }
        }
        let mut starts=vec![(0usize,s.start,None::<Boundary>)];
        for (split,b) in cuts {
            let cut_pos=s.token_starts[split];
            hard_cut_positions.insert(cut_pos);
            starts.push((split,cut_pos,Some(b)));
            hard_cut_count+=1;
        }
        starts.sort_by_key(|x|x.1);
        for idx in 0..starts.len() {
            let (_tok,start,before)=&starts[idx];
            let end=if idx+1<starts.len(){starts[idx+1].1}else{s.end};
            if end <= *start {continue}
            let text=char_slice(&source,&cmap,*start,end);
            if text.trim().is_empty(){continue}
            let (proj,pareto,residual,anchor,roles,actor,patient,clause,coord,paux,subj,obj,pclause,pcoord)=match before {
                Some(b)=>(b.projection.as_str(),b.pareto.as_str(),b.residual.as_str(),b.anchor.as_str(),b.roles.crossing_roles.as_str(),b.roles.actor_crossing,b.roles.patient_crossing,b.roles.clause_crossing,b.roles.coordination_crossing,b.roles.predicate_aux_crossing,b.pnf_subject_crossings,b.pnf_object_crossings,b.pnf_clause_crossings,b.pnf_coordination_crossings),
                None=>("original-sentence-start","","","","",false,false,false,false,false,0,0,0,0)
            };
            ledger.push_str(&format!("{}\ts{}-{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\ttrue\n",SCHEMA,s.id,idx,s.id,idx,start,end,anchor,proj,pareto,residual,roles,actor,patient,clause,coord,paux,subj,obj,pclause,pcoord));
            span_count+=1;
        }
    }

    let reconstructed=render_projection(&source,&cmap,&hard_cut_positions);
    fs::write(&cfg.ledger,ledger)?;
    fs::write(&cfg.reconstructed,reconstructed)?;
    eprintln!("SLR_DISCOURSE_SPAN_RECEIPT schema={} graph={} roles={} spans={} hard_candidate_cuts={} role_blocked_rank1_singletons={} unresolved_rank1={} hard_cut_rule=rank1-singleton+typed-role-compatibility speaker_veto=actor,patient,predicate-aux,clause quote_veto=actor,patient,predicate-aux coordination_is_nonfatal=true quote_clause_crossing_permitted=true candidate_only=true source_bytes_preserved=true original_separator_topology_preserved=true projection_adds_boundary_newlines_only=true",SCHEMA,cfg.graph.display(),cfg.roles.display(),span_count,hard_cut_count,role_blocked_count,unresolved_count);
    Ok(())
}
