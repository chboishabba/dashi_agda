use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::PathBuf;

const SCHEMA: &str = "slr-discourse-quality-v1";

#[derive(Clone, Debug)]
struct Config { graph: PathBuf, roles: PathBuf }

#[derive(Clone, Debug)]
struct GraphRow {
    node_id: String,
    sentence: usize,
    rank: usize,
    split: usize,
    anchor: String,
    pareto: Vec<String>,
    projection: String,
    residual_count: usize,
    clause_crossing: bool,
    negation_shift: bool,
    modality_shift: bool,
}

#[derive(Clone, Debug, Default)]
struct RoleRow {
    actor: bool,
    patient: bool,
    clause: bool,
    coordination: bool,
    predicate_aux: bool,
    crossing_roles: String,
}

fn usage() -> ! {
    eprintln!("usage: slr-discourse-quality --graph discourse-graph.tsv --roles role-transitions.tsv");
    std::process::exit(2)
}

fn args() -> Config {
    let a: Vec<String> = env::args().skip(1).collect();
    let (mut graph, mut roles) = (None, None);
    let mut i = 0;
    while i < a.len() {
        match a[i].as_str() {
            "--graph" => { i += 1; graph = a.get(i).map(PathBuf::from); }
            "--roles" => { i += 1; roles = a.get(i).map(PathBuf::from); }
            _ => usage(),
        }
        i += 1;
    }
    Config { graph: graph.unwrap_or_else(|| usage()), roles: roles.unwrap_or_else(|| usage()) }
}

fn boolv(s: &str) -> bool { matches!(s, "true" | "True" | "1") }

fn parse_graph(text: &str) -> Result<Vec<GraphRow>, String> {
    let mut lines = text.lines();
    let h = lines.next().ok_or("empty graph")?;
    let c: Vec<&str> = h.split('\t').collect();
    let ix = |n:&str| c.iter().position(|x| *x == n).ok_or_else(|| format!("missing {n}"));
    let ino=ix("node_id")?; let is=ix("sentence")?; let ir=ix("within_sentence_rank")?; let isp=ix("split")?;
    let ia=ix("anchor")?; let ipf=ix("pareto_fibres")?; let ip=ix("projection")?; let ires=ix("pnf_residual_count")?;
    let ic=ix("pnf_clause_crossings")?; let ineg=ix("pnf_negation_side_shift")?; let imod=ix("pnf_modality_side_shift")?;
    let mut out=Vec::new();
    for l in lines {
        let p:Vec<&str>=l.split('\t').collect(); if p.len()<c.len(){continue}
        out.push(GraphRow{
            node_id:p[ino].to_string(), sentence:p[is].parse().map_err(|_|"sentence")?, rank:p[ir].parse().map_err(|_|"rank")?,
            split:p[isp].parse().map_err(|_|"split")?, anchor:p[ia].to_string(),
            pareto:p[ipf].split(',').filter(|x|!x.is_empty()).map(|x|x.to_string()).collect(),
            projection:p[ip].to_string(), residual_count:p[ires].parse().unwrap_or(0), clause_crossing:p[ic].parse::<usize>().unwrap_or(0)>0,
            negation_shift:boolv(p[ineg]), modality_shift:boolv(p[imod]),
        });
    }
    Ok(out)
}

fn parse_roles(text:&str)->Result<HashMap<(usize,usize),RoleRow>,String>{
    let mut lines=text.lines(); let h=lines.next().ok_or("empty roles")?; let c:Vec<&str>=h.split('\t').collect();
    let ix=|n:&str|c.iter().position(|x|*x==n).ok_or_else(||format!("missing {n}"));
    let is=ix("sentence")?; let isp=ix("split")?; let iro=ix("crossing_roles")?; let ia=ix("actor_crossing")?; let ipa=ix("patient_crossing")?;
    let ic=ix("clause_crossing")?; let ico=ix("coordination_crossing")?; let ipr=ix("predicate_aux_crossing")?;
    let mut out=HashMap::new();
    for l in lines { let p:Vec<&str>=l.split('\t').collect(); if p.len()<c.len(){continue}
        out.insert((p[is].parse().map_err(|_|"sentence")?,p[isp].parse().map_err(|_|"split")?),RoleRow{
            actor:boolv(p[ia]),patient:boolv(p[ipa]),clause:boolv(p[ic]),coordination:boolv(p[ico]),predicate_aux:boolv(p[ipr]),crossing_roles:p[iro].to_string()
        });
    }
    Ok(out)
}

fn contains(xs:&[String], x:&str)->bool { xs.iter().any(|y| y==x) }
fn hard_cut_admissible(g:&GraphRow,r:&RoleRow)->bool{
    if g.rank!=1{return false}
    match g.projection.as_str(){
        "speaker" => !r.actor&&!r.patient&&!r.predicate_aux&&!r.clause,
        "quote" => !r.actor&&!r.patient&&!r.predicate_aux,
        _ => false,
    }
}
fn esc(s:&str)->String{s.replace('\t'," ").replace('\n'," ")}

fn main()->Result<(),Box<dyn std::error::Error>>{
    let c=args();
    let graph=parse_graph(&fs::read_to_string(&c.graph)?).map_err(|e|format!("graph: {e}"))?;
    let roles=parse_roles(&fs::read_to_string(&c.roles)?).map_err(|e|format!("roles: {e}"))?;

    let mut rank1=0usize; let mut unresolved=0usize; let mut admitted=0usize; let mut blocked=0usize;
    let mut attribution_ambiguity=0usize; let mut speaker_ambiguity=0usize; let mut clause_attribution=0usize;
    let mut hidden_speaker_splice_risk=0usize; let mut false_cut_risk=0usize; let mut fibre_width_sum=0usize;
    let mut negation_shifts=0usize; let mut modality_shifts=0usize;

    println!("schema\tnode_id\tsentence\tsplit\tanchor\tprojection\tpareto_fibres\tpareto_width\tcrossing_roles\thard_cut_admissible\tattribution_ambiguity\tspeaker_ambiguity\tclause_attribution_ambiguity\thidden_speaker_splice_risk\tfalse_cut_risk\tnegation_side_shift\tmodality_side_shift\tpnf_residual_count\tworld_mismatch_observed\tcandidate_only");
    for g in graph.iter().filter(|g|g.rank==1){
        rank1+=1; fibre_width_sum+=g.pareto.len(); if g.projection=="unresolved"{unresolved+=1}
        let r=roles.get(&(g.sentence,g.split)).cloned().unwrap_or_default();
        let hard=hard_cut_admissible(g,&r); if hard{admitted+=1}else if g.projection=="speaker"||g.projection=="quote"{blocked+=1}
        let attr= g.pareto.len()>1 && (contains(&g.pareto,"quote")||contains(&g.pareto,"nesting"));
        let spamb= g.pareto.len()>1 && contains(&g.pareto,"speaker");
        let clattr= g.clause_crossing && (contains(&g.pareto,"quote")||contains(&g.pareto,"nesting"));
        let hidden= g.projection=="unresolved" && contains(&g.pareto,"speaker") && !r.actor&&!r.patient&&!r.predicate_aux&&!r.clause;
        let fcr= g.projection=="speaker" && !hard;
        if attr{attribution_ambiguity+=1} if spamb{speaker_ambiguity+=1} if clattr{clause_attribution+=1}
        if hidden{hidden_speaker_splice_risk+=1} if fcr{false_cut_risk+=1} if g.negation_shift{negation_shifts+=1} if g.modality_shift{modality_shifts+=1}
        println!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\tnot-observed\ttrue",
            SCHEMA,g.node_id,g.sentence,g.split,esc(&g.anchor),g.projection,g.pareto.join(","),g.pareto.len(),r.crossing_roles,hard,attr,spamb,clattr,hidden,fcr,g.negation_shift,g.modality_shift,g.residual_count);
    }
    eprintln!("SLR_DISCOURSE_QUALITY_RECEIPT schema={} rank1={} unresolved={} admitted_hard_cuts={} typed_role_blocked={} attribution_ambiguity={} speaker_ambiguity={} clause_attribution_ambiguity={} hidden_speaker_splice_risk={} false_cut_risk={} pareto_width_sum={} negation_shifts={} modality_shifts={} world_mismatch_observed=false comparison_only=true candidate_only=true",
        SCHEMA,rank1,unresolved,admitted,blocked,attribution_ambiguity,speaker_ambiguity,clause_attribution,hidden_speaker_splice_risk,false_cut_risk,fibre_width_sum,negation_shifts,modality_shifts);
    Ok(())
}
