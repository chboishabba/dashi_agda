use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::PathBuf;

const SCHEMA: &str = "slr-discourse-graph-v2";

#[derive(Clone, Debug)]
struct Config { manifold: PathBuf }

#[derive(Clone, Debug)]
struct Row {
    sentence: usize,
    rank: usize,
    split: usize,
    anchor: String,
    fibre: String,
    front: bool,
    residual: usize,
    pnf_subject_crossings: usize,
    pnf_object_crossings: usize,
    pnf_clause_crossings: usize,
    pnf_coordination_crossings: usize,
    pnf_negation_side_shift: bool,
    pnf_modality_side_shift: bool,
}

#[derive(Clone, Debug)]
struct Group {
    front: Vec<String>,
    residual: usize,
    pnf_subject_crossings: usize,
    pnf_object_crossings: usize,
    pnf_clause_crossings: usize,
    pnf_coordination_crossings: usize,
    pnf_negation_side_shift: bool,
    pnf_modality_side_shift: bool,
}

fn usage() -> ! {
    eprintln!("usage: slr-discourse-graph --manifold discourse-manifold.tsv");
    std::process::exit(2)
}

fn args() -> Config {
    let args: Vec<String> = env::args().skip(1).collect();
    let mut manifold = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--manifold" => { i += 1; manifold = args.get(i).map(PathBuf::from); }
            _ => usage(),
        }
        i += 1;
    }
    Config { manifold: manifold.unwrap_or_else(|| usage()) }
}

fn boolv(s: &str) -> bool { matches!(s, "true" | "True" | "1") }

fn parse(text: &str) -> Result<Vec<Row>, String> {
    let mut lines = text.lines();
    let header = lines.next().ok_or("empty manifold")?;
    let cols: Vec<&str> = header.split('\t').collect();
    let idx = |name: &str| cols.iter().position(|x| *x == name).ok_or_else(|| format!("missing {name}"));
    let i_sentence = idx("sentence")?;
    let i_rank = idx("within_sentence_rank")?;
    let i_split = idx("split")?;
    let i_anchor = idx("anchor")?;
    let i_fibre = idx("fibre")?;
    let i_front = idx("pareto_front")?;
    let i_residual = idx("residual_count")?;
    let i_subj = idx("pnf_subject_crossings")?;
    let i_obj = idx("pnf_object_crossings")?;
    let i_clause = idx("pnf_clause_crossings")?;
    let i_coord = idx("pnf_coordination_crossings")?;
    let i_neg = idx("pnf_negation_side_shift")?;
    let i_modal = idx("pnf_modality_side_shift")?;

    let mut out = Vec::new();
    for line in lines {
        let p: Vec<&str> = line.split('\t').collect();
        if p.len() < cols.len() { continue; }
        out.push(Row {
            sentence: p[i_sentence].parse().map_err(|_| "sentence")?,
            rank: p[i_rank].parse().map_err(|_| "rank")?,
            split: p[i_split].parse().map_err(|_| "split")?,
            anchor: p[i_anchor].to_string(),
            fibre: p[i_fibre].to_string(),
            front: boolv(p[i_front]),
            residual: p[i_residual].parse().unwrap_or(0),
            pnf_subject_crossings: p[i_subj].parse().unwrap_or(0),
            pnf_object_crossings: p[i_obj].parse().unwrap_or(0),
            pnf_clause_crossings: p[i_clause].parse().unwrap_or(0),
            pnf_coordination_crossings: p[i_coord].parse().unwrap_or(0),
            pnf_negation_side_shift: boolv(p[i_neg]),
            pnf_modality_side_shift: boolv(p[i_modal]),
        });
    }
    Ok(out)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cfg = args();
    let rows = parse(&fs::read_to_string(&cfg.manifold)?).map_err(|e| format!("manifold: {e}"))?;

    let mut groups: BTreeMap<(usize, usize, usize, String), Group> = BTreeMap::new();
    for row in rows {
        let entry = groups.entry((row.sentence, row.rank, row.split, row.anchor.clone())).or_insert(Group {
            front: Vec::new(),
            residual: row.residual,
            pnf_subject_crossings: row.pnf_subject_crossings,
            pnf_object_crossings: row.pnf_object_crossings,
            pnf_clause_crossings: row.pnf_clause_crossings,
            pnf_coordination_crossings: row.pnf_coordination_crossings,
            pnf_negation_side_shift: row.pnf_negation_side_shift,
            pnf_modality_side_shift: row.pnf_modality_side_shift,
        });
        if row.front { entry.front.push(row.fibre); }
    }

    eprintln!("SLR_DISCOURSE_GRAPH_RECEIPT schema={} manifold={} projection_rule=singleton-pareto-only pnf_topology_retained=true residual_retained=true candidate_only=true", SCHEMA, cfg.manifold.display());
    println!("schema\tnode_id\tsentence\twithin_sentence_rank\tsplit\tanchor\tpareto_fibres\tprojection\tresidual_fibres\tpnf_residual_count\tpnf_subject_crossings\tpnf_object_crossings\tpnf_clause_crossings\tpnf_coordination_crossings\tpnf_negation_side_shift\tpnf_modality_side_shift\tcandidate_only");

    for ((sentence, rank, split, anchor), mut group) in groups {
        group.front.sort();
        group.front.dedup();
        let projection = if group.front.len() == 1 { group.front[0].clone() } else { "unresolved".to_string() };
        let all = ["speaker", "quote", "nesting", "asr", "rhetorical"];
        let residual_fibres = all.iter().filter(|name| !group.front.iter().any(|f| f == *name)).copied().collect::<Vec<_>>().join(",");
        println!("{}\tb{}-{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\ttrue",
            SCHEMA, sentence, split, sentence, rank, split, anchor, group.front.join(","), projection, residual_fibres,
            group.residual, group.pnf_subject_crossings, group.pnf_object_crossings, group.pnf_clause_crossings,
            group.pnf_coordination_crossings, group.pnf_negation_side_shift, group.pnf_modality_side_shift);
    }
    Ok(())
}
