use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::PathBuf;

const SCHEMA: &str = "slr-discourse-graph-v1";

#[derive(Clone, Debug)]
struct Config {
    manifold: PathBuf,
}

#[derive(Clone, Debug)]
struct Row {
    sentence: usize,
    rank: usize,
    split: usize,
    anchor: String,
    fibre: String,
    front: bool,
    residual: usize,
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
            "--manifold" => {
                i += 1;
                manifold = args.get(i).map(PathBuf::from);
            }
            _ => usage(),
        }
        i += 1;
    }
    Config {
        manifold: manifold.unwrap_or_else(|| usage()),
    }
}

fn parse(text: &str) -> Result<Vec<Row>, String> {
    let mut lines = text.lines();
    let header = lines.next().ok_or("empty manifold")?;
    let cols: Vec<&str> = header.split('\t').collect();
    let idx = |name: &str| {
        cols.iter()
            .position(|x| *x == name)
            .ok_or_else(|| format!("missing {name}"))
    };
    let i_sentence = idx("sentence")?;
    let i_rank = idx("within_sentence_rank")?;
    let i_split = idx("split")?;
    let i_anchor = idx("anchor")?;
    let i_fibre = idx("fibre")?;
    let i_front = idx("pareto_front")?;
    let i_residual = idx("residual_count")?;

    let mut out = Vec::new();
    for line in lines {
        let p: Vec<&str> = line.split('\t').collect();
        if p.len() < cols.len() {
            continue;
        }
        out.push(Row {
            sentence: p[i_sentence].parse().map_err(|_| "sentence")?,
            rank: p[i_rank].parse().map_err(|_| "rank")?,
            split: p[i_split].parse().map_err(|_| "split")?,
            anchor: p[i_anchor].to_string(),
            fibre: p[i_fibre].to_string(),
            front: matches!(p[i_front], "true" | "True" | "1"),
            residual: p[i_residual].parse().unwrap_or(0),
        });
    }
    Ok(out)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cfg = args();
    let rows = parse(&fs::read_to_string(&cfg.manifold)?)
        .map_err(|e| format!("manifold: {e}"))?;

    let mut groups: BTreeMap<(usize, usize, usize, String), (Vec<String>, usize)> =
        BTreeMap::new();
    for row in rows {
        let entry = groups
            .entry((row.sentence, row.rank, row.split, row.anchor))
            .or_insert((Vec::new(), row.residual));
        if row.front {
            entry.0.push(row.fibre);
        }
    }

    eprintln!(
        "SLR_DISCOURSE_GRAPH_RECEIPT schema={} manifold={} projection_rule=singleton-pareto-only residual_retained=true candidate_only=true",
        SCHEMA,
        cfg.manifold.display()
    );
    println!(
        "schema\tnode_id\tsentence\twithin_sentence_rank\tsplit\tanchor\tpareto_fibres\tprojection\tresidual_fibres\tpnf_residual_count\tcandidate_only"
    );

    for ((sentence, rank, split, anchor), (mut front, residual_count)) in groups {
        front.sort();
        front.dedup();
        let projection = if front.len() == 1 {
            front[0].clone()
        } else {
            "unresolved".to_string()
        };
        let all = ["speaker", "quote", "nesting", "asr", "rhetorical"];
        let residual_fibres = all
            .iter()
            .filter(|name| !front.iter().any(|f| f.as_str() == *name))
            .copied()
            .collect::<Vec<_>>()
            .join(",");

        println!(
            "{}\tb{}-{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\ttrue",
            SCHEMA,
            sentence,
            split,
            sentence,
            rank,
            split,
            anchor,
            front.join(","),
            projection,
            residual_fibres,
            residual_count
        );
    }
    Ok(())
}
