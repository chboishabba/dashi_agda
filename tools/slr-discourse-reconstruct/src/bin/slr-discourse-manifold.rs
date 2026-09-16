use std::collections::{BTreeMap, HashMap};
use std::env;
use std::fs;
use std::path::PathBuf;

const SCHEMA: &str = "slr-discourse-manifold-v2";

#[derive(Clone, Debug)]
struct Config {
    cuts: PathBuf,
    parser: PathBuf,
    source: PathBuf,
    pnf: Option<PathBuf>,
    max_rank: usize,
    top: usize,
}

#[derive(Clone, Debug)]
struct Token {
    ordinal: usize,
    head: usize,
    start: usize,
    end: usize,
    text: String,
    lemma: String,
    dep: String,
}

#[derive(Clone, Debug)]
struct Sentence {
    id: usize,
    start: usize,
    end: usize,
    tokens: Vec<Token>,
}

#[derive(Clone, Debug)]
struct Cut {
    sentence: usize,
    rank: usize,
    split: usize,
    anchor: String,
    cut_score: i32,
    dep_content: usize,
    punctuation: i32,
    discourse_marker: bool,
    perspective_shift: bool,
    sentiment_delta: f64,
    left_profile: String,
    right_profile: String,
    left_profile_score: i32,
    right_profile_score: i32,
    profile_shift: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Fibre {
    Speaker,
    Quote,
    Nesting,
    Asr,
    Rhetorical,
}

#[derive(Clone, Debug, Default)]
struct PnfTopology {
    subject_crossings: usize,
    object_crossings: usize,
    clause_crossings: usize,
    coordination_crossings: usize,
    negation_side_shift: bool,
    modality_side_shift: bool,
}

#[derive(Clone, Debug)]
struct Point {
    fibre: Fibre,
    syntax: i32,
    pnf_structure: i32,
    pnf_residual: i32,
    attribution: i32,
    speaker: i32,
    world: i32,
    asr: i32,
    rhetorical: i32,
}

fn usage() -> ! {
    eprintln!("usage: slr-discourse-manifold --cuts discourse-cuts.tsv --parser parser.tsv --source source.txt [--pnf pnf.stdout] [--max-rank 3] [--top 1000]");
    std::process::exit(2)
}

fn args() -> Config {
    let args: Vec<String> = env::args().skip(1).collect();
    let (mut cuts, mut parser, mut source, mut pnf) = (None, None, None, None);
    let (mut max_rank, mut top) = (3usize, 1000usize);
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--cuts" => { i += 1; cuts = args.get(i).map(PathBuf::from); }
            "--parser" => { i += 1; parser = args.get(i).map(PathBuf::from); }
            "--source" => { i += 1; source = args.get(i).map(PathBuf::from); }
            "--pnf" => { i += 1; pnf = args.get(i).map(PathBuf::from); }
            "--max-rank" => { i += 1; max_rank = args.get(i).and_then(|x| x.parse().ok()).unwrap_or(3); }
            "--top" => { i += 1; top = args.get(i).and_then(|x| x.parse().ok()).unwrap_or(1000); }
            _ => usage(),
        }
        i += 1;
    }
    Config {
        cuts: cuts.unwrap_or_else(|| usage()),
        parser: parser.unwrap_or_else(|| usage()),
        source: source.unwrap_or_else(|| usage()),
        pnf,
        max_rank,
        top,
    }
}

fn boolv(s: &str) -> bool {
    matches!(s, "true" | "True" | "1")
}

fn parse_parser(text: &str) -> Result<HashMap<usize, Sentence>, String> {
    let mut out = HashMap::new();
    let mut current: Option<Sentence> = None;
    for (line_no, line) in text.lines().enumerate() {
        let p: Vec<&str> = line.split('\t').collect();
        match p.first().copied().unwrap_or("") {
            "S" => {
                if let Some(s) = current.take() { out.insert(s.id, s); }
                if p.len() < 4 { return Err(format!("bad S row at line {}", line_no + 1)); }
                current = Some(Sentence {
                    id: p[1].parse().map_err(|_| format!("bad sentence id at line {}", line_no + 1))?,
                    start: p[2].parse().map_err(|_| format!("bad sentence start at line {}", line_no + 1))?,
                    end: p[3].parse().map_err(|_| format!("bad sentence end at line {}", line_no + 1))?,
                    tokens: Vec::new(),
                });
            }
            "T" => {
                if p.len() < 10 { return Err(format!("bad T row at line {}", line_no + 1)); }
                let s = current.as_mut().ok_or_else(|| format!("T before S at line {}", line_no + 1))?;
                s.tokens.push(Token {
                    ordinal: p[1].parse().map_err(|_| format!("bad ordinal at line {}", line_no + 1))?,
                    start: p[2].parse().map_err(|_| format!("bad token start at line {}", line_no + 1))?,
                    end: p[3].parse().map_err(|_| format!("bad token end at line {}", line_no + 1))?,
                    head: p[4].parse().map_err(|_| format!("bad head at line {}", line_no + 1))?,
                    text: p[5].to_string(),
                    lemma: p[6].to_lowercase(),
                    dep: p[9].to_string(),
                });
            }
            "E" => if let Some(s) = current.take() { out.insert(s.id, s); },
            _ => {}
        }
    }
    if let Some(s) = current { out.insert(s.id, s); }
    Ok(out)
}

fn parse_cuts(text: &str) -> Result<Vec<Cut>, String> {
    let mut lines = text.lines();
    let header = lines.next().ok_or("empty cuts")?;
    let cols: Vec<&str> = header.split('\t').collect();
    let idx = |name: &str| cols.iter().position(|x| *x == name).ok_or_else(|| format!("missing {name}"));
    let i_sentence = idx("sentence")?;
    let i_rank = idx("within_sentence_rank")?;
    let i_split = idx("split")?;
    let i_anchor = idx("anchor")?;
    let i_cut = idx("cut_score")?;
    let i_dep = idx("dep_crossings_content")?;
    let i_punc = idx("punctuation")?;
    let i_dm = idx("discourse_marker")?;
    let i_ps = idx("perspective_shift")?;
    let i_sd = idx("sentiment_delta")?;
    let i_lp = idx("left_profile")?;
    let i_lps = idx("left_profile_score")?;
    let i_rp = idx("right_profile")?;
    let i_rps = idx("right_profile_score")?;
    let i_prof = idx("profile_shift")?;

    let mut out = Vec::new();
    for line in lines {
        let p: Vec<&str> = line.split('\t').collect();
        if p.len() < cols.len() { continue; }
        out.push(Cut {
            sentence: p[i_sentence].parse().map_err(|_| "sentence")?,
            rank: p[i_rank].parse().map_err(|_| "rank")?,
            split: p[i_split].parse().map_err(|_| "split")?,
            anchor: p[i_anchor].to_string(),
            cut_score: p[i_cut].parse().map_err(|_| "cut")?,
            dep_content: p[i_dep].parse().map_err(|_| "dep")?,
            punctuation: p[i_punc].parse().map_err(|_| "punctuation")?,
            discourse_marker: boolv(p[i_dm]),
            perspective_shift: boolv(p[i_ps]),
            sentiment_delta: p[i_sd].parse().map_err(|_| "sentiment")?,
            left_profile: p[i_lp].to_string(),
            left_profile_score: p[i_lps].parse().map_err(|_| "left profile")?,
            right_profile: p[i_rp].to_string(),
            right_profile_score: p[i_rps].parse().map_err(|_| "right profile")?,
            profile_shift: boolv(p[i_prof]),
        });
    }
    Ok(out)
}

fn parse_residuals(text: &str) -> BTreeMap<usize, usize> {
    let mut out = BTreeMap::new();
    for line in text.lines() {
        let p: Vec<&str> = line.split('\t').collect();
        if p.first() == Some(&"R") && p.len() >= 3 {
            if let (Ok(sentence), Ok(count)) = (p[1].parse::<usize>(), p[2].parse::<usize>()) {
                out.insert(sentence, count);
            }
        }
    }
    out
}

fn char_to_byte_map(s: &str) -> Vec<usize> {
    let mut out = s.char_indices().map(|(i, _)| i).collect::<Vec<_>>();
    out.push(s.len());
    out
}

fn char_slice<'a>(s: &'a str, map: &[usize], a: usize, b: usize) -> &'a str {
    &s[map[a.min(map.len() - 1)]..map[b.min(map.len() - 1)]]
}

fn contains_any(text: &str, xs: &[&str]) -> bool {
    let t = text.to_lowercase();
    xs.iter().any(|x| t.contains(x))
}

fn crosses(t: &Token, split: usize) -> bool {
    t.head != t.ordinal && ((t.ordinal < split) != (t.head < split))
}

fn pnf_topology(tokens: &[Token], split: usize) -> PnfTopology {
    let mut out = PnfTopology::default();
    for t in tokens.iter().filter(|t| crosses(t, split)) {
        match t.dep.as_str() {
            "nsubj" | "nsubjpass" | "csubj" | "csubjpass" => out.subject_crossings += 1,
            "obj" | "dobj" | "iobj" | "pobj" => out.object_crossings += 1,
            "ccomp" | "xcomp" | "advcl" | "acl" | "relcl" => out.clause_crossings += 1,
            "cc" | "conj" => out.coordination_crossings += 1,
            _ => {}
        }
    }
    let left = &tokens[..split.min(tokens.len())];
    let right = &tokens[split.min(tokens.len())..];
    let neg = |xs: &[Token]| xs.iter().any(|t| t.dep == "neg" || t.lemma == "not" || t.lemma == "n't");
    let modal = |xs: &[Token]| xs.iter().any(|t| matches!(t.lemma.as_str(), "can" | "could" | "may" | "might" | "must" | "shall" | "should" | "will" | "would"));
    out.negation_side_shift = neg(left) != neg(right);
    out.modality_side_shift = modal(left) != modal(right);
    out
}

fn fibre_points(c: &Cut, s: &Sentence, source: &str, cmap: &[usize], residuals: usize) -> (PnfTopology, Vec<Point>) {
    let split = c.split.min(s.tokens.len());
    let left_end = s.tokens[..split].last().map(|t| t.end).unwrap_or(s.start);
    let right_start = s.tokens[split..].first().map(|t| t.start).unwrap_or(s.end);
    let right_text = char_slice(source, cmap, right_start, s.end);
    let whole_text = char_slice(source, cmap, s.start, s.end);

    let topology = pnf_topology(&s.tokens, split);
    let attribution = contains_any(whole_text, &["according to", " said ", " says ", " told ", " believes", " reported", " argues", " concluded", " asked", " replied"]);
    let quote_like = attribution && (c.perspective_shift || contains_any(right_text, &[" i ", " we ", " i'm ", " we're ", " our "]));
    let adversative = c.discourse_marker && contains_any(right_text, &["but", "however", "although", "yet", "well"]);
    let repeated = s.tokens.windows(2).any(|w| w[0].lemma == w[1].lemma && w[0].lemma.chars().any(|x| x.is_alphabetic()));
    let stable_profile = !c.left_profile.is_empty() && c.left_profile == c.right_profile && c.left_profile_score > 0 && c.right_profile_score > 0;
    let profile_shift = c.profile_shift && c.left_profile_score > 0 && c.right_profile_score > 0;

    let syntax = match c.dep_content { 0 => 3, 1 => 2, 2 => 1, 3 => 0, _ => -2 };
    let pnf_residual = match residuals { 0..=4 => 2, 5..=10 => 1, 11..=18 => 0, _ => -1 };
    let world_shift = if profile_shift { 3 } else if stable_profile { -2 } else { 0 };

    let speaker_pnf = if topology.clause_crossings == 0 { 2 } else if topology.clause_crossings == 1 { 0 } else { -2 };
    let quote_pnf = (topology.clause_crossings.min(2) as i32) + if topology.subject_crossings > 0 { 1 } else { 0 };
    let nesting_pnf = (topology.clause_crossings.min(2) as i32) + if attribution { 2 } else { 0 };
    let asr_pnf = if c.dep_content >= 5 { 2 } else { 0 } + if residuals >= 10 { 1 } else { 0 };
    let rhetorical_pnf = (topology.coordination_crossings.min(2) as i32) + if topology.modality_side_shift { 1 } else { 0 };

    let points = vec![
        Point {
            fibre: Fibre::Speaker,
            syntax,
            pnf_structure: speaker_pnf,
            pnf_residual,
            attribution: if quote_like { -2 } else { 0 },
            speaker: (if c.perspective_shift { 2 } else { 0 }) + (if profile_shift { 3 } else { 0 }),
            world: world_shift,
            asr: if repeated { -1 } else { 0 },
            rhetorical: if adversative { -1 } else { 0 },
        },
        Point {
            fibre: Fibre::Quote,
            syntax: if c.punctuation > 0 { 1 } else { 0 },
            pnf_structure: quote_pnf,
            pnf_residual,
            attribution: (if attribution { 3 } else { 0 }) + (if quote_like { 2 } else { 0 }),
            speaker: if c.perspective_shift { 1 } else { 0 },
            world: if profile_shift { 1 } else { 0 },
            asr: 0,
            rhetorical: 0,
        },
        Point {
            fibre: Fibre::Nesting,
            syntax: 0,
            pnf_structure: nesting_pnf,
            pnf_residual,
            attribution: if attribution { 4 } else { -1 },
            speaker: if profile_shift { -1 } else { 0 },
            world: 0,
            asr: 0,
            rhetorical: if adversative { 1 } else { 0 },
        },
        Point {
            fibre: Fibre::Asr,
            syntax: if c.dep_content >= 5 { 2 } else { 0 },
            pnf_structure: asr_pnf,
            pnf_residual: if residuals >= 10 { 2 } else { 0 },
            attribution: 0,
            speaker: 0,
            world: 0,
            asr: (if repeated { 4 } else { 0 }) + (if c.dep_content >= 5 { 1 } else { 0 }),
            rhetorical: 0,
        },
        Point {
            fibre: Fibre::Rhetorical,
            syntax: if c.dep_content <= 1 { 1 } else { 0 },
            pnf_structure: rhetorical_pnf,
            pnf_residual,
            attribution: if attribution { -1 } else { 0 },
            speaker: if stable_profile { 2 } else { 0 },
            world: if profile_shift { -2 } else { 0 },
            asr: if repeated { -1 } else { 0 },
            rhetorical: (if adversative { 4 } else { 0 }) + (if c.sentiment_delta >= 0.5 { 1 } else { 0 }),
        },
    ];
    (topology, points)
}

fn dominates(a: &Point, b: &Point) -> bool {
    let av = [a.syntax, a.pnf_structure, a.pnf_residual, a.attribution, a.speaker, a.world, a.asr, a.rhetorical];
    let bv = [b.syntax, b.pnf_structure, b.pnf_residual, b.attribution, b.speaker, b.world, b.asr, b.rhetorical];
    av.iter().zip(bv.iter()).all(|(x, y)| x >= y)
        && av.iter().zip(bv.iter()).any(|(x, y)| x > y)
}

fn fibre_name(f: Fibre) -> &'static str {
    match f {
        Fibre::Speaker => "speaker",
        Fibre::Quote => "quote",
        Fibre::Nesting => "nesting",
        Fibre::Asr => "asr",
        Fibre::Rhetorical => "rhetorical",
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cfg = args();
    let source = fs::read_to_string(&cfg.source)?;
    let parser = parse_parser(&fs::read_to_string(&cfg.parser)?).map_err(|e| format!("parser: {e}"))?;
    let cuts = parse_cuts(&fs::read_to_string(&cfg.cuts)?).map_err(|e| format!("cuts: {e}"))?;
    let residuals = cfg.pnf.as_ref().map(|p| fs::read_to_string(p).map(|s| parse_residuals(&s))).transpose()?.unwrap_or_default();
    let cmap = char_to_byte_map(&source);

    eprintln!(
        "SLR_DISCOURSE_MANIFOLD_RECEIPT schema={} scalar_selection=false pareto_front=true residual_retained=true pnf_role=topology+residual world_role=profile-compatibility source={} cuts={}",
        SCHEMA,
        cfg.source.display(),
        cfg.cuts.display()
    );
    println!("schema\tsentence\twithin_sentence_rank\tsplit\tanchor\tfibre\tsyntax\tpnf_structure\tpnf_residual\tattribution\tspeaker\tworld_model\tasr\trhetorical\tpnf_subject_crossings\tpnf_object_crossings\tpnf_clause_crossings\tpnf_coordination_crossings\tpnf_negation_side_shift\tpnf_modality_side_shift\tpareto_front\tlegacy_cut_score\tresidual_count\tcandidate_only");

    let mut emitted = 0usize;
    for cut in cuts.iter().filter(|c| c.rank <= cfg.max_rank) {
        let Some(sentence) = parser.get(&cut.sentence) else { continue; };
        let residual_count = residuals.get(&cut.sentence).copied().unwrap_or(0);
        let (topology, points) = fibre_points(cut, sentence, &source, &cmap, residual_count);
        for (i, point) in points.iter().enumerate() {
            let front = !points.iter().enumerate().any(|(j, other)| i != j && dominates(other, point));
            println!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\ttrue",
                SCHEMA,
                cut.sentence,
                cut.rank,
                cut.split,
                cut.anchor,
                fibre_name(point.fibre),
                point.syntax,
                point.pnf_structure,
                point.pnf_residual,
                point.attribution,
                point.speaker,
                point.world,
                point.asr,
                point.rhetorical,
                topology.subject_crossings,
                topology.object_crossings,
                topology.clause_crossings,
                topology.coordination_crossings,
                topology.negation_side_shift,
                topology.modality_side_shift,
                front,
                cut.cut_score,
                residual_count
            );
            emitted += 1;
            if emitted >= cfg.top { return Ok(()); }
        }
    }
    Ok(())
}
