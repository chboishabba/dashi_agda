use std::collections::{BTreeMap, HashMap, HashSet};
use std::env;
use std::fs;
use std::path::PathBuf;
use vader_parity::SentimentIntensityAnalyzer;

const SCHEMA: &str = "slr-discourse-cut-v2";

#[derive(Clone, Debug)]
struct Token {
    ordinal: usize,
    start: usize,
    end: usize,
    head: usize,
    text: String,
    lemma: String,
    pos: String,
    dep: String,
}

#[derive(Clone, Debug)]
struct Sentence {
    id: usize,
    start: usize,
    end: usize,
    tokens: Vec<Token>,
}

#[derive(Clone, Debug, Default)]
struct Profile { weights: HashMap<String, i32> }

#[derive(Clone, Debug)]
struct Config {
    parser: PathBuf,
    source: PathBuf,
    pnf: Option<PathBuf>,
    source_sha: Option<PathBuf>,
    profiles: Option<PathBuf>,
    focus: Option<Vec<usize>>,
    top: usize,
}

#[derive(Clone, Debug)]
struct Candidate {
    sentence_id: usize,
    split: usize,
    anchor: String,
    cut_score: i32,
    inspection_priority: i32,
    within_sentence_rank: usize,
    dep_crossings_raw: usize,
    dep_crossings_content: usize,
    residuals: usize,
    residual_density_milli: usize,
    punctuation_strength: i32,
    discourse_marker: bool,
    perspective_shift: bool,
    sentiment_delta: f64,
    sentiment_contribution: i32,
    left_compound: f64,
    right_compound: f64,
    left_profile: String,
    right_profile: String,
    left_profile_score: i32,
    right_profile_score: i32,
    profile_shift: bool,
}

fn usage() -> ! {
    eprintln!("usage: slr-discourse-reconstruct --parser parser.tsv --source source.txt [--pnf pnf.stdout] [--source-sha source.sha256] [--profiles speaker-profiles.tsv] [--focus 42,45] [--top 25]");
    std::process::exit(2);
}

fn parse_args() -> Config {
    let mut parser = None; let mut source = None; let mut pnf = None; let mut source_sha = None;
    let mut profiles = None; let mut focus = None; let mut top = 25usize;
    let args: Vec<String> = env::args().skip(1).collect();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--parser" => { i += 1; parser = args.get(i).map(PathBuf::from); }
            "--source" => { i += 1; source = args.get(i).map(PathBuf::from); }
            "--pnf" => { i += 1; pnf = args.get(i).map(PathBuf::from); }
            "--source-sha" => { i += 1; source_sha = args.get(i).map(PathBuf::from); }
            "--profiles" => { i += 1; profiles = args.get(i).map(PathBuf::from); }
            "--focus" => { i += 1; focus = args.get(i).map(|s| s.split(',').filter_map(|x| x.parse::<usize>().ok()).collect::<Vec<_>>()); }
            "--top" => { i += 1; top = args.get(i).and_then(|s| s.parse().ok()).unwrap_or(25); }
            _ => usage(),
        }
        i += 1;
    }
    Config { parser: parser.unwrap_or_else(|| usage()), source: source.unwrap_or_else(|| usage()), pnf, source_sha, profiles, focus, top }
}

fn parse_parser_tsv(text: &str) -> Result<Vec<Sentence>, String> {
    let mut out = Vec::new(); let mut current: Option<Sentence> = None;
    for (line_no, line) in text.lines().enumerate() {
        let parts: Vec<&str> = line.split('\t').collect();
        match parts.first().copied().unwrap_or("") {
            "S" => {
                if let Some(s) = current.take() { out.push(s); }
                if parts.len() < 4 { return Err(format!("bad S row at line {}", line_no + 1)); }
                current = Some(Sentence { id: parts[1].parse().map_err(|_| format!("bad sentence id at line {}", line_no + 1))?, start: parts[2].parse().map_err(|_| format!("bad sentence start at line {}", line_no + 1))?, end: parts[3].parse().map_err(|_| format!("bad sentence end at line {}", line_no + 1))?, tokens: Vec::new() });
            }
            "T" => {
                if parts.len() < 10 { return Err(format!("bad T row at line {}", line_no + 1)); }
                let s = current.as_mut().ok_or_else(|| format!("T before S at line {}", line_no + 1))?;
                s.tokens.push(Token { ordinal: parts[1].parse().map_err(|_| format!("bad token ordinal at line {}", line_no + 1))?, start: parts[2].parse().map_err(|_| format!("bad token start at line {}", line_no + 1))?, end: parts[3].parse().map_err(|_| format!("bad token end at line {}", line_no + 1))?, head: parts[4].parse().map_err(|_| format!("bad head at line {}", line_no + 1))?, text: parts[5].to_string(), lemma: parts[6].to_lowercase(), pos: parts[7].to_string(), dep: parts[9].to_string() });
            }
            "E" => { if let Some(s) = current.take() { out.push(s); } }
            _ => {}
        }
    }
    if let Some(s) = current { out.push(s); }
    Ok(out)
}

fn parse_residuals(text: &str) -> BTreeMap<usize, usize> {
    let mut m = BTreeMap::new();
    for line in text.lines() {
        let p: Vec<&str> = line.split('\t').collect();
        if p.first() == Some(&"R") && p.len() >= 3 {
            if let (Ok(id), Ok(r)) = (p[1].parse::<usize>(), p[2].parse::<usize>()) { m.insert(id, r); }
        }
    }
    m
}

fn parse_profiles(text: &str) -> BTreeMap<String, Profile> {
    let mut out: BTreeMap<String, Profile> = BTreeMap::new();
    for line in text.lines() {
        let line = line.trim(); if line.is_empty() || line.starts_with('#') { continue; }
        let p: Vec<&str> = line.split('\t').collect(); if p.len() < 3 || p[0] == "speaker" { continue; }
        if let Ok(weight) = p[2].parse::<i32>() { out.entry(p[0].to_string()).or_default().weights.insert(p[1].to_lowercase(), weight); }
    }
    out
}

fn char_to_byte_map(s: &str) -> Vec<usize> { let mut map = s.char_indices().map(|(i, _)| i).collect::<Vec<_>>(); map.push(s.len()); map }
fn char_slice<'a>(s: &'a str, map: &[usize], a: usize, b: usize) -> &'a str { let a = a.min(map.len().saturating_sub(1)); let b = b.min(map.len().saturating_sub(1)); &s[map[a]..map[b]] }

fn crossing_counts(tokens: &[Token], split: usize, discourse_boundary: bool) -> (usize, usize) {
    let mut raw = 0usize; let mut content = 0usize;
    for t in tokens {
        if t.head == t.ordinal { continue; }
        if (t.ordinal < split) == (t.head < split) { continue; }
        raw += 1;
        let coordination_like = matches!(t.dep.as_str(), "cc" | "conj" | "punct");
        if !(discourse_boundary && coordination_like) { content += 1; }
    }
    (raw, content)
}

fn punctuation_strength(left: &Token, right: &Token) -> i32 {
    let l = left.text.as_str(); let r = right.text.as_str();
    if matches!(l, "." | "?" | "!" | ";" | ":") || matches!(r, "." | "?" | "!" | ";" | ":") { 3 }
    else if matches!(l, "," | "—" | "-" | "–") || matches!(r, "," | "—" | "-" | "–") { 1 } else { 0 }
}
fn is_discourse_marker(t: &Token) -> bool { matches!(t.lemma.as_str(), "but" | "however" | "well" | "yeah" | "yes" | "no" | "now" | "listen" | "so" | "although" | "yet") }

fn perspective_class(tokens: &[Token]) -> u8 {
    let mut seen = [0usize; 4];
    for t in tokens { match t.lemma.as_str() { "i" | "me" | "my" | "mine" => seen[0] += 1, "we" | "us" | "our" | "ours" => seen[1] += 1, "you" | "your" | "yours" => seen[2] += 1, "he" | "she" | "they" | "him" | "her" | "them" | "their" => seen[3] += 1, _ => {} } }
    seen.iter().enumerate().max_by_key(|(_, n)| *n).and_then(|(i, n)| if *n == 0 { None } else { Some((i + 1) as u8) }).unwrap_or(0)
}

fn lexical_features(tokens: &[Token]) -> HashSet<String> {
    let mut out = HashSet::new();
    for t in tokens { out.insert(t.lemma.clone()); out.insert(t.text.to_lowercase()); }
    for w in tokens.windows(3) {
        if w[1].text == "-" || w[1].text == "–" || w[1].text == "—" { out.insert(format!("{}-{}", w[0].lemma, w[2].lemma)); }
    }
    for n in 2..=3 {
        for w in tokens.windows(n) { out.insert(w.iter().map(|t| t.lemma.as_str()).collect::<Vec<_>>().join(" ")); }
    }
    out
}

fn profile_best(tokens: &[Token], profiles: &BTreeMap<String, Profile>) -> (String, i32) {
    if profiles.is_empty() { return (String::new(), 0); }
    let features = lexical_features(tokens);
    let mut best = (String::new(), i32::MIN);
    for (speaker, profile) in profiles {
        let score = profile.weights.iter().filter_map(|(k, w)| if features.contains(k) { Some(*w) } else { None }).sum::<i32>();
        if score > best.1 { best = (speaker.clone(), score); }
    }
    best
}

fn anchor(left: &Token, right: &Token) -> String { format!("{}|{}", left.text.replace('\t', " "), right.text.replace('\t', " ")) }

fn score_candidate(sentence: &Sentence, split: usize, source: &str, char_map: &[usize], residuals: usize, analyzer: &SentimentIntensityAnalyzer, profiles: &BTreeMap<String, Profile>) -> Candidate {
    let left_tokens = &sentence.tokens[..split]; let right_tokens = &sentence.tokens[split..];
    let left_end = left_tokens.last().map(|t| t.end).unwrap_or(sentence.start); let right_start = right_tokens.first().map(|t| t.start).unwrap_or(sentence.end);
    let left_text = char_slice(source, char_map, sentence.start, left_end).trim(); let right_text = char_slice(source, char_map, right_start, sentence.end).trim();
    let lv = analyzer.polarity_scores(left_text); let rv = analyzer.polarity_scores(right_text); let sentiment_delta = (lv.compound - rv.compound).abs();
    let punc = punctuation_strength(left_tokens.last().unwrap(), right_tokens.first().unwrap()); let marker = is_discourse_marker(right_tokens.first().unwrap());
    let lp = perspective_class(&left_tokens[left_tokens.len().saturating_sub(8)..]); let rp = perspective_class(&right_tokens[..right_tokens.len().min(8)]); let perspective_shift = lp != 0 && rp != 0 && lp != rp;
    let (left_profile, left_profile_score) = profile_best(left_tokens, profiles); let (right_profile, right_profile_score) = profile_best(right_tokens, profiles);
    let profile_shift = !left_profile.is_empty() && !right_profile.is_empty() && left_profile != right_profile && left_profile_score > 0 && right_profile_score > 0;
    let independent_boundary_cue = marker || perspective_shift || profile_shift || punc >= 2;
    let (dep_raw, dep_content) = crossing_counts(&sentence.tokens, split, independent_boundary_cue);

    // v2: sentiment is auxiliary and capped so rhetorical valence swings cannot dominate.
    let sentiment_contribution = if independent_boundary_cue { ((sentiment_delta * 4.0).round() as i32).min(4) } else { ((sentiment_delta * 2.0).round() as i32).min(2) };
    let mut cut_score = 0i32;
    cut_score += punc * 3;
    if marker { cut_score += 6; }
    if perspective_shift { cut_score += 5; }
    if profile_shift { cut_score += 6; }
    cut_score += sentiment_contribution;
    cut_score += match dep_content { 0 => 12, 1 => 8, 2 => 4, 3 => 1, _ => -(dep_content as i32 - 3) };

    // Residual density ranks sentences for inspection, but no longer changes cut ranking inside or across sentences.
    let residual_density_milli = residuals.saturating_mul(1000) / sentence.tokens.len().max(1);
    let inspection_priority = cut_score + ((residual_density_milli.min(500) / 100) as i32);

    Candidate { sentence_id: sentence.id, split, anchor: anchor(left_tokens.last().unwrap(), right_tokens.first().unwrap()), cut_score, inspection_priority, within_sentence_rank: 0, dep_crossings_raw: dep_raw, dep_crossings_content: dep_content, residuals, residual_density_milli, punctuation_strength: punc, discourse_marker: marker, perspective_shift, sentiment_delta, sentiment_contribution, left_compound: lv.compound, right_compound: rv.compound, left_profile, right_profile, left_profile_score, right_profile_score, profile_shift }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cfg = parse_args(); let parser_text = fs::read_to_string(&cfg.parser)?; let source = fs::read_to_string(&cfg.source)?;
    let sentences = parse_parser_tsv(&parser_text).map_err(|e| format!("parser.tsv: {e}"))?;
    let residuals = cfg.pnf.as_ref().map(|p| fs::read_to_string(p).map(|s| parse_residuals(&s))).transpose()?.unwrap_or_default();
    let profiles = cfg.profiles.as_ref().map(|p| fs::read_to_string(p).map(|s| parse_profiles(&s))).transpose()?.unwrap_or_default();
    let sha_receipt = cfg.source_sha.as_ref().map(fs::read_to_string).transpose()?.unwrap_or_else(|| "not-supplied".to_string()).trim().to_string();
    let char_map = char_to_byte_map(&source); let analyzer = SentimentIntensityAnalyzer::new();
    eprintln!("SLR_DISCOURSE_RECEIPT schema={} sentiment=vader_parity@0.1.0 parity=vaderSentiment@3.3.2 source_sha={} parser={} pnf={} profiles={} candidate_only=true residual_role=inspection_only sentiment_role=capped_auxiliary profile_tokenization=hyphen_normalized",
        SCHEMA, sha_receipt, cfg.parser.display(), cfg.pnf.as_ref().map(|p| p.display().to_string()).unwrap_or_else(|| "none".into()), cfg.profiles.as_ref().map(|p| p.display().to_string()).unwrap_or_else(|| "none".into()));

    let mut all = Vec::new();
    for s in &sentences {
        if let Some(focus) = &cfg.focus { if !focus.contains(&s.id) { continue; } }
        if s.tokens.len() < 4 { continue; }
        let r = *residuals.get(&s.id).unwrap_or(&0);
        let mut local = Vec::new();
        for split in 2..s.tokens.len().saturating_sub(1) { local.push(score_candidate(s, split, &source, &char_map, r, &analyzer, &profiles)); }
        local.sort_by(|a, b| b.cut_score.cmp(&a.cut_score).then_with(|| a.split.cmp(&b.split)));
        for (rank, mut c) in local.into_iter().enumerate() { c.within_sentence_rank = rank + 1; all.push(c); }
    }
    all.sort_by(|a, b| b.cut_score.cmp(&a.cut_score).then_with(|| b.inspection_priority.cmp(&a.inspection_priority)).then_with(|| a.sentence_id.cmp(&b.sentence_id)).then_with(|| a.split.cmp(&b.split)));

    println!("schema\tsentence\twithin_sentence_rank\tsplit\tanchor\tcut_score\tinspection_priority\tdep_crossings_raw\tdep_crossings_content\tresiduals\tresidual_density_milli\tpunctuation\tdiscourse_marker\tperspective_shift\tsentiment_delta\tsentiment_contribution\tleft_compound\tright_compound\tleft_profile\tleft_profile_score\tright_profile\tright_profile_score\tprofile_shift\tcandidate_only");
    for c in all.into_iter().take(cfg.top) {
        println!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.4}\t{}\t{:.4}\t{:.4}\t{}\t{}\t{}\t{}\t{}\ttrue",
            SCHEMA, c.sentence_id, c.within_sentence_rank, c.split, c.anchor, c.cut_score, c.inspection_priority, c.dep_crossings_raw, c.dep_crossings_content, c.residuals, c.residual_density_milli, c.punctuation_strength, c.discourse_marker, c.perspective_shift, c.sentiment_delta, c.sentiment_contribution, c.left_compound, c.right_compound, c.left_profile, c.left_profile_score, c.right_profile, c.right_profile_score, c.profile_shift);
    }
    Ok(())
}
