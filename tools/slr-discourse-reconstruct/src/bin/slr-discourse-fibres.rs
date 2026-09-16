use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::PathBuf;

const SCHEMA: &str = "slr-discourse-fibre-v1";

#[derive(Clone, Debug)]
struct Token {
    ordinal: usize,
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
struct CutRow {
    sentence: usize,
    within_rank: usize,
    split: usize,
    anchor: String,
    cut_score: i32,
    dep_content: usize,
    punctuation: i32,
    discourse_marker: bool,
    perspective_shift: bool,
    sentiment_delta: f64,
    left_profile: String,
    left_profile_score: i32,
    right_profile: String,
    right_profile_score: i32,
    profile_shift: bool,
}

#[derive(Clone, Debug)]
struct Config {
    cuts: PathBuf,
    parser: PathBuf,
    source: PathBuf,
    top: usize,
    max_rank: usize,
}

fn usage() -> ! {
    eprintln!("usage: slr-discourse-fibres --cuts discourse-cuts.tsv --parser parser.tsv --source source.txt [--top 500] [--max-rank 3]");
    std::process::exit(2);
}

fn parse_args() -> Config {
    let args: Vec<String> = env::args().skip(1).collect();
    let mut cuts = None;
    let mut parser = None;
    let mut source = None;
    let mut top = 500usize;
    let mut max_rank = 3usize;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--cuts" => { i += 1; cuts = args.get(i).map(PathBuf::from); }
            "--parser" => { i += 1; parser = args.get(i).map(PathBuf::from); }
            "--source" => { i += 1; source = args.get(i).map(PathBuf::from); }
            "--top" => { i += 1; top = args.get(i).and_then(|s| s.parse().ok()).unwrap_or(500); }
            "--max-rank" => { i += 1; max_rank = args.get(i).and_then(|s| s.parse().ok()).unwrap_or(3); }
            _ => usage(),
        }
        i += 1;
    }
    Config {
        cuts: cuts.unwrap_or_else(|| usage()),
        parser: parser.unwrap_or_else(|| usage()),
        source: source.unwrap_or_else(|| usage()),
        top,
        max_rank,
    }
}

fn parse_parser(text: &str) -> Result<HashMap<usize, Sentence>, String> {
    let mut map = HashMap::new();
    let mut current: Option<Sentence> = None;
    for (line_no, line) in text.lines().enumerate() {
        let p: Vec<&str> = line.split('\t').collect();
        match p.first().copied().unwrap_or("") {
            "S" => {
                if let Some(s) = current.take() { map.insert(s.id, s); }
                if p.len() < 4 { return Err(format!("bad S row at line {}", line_no + 1)); }
                current = Some(Sentence {
                    id: p[1].parse().map_err(|_| format!("bad sentence id line {}", line_no + 1))?,
                    start: p[2].parse().map_err(|_| format!("bad sentence start line {}", line_no + 1))?,
                    end: p[3].parse().map_err(|_| format!("bad sentence end line {}", line_no + 1))?,
                    tokens: Vec::new(),
                });
            }
            "T" => {
                if p.len() < 10 { return Err(format!("bad T row at line {}", line_no + 1)); }
                let s = current.as_mut().ok_or_else(|| format!("T before S line {}", line_no + 1))?;
                s.tokens.push(Token {
                    ordinal: p[1].parse().map_err(|_| format!("bad ordinal line {}", line_no + 1))?,
                    start: p[2].parse().map_err(|_| format!("bad token start line {}", line_no + 1))?,
                    end: p[3].parse().map_err(|_| format!("bad token end line {}", line_no + 1))?,
                    text: p[5].to_string(),
                    lemma: p[6].to_lowercase(),
                    dep: p[9].to_string(),
                });
            }
            "E" => if let Some(s) = current.take() { map.insert(s.id, s); },
            _ => {}
        }
    }
    if let Some(s) = current { map.insert(s.id, s); }
    Ok(map)
}

fn parse_bool(s: &str) -> bool { matches!(s, "true" | "True" | "1") }

fn parse_cuts(text: &str) -> Result<Vec<CutRow>, String> {
    let mut lines = text.lines();
    let header = lines.next().ok_or("empty cut TSV")?;
    let cols: Vec<&str> = header.split('\t').collect();
    let idx = |name: &str| cols.iter().position(|x| *x == name).ok_or_else(|| format!("missing column {name}"));
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
    for (line_no, line) in lines.enumerate() {
        let p: Vec<&str> = line.split('\t').collect();
        if p.len() < cols.len() { continue; }
        let parse_usize = |i: usize| p[i].parse::<usize>().map_err(|_| format!("bad usize line {} col {}", line_no + 2, cols[i]));
        let parse_i32 = |i: usize| p[i].parse::<i32>().map_err(|_| format!("bad i32 line {} col {}", line_no + 2, cols[i]));
        let parse_f64 = |i: usize| p[i].parse::<f64>().map_err(|_| format!("bad f64 line {} col {}", line_no + 2, cols[i]));
        out.push(CutRow {
            sentence: parse_usize(i_sentence)?,
            within_rank: parse_usize(i_rank)?,
            split: parse_usize(i_split)?,
            anchor: p[i_anchor].to_string(),
            cut_score: parse_i32(i_cut)?,
            dep_content: parse_usize(i_dep)?,
            punctuation: parse_i32(i_punc)?,
            discourse_marker: parse_bool(p[i_dm]),
            perspective_shift: parse_bool(p[i_ps]),
            sentiment_delta: parse_f64(i_sd)?,
            left_profile: p[i_lp].to_string(),
            left_profile_score: parse_i32(i_lps)?,
            right_profile: p[i_rp].to_string(),
            right_profile_score: parse_i32(i_rps)?,
            profile_shift: parse_bool(p[i_prof]),
        });
    }
    Ok(out)
}

fn char_to_byte_map(s: &str) -> Vec<usize> {
    let mut map = s.char_indices().map(|(i, _)| i).collect::<Vec<_>>();
    map.push(s.len());
    map
}

fn char_slice<'a>(s: &'a str, map: &[usize], a: usize, b: usize) -> &'a str {
    let a = a.min(map.len().saturating_sub(1));
    let b = b.min(map.len().saturating_sub(1));
    &s[map[a]..map[b]]
}

fn contains_any(text: &str, terms: &[&str]) -> bool {
    let t = text.to_lowercase();
    terms.iter().any(|x| t.contains(x))
}

fn repeated_adjacent(tokens: &[Token]) -> bool {
    tokens.windows(2).any(|w| w[0].lemma == w[1].lemma && w[0].lemma.chars().any(|c| c.is_alphabetic()))
        || tokens.windows(4).any(|w| w[0].lemma == w[2].lemma && w[1].lemma == w[3].lemma)
}

fn fibre_scores(c: &CutRow, s: &Sentence, source: &str, cmap: &[usize]) -> (i32, i32, i32, i32, i32, String) {
    let split = c.split.min(s.tokens.len());
    let left = &s.tokens[..split];
    let right = &s.tokens[split..];
    let left_end = left.last().map(|t| t.end).unwrap_or(s.start);
    let right_start = right.first().map(|t| t.start).unwrap_or(s.end);
    let left_text = char_slice(source, cmap, s.start, left_end).trim();
    let right_text = char_slice(source, cmap, right_start, s.end).trim();
    let whole_text = char_slice(source, cmap, s.start, s.end).trim();

    let attribution = contains_any(whole_text, &["according to", "said ", "says ", "told ", "concluded", "reported", "argues", "argued", "believes", "announced", "declared", "asked", "replied"]);
    let quote_like = attribution && (c.perspective_shift || contains_any(right_text, &[" i ", " we ", " i'm ", " we're ", " our "]));
    let adversative = c.discourse_marker && contains_any(right_text, &["but", "however", "although", "yet", "well"]);
    let stable_profile = !c.left_profile.is_empty() && c.left_profile == c.right_profile && c.left_profile_score > 0 && c.right_profile_score > 0;
    let strong_profile_shift = c.profile_shift && c.left_profile_score > 0 && c.right_profile_score > 0;
    let asr_repeat = repeated_adjacent(&s.tokens) || contains_any(whole_text, &["we give we give", "we have, we have", "i'd been i've been", "to prevent the to prevent"]);
    let fragment_like = c.dep_content >= 5 && c.punctuation == 0 && !c.discourse_marker;

    let mut speaker = 0;
    if strong_profile_shift { speaker += 8; }
    if c.perspective_shift { speaker += 4; }
    if c.discourse_marker { speaker += 2; }
    speaker += match c.dep_content { 0 => 5, 1 => 4, 2 => 2, _ => 0 };
    if quote_like { speaker -= 2; }
    if stable_profile { speaker -= 5; }

    let mut quote = 0;
    if attribution { quote += 7; }
    if quote_like { quote += 6; }
    if c.perspective_shift { quote += 3; }
    if strong_profile_shift { quote += 2; }
    if c.punctuation > 0 { quote += 1; }

    let mut nesting = 0;
    if attribution { nesting += 9; }
    if contains_any(whole_text, &["according to", "concluded", "believes", "reported", "as we understand", "the reason that"]) { nesting += 5; }
    if c.perspective_shift { nesting += 1; }
    if strong_profile_shift { nesting -= 3; }

    let mut asr = 0;
    if asr_repeat { asr += 10; }
    if fragment_like { asr += 5; }
    if c.dep_content >= 5 { asr += 2; }
    if contains_any(whole_text, &["miller band", "miliband", "jacobreber", "citations assistance"]) { asr += 4; }

    let mut rhetorical = 0;
    if adversative { rhetorical += 10; }
    if stable_profile { rhetorical += 6; }
    if c.sentiment_delta >= 0.5 { rhetorical += 3; }
    if c.dep_content <= 1 { rhetorical += 2; }
    if strong_profile_shift { rhetorical -= 5; }
    if attribution { rhetorical -= 2; }

    let mut top = [("speaker", speaker), ("quote", quote), ("nesting", nesting), ("asr", asr), ("rhetorical", rhetorical)];
    top.sort_by(|a, b| b.1.cmp(&a.1));
    (speaker, quote, nesting, asr, rhetorical, top[0].0.to_string())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cfg = parse_args();
    let source = fs::read_to_string(&cfg.source)?;
    let parser = parse_parser(&fs::read_to_string(&cfg.parser)?).map_err(|e| format!("parser: {e}"))?;
    let cuts = parse_cuts(&fs::read_to_string(&cfg.cuts)?).map_err(|e| format!("cuts: {e}"))?;
    let cmap = char_to_byte_map(&source);
    eprintln!("SLR_DISCOURSE_FIBRE_RECEIPT schema={} source={} parser={} cuts={} candidate_only=true scorer_feedback=false", SCHEMA, cfg.source.display(), cfg.parser.display(), cfg.cuts.display());
    println!("schema\tsentence\twithin_sentence_rank\tsplit\tanchor\tcut_score\tspeaker_score\tquote_score\tnesting_score\tasr_score\trhetorical_score\ttop_fibre\tcandidate_only");
    let mut emitted = 0usize;
    for c in cuts.iter().filter(|c| c.within_rank <= cfg.max_rank) {
        let Some(s) = parser.get(&c.sentence) else { continue; };
        let (speaker, quote, nesting, asr, rhetorical, top) = fibre_scores(c, s, &source, &cmap);
        println!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\ttrue", SCHEMA, c.sentence, c.within_rank, c.split, c.anchor, c.cut_score, speaker, quote, nesting, asr, rhetorical, top);
        emitted += 1;
        if emitted >= cfg.top { break; }
    }
    Ok(())
}
