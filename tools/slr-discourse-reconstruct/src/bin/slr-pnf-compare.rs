use std::env;
use std::fs;
use std::path::PathBuf;

const SCHEMA: &str = "slr-pnf-comparison-v1";

#[derive(Clone, Debug)]
struct Config { raw: PathBuf, reconstructed: PathBuf }
#[derive(Clone, Debug, Default)]
struct Summary { lines: usize, sentence_rows: usize, residual_rows: usize, residual_total: usize, candidate_rows: usize, symbol_rows: usize }

fn usage() -> ! {
    eprintln!("usage: slr-pnf-compare --raw-pnf raw/pnf.stdout --reconstructed-pnf reconstructed/pnf.stdout");
    std::process::exit(2)
}
fn args() -> Config {
    let a: Vec<String> = env::args().skip(1).collect();
    let (mut raw, mut reconstructed) = (None,None); let mut i=0;
    while i<a.len() { match a[i].as_str() {
        "--raw-pnf" => {i+=1; raw=a.get(i).map(PathBuf::from)},
        "--reconstructed-pnf" => {i+=1; reconstructed=a.get(i).map(PathBuf::from)},
        _ => usage(),
    } i+=1; }
    Config { raw:raw.unwrap_or_else(||usage()), reconstructed:reconstructed.unwrap_or_else(||usage()) }
}
fn summarize(text:&str)->Summary {
    let mut s=Summary::default();
    for line in text.lines() {
        if line.trim().is_empty(){continue}
        s.lines+=1;
        let p:Vec<&str>=line.split('\t').collect();
        match p.first().copied().unwrap_or("") {
            "S" => s.sentence_rows+=1,
            "R" => { s.residual_rows+=1; if p.len()>=3 { s.residual_total+=p[2].parse::<usize>().unwrap_or(0); } },
            "C" => s.candidate_rows+=1,
            "Y" | "A" | "F" => s.symbol_rows+=1,
            _ => {}
        }
    }
    s
}
fn ratio_milli(n:usize,d:usize)->usize { if d==0 {0} else {n.saturating_mul(1000)/d} }
fn signed_delta(a:usize,b:usize)->i64 { b as i64 - a as i64 }

fn main()->Result<(),Box<dyn std::error::Error>> {
    let cfg=args();
    let raw=summarize(&fs::read_to_string(&cfg.raw)?);
    let rec=summarize(&fs::read_to_string(&cfg.reconstructed)?);
    let raw_density=ratio_milli(raw.residual_total,raw.residual_rows.max(raw.sentence_rows).max(1));
    let rec_density=ratio_milli(rec.residual_total,rec.residual_rows.max(rec.sentence_rows).max(1));
    eprintln!("SLR_PNF_COMPARISON_RECEIPT schema={} raw={} reconstructed={} semantic_promotion=false comparison_only=true",SCHEMA,cfg.raw.display(),cfg.reconstructed.display());
    println!("schema\trun\tlines\tsentence_rows\tresidual_rows\tresidual_total\tresidual_density_milli\tcandidate_rows\tsymbol_rows");
    println!("{}\traw\t{}\t{}\t{}\t{}\t{}\t{}\t{}",SCHEMA,raw.lines,raw.sentence_rows,raw.residual_rows,raw.residual_total,raw_density,raw.candidate_rows,raw.symbol_rows);
    println!("{}\treconstructed\t{}\t{}\t{}\t{}\t{}\t{}\t{}",SCHEMA,rec.lines,rec.sentence_rows,rec.residual_rows,rec.residual_total,rec_density,rec.candidate_rows,rec.symbol_rows);
    println!("{}\tdelta\t{}\t{}\t{}\t{}\t{}\t{}\t{}",SCHEMA,signed_delta(raw.lines,rec.lines),signed_delta(raw.sentence_rows,rec.sentence_rows),signed_delta(raw.residual_rows,rec.residual_rows),signed_delta(raw.residual_total,rec.residual_total),rec_density as i64-raw_density as i64,signed_delta(raw.candidate_rows,rec.candidate_rows),signed_delta(raw.symbol_rows,rec.symbol_rows));
    Ok(())
}
