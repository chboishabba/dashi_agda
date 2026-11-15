#!/usr/bin/env python3
"""Primary pigeon macrophage RNA-seq discovery and optional MD5-verified FASTQ.

Lisowski et al. 2026 Science DOI 10.1126/science.ady2486, ENA PRJEB98986.
Uses ENA original official /ena/portal/api/filereport?accession=...&result=read_run.
A registered BioProject is NOT itself a gene count matrix. FASTQ acquisition
does NOT identify gene expression without pinned reference/transcriptome,
barcode/cell metadata, quantification and quality-control receipt.

Default: fetch *metadata only*. --download-reads must be explicitly selected,
with a constrained size budget (default 1 GiB). ENA-supplied MD5 must match;
a SHA256 is then pinned as independent local integrity evidence.
"""
import argparse, csv, hashlib, io, json
from pathlib import Path
from urllib.parse import urlencode, urlparse
from urllib.request import urlopen,Request

PROJECT="PRJEB98986"
DOI="10.1126/science.ady2486"
BASE="https://www.ebi.ac.uk/ena/portal/api/filereport"
FIELDS="run_accession,experiment_accession,sample_accession,fastq_ftp,fastq_md5,fastq_bytes"


def raw_metadata(url=BASE):
    params={"accession":PROJECT,"result":"read_run","fields":FIELDS,"format":"tsv"}
    with urlopen(url+"?"+urlencode(params),timeout=40) as response:
        raw=response.read(5*1024*1024+1)
    if len(raw)>5*1024*1024:raise ValueError("Oversize ENA run manifest")
    text=raw.decode("utf-8-sig")
    if "run_accession" not in text.splitlines()[0]:
        raise ValueError("ENA did not return valid run accession rows")
    rows=list(csv.DictReader(io.StringIO(text),delimiter="\t"))
    if not rows:raise RuntimeError("ENA project currently has no open raw runs")
    return raw,rows


def planned_files(rows):
    entries=[]
    for row in rows:
        uris=row.get("fastq_ftp","").split(";") if row.get("fastq_ftp") else []
        hashes=row.get("fastq_md5","").split(";") if row.get("fastq_md5") else []
        bytes_=row.get("fastq_bytes","").split(";") if row.get("fastq_bytes") else []
        if not uris or len(uris)!=len(hashes) or len(uris)!=len(bytes_):
            raise ValueError("ENA missing matching FASTQ URL/MD5/size: "+row["run_accession"])
        for path,md5,size in zip(uris,hashes,bytes_):
            url=path if path.startswith("https://") else "https://"+path
            parsed=urlparse(url)
            if parsed.scheme!="https" or parsed.hostname not in (
                    "ftp.sra.ebi.ac.uk","www.ebi.ac.uk","era-fasp@fasp.sra.ebi.ac.uk"):
                raise ValueError("Unexpected ENA FASTQ hostname: "+url)
            if len(md5)!=32 or any(ch not in "0123456789abcdef" for ch in md5.lower()):
                raise ValueError("Invalid ENA MD5")
            entries.append({"run":row["run_accession"],
                            "experiment":row.get("experiment_accession",""),
                            "sample":row.get("sample_accession",""),
                            "url":url,"expected_md5":md5.lower(),
                            "expected_bytes":int(size)})
    if len({z["url"] for z in entries})!=len(entries):
        raise ValueError("Duplicate ENA read file metadata")
    return entries


def download_verified(files,directory,max_bytes):
    total=sum(x["expected_bytes"] for x in files)
    if total>max_bytes:raise ValueError(
        f"ENA declared {total} bytes > budget {max_bytes}; raise explicitly")
    directory=Path(directory)
    directory.mkdir(parents=True,exist_ok=True)
    records=[]
    for item in files:
        name=item["url"].rsplit("/",1)[-1]
        if not name.endswith((".fastq.gz",".fq.gz")):
            raise ValueError("Not an expected compressed FASTQ file: "+name)
        path=directory/name
        partial=directory/(name+".part")
        md5=hashlib.md5()
        sha=hashlib.sha256()
        count=0
        with urlopen(Request(item["url"],headers={"User-Agent":"DASHI-KSW668/1.0"}),
                     timeout=120) as response, partial.open("wb") as sink:
            for block in iter(lambda:response.read(1024*1024),b""):
                count+=len(block)
                if count>item["expected_bytes"] or count>max_bytes:
                    raise ValueError("File exceeds declared expected size")
                md5.update(block);sha.update(block);sink.write(block)
        if count!=item["expected_bytes"] or md5.hexdigest()!=item["expected_md5"]:
            partial.unlink(missing_ok=True)
            raise ValueError("ENA original FASTQ size/MD5 mismatch: "+name)
        partial.replace(path)
        records.append(dict(item,local_path=str(path),sha256=sha.hexdigest(),
                            verified_size=count,ena_md5_verified=True))
    return records


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--execute",action="store_true",
                    help="Fetch the ENA accession metadata")
    ap.add_argument("--download-reads",action="store_true")
    ap.add_argument("--max-gib",type=float,default=1.0)
    ap.add_argument("--output-dir",default="data/ena_PRJEB98986")
    ap.add_argument("--receipt",type=Path)
    args=ap.parse_args()
    if args.download_reads and not args.execute:
        ap.error("--download-reads requires --execute")
    if not args.execute:
        print(json.dumps({"status":"plan-only; metadata and FASTQ not retrieved",
                          "accession":PROJECT,
                          "api":BASE,
                          "request_fields":FIELDS,
                          "raw_count_matrix":"unavailable until independently sourced or reconstructed"},indent=2))
        return
    raw,rows=raw_metadata()
    files=planned_files(rows)
    receipt={
        "schema":"dashi.ksw668.ena-primary-v1",
        "source_doI":DOI,
        "study_accession":PROJECT,
        "run_count":len(rows),
        "ena_file_report_sha256":hashlib.sha256(raw).hexdigest(),
        "ena_report_raw_rows":rows,
        "files_expected":files,
        "fastq_downloaded":False,
        "counts_matrices_acquired":False,
        "unresolved":"pinned reference genome, exact read processing, quantification and cell metadata",
    }
    if args.download_reads:
        if args.max_gib<=0:raise ValueError("Invalid requested budget")
        receipt["files_verified"]=download_verified(
            files,args.output_dir,int(args.max_gib*1024**3))
        receipt["fastq_downloaded"]=True
    output=json.dumps(receipt,indent=2)+"\n"
    if args.receipt:args.receipt.write_text(output)
    print(output)


if __name__=="__main__":
    main()
