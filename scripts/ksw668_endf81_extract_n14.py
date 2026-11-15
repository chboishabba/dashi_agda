#!/usr/bin/env python3
"""C2 original ENDF/B-VIII.1 N14 MT103 source-from-archive verification.

The user supplies the original NNDC ENDF neutron archive downloaded from
the official release DOI 10.11578/endf/2571019.
Two SHA-256 and byte-size witnesses are from an independently existing
AvilaLabs/OpenBNCT acquisition receipt. Actual archive/member bytes
have NOT been retrieved in this authoring environment.
"""
import argparse,hashlib,json,tarfile
from pathlib import Path
ARCHIVE_SHA="decff90016bfb5c25c8d4c7fb8d81f94ff2f104853165f0fe6a21bf61c4164e4"
ARCHIVE_BYTES=343724780
ORIGINAL_MEMBER="neutrons-version.VIII.1/n-007_N_014.endf"
MEMBER_SHA="fd5c0c0beccefbcd0b57c49bcdf835449d2014e3740830377ce24760478c06d8"
MEMBER_BYTES=1253924

def sha_file(path):
    h=hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda:f.read(1048576),b""):h.update(block)
    return h.hexdigest()

def extract(archive,output):
    archive=Path(archive)
    if archive.stat().st_size!=ARCHIVE_BYTES or sha_file(archive)!=ARCHIVE_SHA:
        raise ValueError("Original NNDC ENDF neutron archive SHA256/size mismatch")
    with tarfile.open(archive,"r:gz") as tar:
        entry=tar.getmember(ORIGINAL_MEMBER)
        if not entry.isfile() or entry.size!=MEMBER_BYTES:
            raise ValueError("N14 original member path or size mismatch")
        with tar.extractfile(entry) as inp:
            if inp is None:raise ValueError("No member stream")
            raw=inp.read(MEMBER_BYTES+1)
    if len(raw)!=MEMBER_BYTES or hashlib.sha256(raw).hexdigest()!=MEMBER_SHA:
        raise ValueError("Unverified original ENDF N14 file")
    output=Path(output);output.parent.mkdir(parents=True,exist_ok=True)
    output.write_bytes(raw)
    return {"status":"PASS, exact original bytes source-hashed",
            "source_release":"ENDF/B-VIII.1",
            "source_DOI":"10.11578/endf/2571019",
            "archive_sha256":ARCHIVE_SHA,"archive_size":ARCHIVE_BYTES,
            "member_path":ORIGINAL_MEMBER,"member_sha256":MEMBER_SHA,
            "member_size":MEMBER_BYTES,"output":str(output),
            "physical_rate_established":False}
if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--archive",type=Path,required=True)
    p.add_argument("--out",type=Path,required=True)
    args=p.parse_args()
    print(json.dumps(extract(args.archive,args.out),indent=2))
