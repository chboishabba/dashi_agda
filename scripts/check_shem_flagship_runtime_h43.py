#!/usr/bin/env python3
"""Torah application adapter for the unchanged DASHI flagship runtime.

Run from repository root. Actual binary serialization, including stream counts,
lengths, chapter metadata, flags, and tails; exact roundtrip required.
This is descriptive whole-corpus compression, not independent prediction.
"""
import argparse
import json
import struct
import zlib
from itertools import product
from pathlib import Path
import run_triadic_flagship_benchmark as F

BASE = Path("Docs/support/reference/TorahCryptoCorpus20261125")
NAMES = ("genesis", "exodus", "leviticus", "numbers", "deuteronomy")
GLYPHS = "אבגדהוזחטיכלמנסעפצקרשתךםןףץ"
ENC = {g: (i//9, (i//9+i%3)%3, (i//9+i%9//3)%3) for i,g in enumerate(GLYPHS)}
DEC = {v:k for k,v in ENC.items()}

def pack_u32(x):
    return struct.pack("<I", x)

def blob(x):
    return pack_u32(len(x))+x

class Reader:
    def __init__(self, data):
        self.data, self.pos = data, 0
    def take(self, n):
        v = self.data[self.pos:self.pos+n]
        if len(v)!=n: raise ValueError("short stream")
        self.pos += n
        return v
    def uint(self):
        return struct.unpack("<I",self.take(4))[0]
    def blob(self):
        return self.take(self.uint())
    def done(self):
        if self.pos != len(self.data): raise ValueError("trailing data")

def pack_stream(s):
    return pack_u32(s.symbol_count)+pack_u32(len(s.bucket_lengths))+b"".join(
        pack_u32(n)+pack_u32(a)+blob(m)+blob(g)
        for n,(m,g,a) in zip(s.bucket_lengths,s.bucket_blobs,strict=True))
def unpack_stream(r):
    n,k=r.uint(),r.uint()
    sizes,blobs=[],[]
    for _ in range(k):
        length,active=r.uint(),r.uint()
        sizes.append(length)
        blobs.append((r.blob(),r.blob(),active))
    return F.EncodedStream(n,sizes,blobs)

def pack_candidate(p):
    mask=sum(int(getattr(p.options,name))<<i for i,name in enumerate(F.FEATURES))
    return (bytes([mask])+pack_u32(p.frame_count)+pack_u32(p.frame_size)
            +pack_stream(p.residual)
            +(pack_stream(p.coarse) if p.coarse is not None else b"")
            +pack_u32(p.symmetry_flag_count)+blob(p.symmetry_flags))
def unpack_candidate(data):
    r=Reader(data)
    mask=r.take(1)[0]
    if mask>=16: raise ValueError("invalid mode")
    o=F.Options(**{name:bool(mask>>i&1) for i,name in enumerate(F.FEATURES)})
    n,w=r.uint(),r.uint()
    residual=unpack_stream(r)
    coarse=unpack_stream(r) if o.multiscale_prediction else None
    count=r.uint()
    flags=r.blob()
    r.done()
    return F.CandidatePayload(n,w,o,coarse,residual,flags,count)

def flatten(glyphs):
    return [x for g in glyphs for x in ENC[g]]
def glyphs(trits):
    if len(trits)%3: raise ValueError("glyph width")
    return "".join(DEC[tuple(trits[i:i+3])] for i in range(0,len(trits),3))
def weave(s):
    return "".join(s[j]+s[143-j]+s[144+j] for j in range(72))
def unweave(s):
    return s[::3]+s[1::3][::-1]+s[2::3]

def run(chapters, orientation, options):
    frames,tails=[],[]
    for _,_,s in chapters:
        for j in range(0,len(s)//216*216,216):
            w=s[j:j+216]
            frames.append(flatten(weave(w) if orientation else w))
        tails.append(s[len(s)//216*216:])
    meta=pack_u32(len(chapters))+b"".join(struct.pack("<BBI",b,c,len(s)) for b,c,s in chapters)
    tail=zlib.compress(bytes(GLYPHS.index(g) for g in "".join(tails)),9)
    raw=pack_candidate(F.encode_candidate(frames,options))
    stream=bytes([int(orientation)])+meta+blob(tail)+blob(raw)
    r=Reader(stream)
    direction=r.take(1)[0]
    rows=[struct.unpack("<BBI",r.take(6)) for _ in range(r.uint())]
    tailstr="".join(GLYPHS[i] for i in zlib.decompress(r.blob()))
    decoded=F.decode_candidate(unpack_candidate(r.blob()))
    r.done()
    out=[];i=j=0
    for b,c,n in rows:
        words=[]
        for _ in range(n//216):
            s=glyphs(decoded[i]); i+=1
            words.append(unweave(s) if direction else s)
        words.append(tailstr[j:j+n%216]);j+=n%216
        out.append((b,c,"".join(words)))
    assert out==chapters and i==len(decoded) and j==len(tailstr)
    return {"orientation":"FRF" if orientation else "physical",
            "options":vars(options),"bytes":len(stream),"verified":sum(len(s) for _,_,s in out)}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    chapters=[]
    for b,name in enumerate(NAMES):
        data=json.loads((BASE/(name+".normalized.json")).read_text())
        chapters.extend((b,c["c"],"".join(v["letters"] for v in c["verses"])) for c in data["chapters"])
    assert sum(len(s) for _,_,s in chapters)==304850
    meta=pack_u32(len(chapters))+b"".join(struct.pack("<BBI",b,c,len(s)) for b,c,s in chapters)
    direct=meta+blob(zlib.compress(bytes(GLYPHS.index(g) for _,_,s in chapters for g in s),9))
    r=Reader(direct)
    rows=[struct.unpack("<BBI",r.take(6)) for _ in range(r.uint())]
    decoded="".join(GLYPHS[i] for i in zlib.decompress(r.blob()))
    r.done()
    off=0; out=[]
    for b,c,n in rows:
        out.append((b,c,decoded[off:off+n]));off+=n
    assert out==chapters and off==len(decoded)
    results=[]
    for orientation in (False,True):
        for flags in product((False,True),repeat=4):
            results.append(run(chapters,orientation,F.Options(**dict(zip(F.FEATURES,flags)))))
    ex={c:s for b,c,s in chapters if b==1}
    pre,truth=ex[14][1728:],ex[15][:91]
    assert len(pre)==125 and len(truth)==91
    # Exact target-derived patch, with preceding 91 glyphs as producer.
    p,t=flatten(pre[-91:]),flatten(truth)
    residual=[(x-y)%3 for x,y in zip(t,p,strict=True)]
    packed=pack_stream(F.encode_stream(residual,True))
    r=Reader(packed); z=F.decode_stream(unpack_stream(r),True);r.done()
    assert glyphs([(x+y)%3 for x,y in zip(z,p,strict=True)])==truth
    receipt={"direct_zlib_bytes":len(direct),"variants":results,
             "patch":{"exact":91,"bytes":len(packed)},
             "scope":"actual flagship Python zlib backend; synthetic frame time, normalized glyphs by chapter, known shared chart; descriptive lossless encoding, target-derived patch not blind prediction"}
    args.output.write_text(json.dumps(receipt,indent=2)+"\n")
if __name__=="__main__":
    main()
