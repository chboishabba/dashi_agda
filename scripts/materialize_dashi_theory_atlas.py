#!/usr/bin/env python3
"""Generate a source-aware DASHI theory atlas downstream of Agda proofs."""
from __future__ import annotations
import argparse, datetime as dt, html, json, re
from dataclasses import dataclass, field
from pathlib import Path

SCHEMA="dashi-theory-atlas-v1"
IDENT=r"[^\W\d][\w′″₀-₉-]*"
SIG=re.compile(rf"^(?P<n>{IDENT})\s*:\s*(?P<t>.*)$")
MOD=re.compile(r"^\s*module\s+([\w.]+)\s+where")
IMP=re.compile(r"^\s*(?:open\s+)?import\s+([\w.]+)")
TOK=re.compile(IDENT)
LABEL={"proved":"proved","proved_conditional":"proved conditional on named inputs","source_imported":"source-imported","open_analytic":"OPEN ANALYTIC INPUT","legacy":"legacy/non-critical"}
COLOUR={"proved":("#153c2f","#4ade80"),"proved_conditional":("#123b4a","#22d3ee"),"source_imported":("#4a3510","#fbbf24"),"open_analytic":("#3f1717","#f87171"),"legacy":("#27272a","#a1a1aa")}

class AtlasError(RuntimeError): pass
@dataclass
class Decl:
    module:str; name:str; path:Path; line:int; signature:str; body:str; imports:list[str]; postulated:bool=False
    @property
    def fq(self): return f"{self.module}.{self.name}"
    @property
    def tokens(self): return set(TOK.findall(self.signature+"\n"+self.body))
@dataclass
class Card:
    id:str; decl:Decl; title:str; formula:str; lane:str; critical:bool; anchors:list[str]; relation:str; explicit:list[str]
    state:str="proved"; deps:list[str]=field(default_factory=list); open_inputs:list[str]=field(default_factory=list)

def clean(s): return s.split("--",1)[0].rstrip()
def parse(path:Path):
    lines=path.read_text(encoding="utf-8").splitlines(); module=next((m.group(1) for x in lines if (m:=MOD.match(x))),None)
    if not module:return []
    imports=[m.group(1) for x in lines if (m:=IMP.match(x))]; out=[]; post=None; i=0
    while i<len(lines):
        raw=lines[i]; s=clean(raw); z=s.strip(); ind=len(raw)-len(raw.lstrip())
        if z in {"postulate","primitive"}: post=ind; i+=1; continue
        if post is not None and z and ind<=post: post=None
        m=SIG.match(z) if ind==0 or post is not None else None
        if not m or m.group("n") in {"module","open","import","record","data","field"}: i+=1; continue
        name=m.group("n"); start=i; parts=[m.group("t")]; i+=1
        while i<len(lines):
            raw2=lines[i]; z2=clean(raw2).strip(); ind2=len(raw2)-len(raw2.lstrip())
            if not z2:i+=1;continue
            if post is not None:
                if ind2<=post and SIG.match(z2):break
                parts.append(z2);i+=1;continue
            if ind2==0 and (SIG.match(z2) or re.match(rf"^{re.escape(name)}(?:\s|\(|\{{|$)",z2)):break
            parts.append(z2);i+=1
        body=[]
        if post is None and i<len(lines) and re.match(rf"^{re.escape(name)}(?:\s|\(|\{{|$)",clean(lines[i]).strip()):
            while i<len(lines):
                raw2=lines[i]; z2=clean(raw2).strip(); ind2=len(raw2)-len(raw2.lstrip())
                if z2 and ind2==0 and SIG.match(z2):break
                if z2:body.append(z2)
                i+=1
        out.append(Decl(module,name,path,start+1," ".join(parts),"\n".join(body),imports,post is not None))
    return out

def scan(root):
    return {d.fq:d for p in sorted(root.rglob("*.agda")) for d in parse(p)}
def anymatch(value,pats): return any(re.search(p,value) for p in pats)
def build(spec,decls,strict=True):
    cards=[]
    for r in spec["cards"]:
        d=decls.get(r["declaration"])
        if not d:
            if strict: raise AtlasError(f"selected declaration not found: {r['declaration']}")
            continue
        cards.append(Card(r.get("id",d.fq),d,r.get("title",d.name),r.get("formula",d.signature),r.get("lane","critical path"),r.get("critical",True),r.get("source_anchors",[]),r.get("source_relation","DASHI introduces new theorem"),r.get("dependencies",[])))
    if len({c.id for c in cards})!=len(cards):raise AtlasError("duplicate card id")
    return cards

def derive(cards,spec):
    byid={c.id:c for c in cards}; byname={c.decl.name:c.id for c in cards}; rules=spec.get("authority_rules",{})
    for c in cards:
        c.deps=sorted(set(c.explicit)|{byname[t] for t in c.decl.tokens if t in byname and byname[t]!=c.id})
        missing=set(c.deps)-set(byid)
        if missing:raise AtlasError(f"{c.id}: unknown dependencies {sorted(missing)}")
        if not c.critical:c.state="legacy"
        elif c.decl.postulated or not c.decl.body or anymatch(c.decl.name,rules.get("open_declaration_patterns",[])):c.state="open_analytic"
        elif anymatch(c.decl.module,rules.get("source_imported_module_patterns",[])):c.state="source_imported"
        else:
            hits=[p for p in rules.get("conditional_input_type_patterns",[]) if re.search(p,c.decl.signature)]
            if hits:c.state="proved_conditional";c.open_inputs=hits
    def opens(n,trail=frozenset()):
        if n in trail:return set()
        c=byid[n]; found={n} if c.state=="open_analytic" else set()
        for d in c.deps:found|=opens(d,trail|{n})
        return found
    for c in cards:
        inherited=sorted(opens(c.id)-{c.id})
        if c.state=="proved" and inherited:c.state="proved_conditional"
        c.open_inputs=sorted(set(c.open_inputs)|set(inherited))
    visiting=set();done=set()
    def visit(n):
        if n in visiting:raise AtlasError(f"dependency cycle at {n}")
        if n in done:return
        visiting.add(n)
        for d in byid[n].deps:visit(d)
        visiting.remove(n);done.add(n)
    for n in byid:visit(n)

def make_payload(spec,cards,root,stamp):
    counts={k:0 for k in LABEL}; rows=[]
    for i,c in enumerate(cards,1):
        counts[c.state]+=1;d=c.decl
        rows.append({"number":i,"id":c.id,"title":c.title,"formula":c.formula,"lane":c.lane,"declaration":d.fq,"module":d.module,"name":d.name,"state":c.state,"state_label":LABEL[c.state],"critical":c.critical,"dependencies":c.deps,"open_inputs":c.open_inputs,"imports":d.imports,"source_locator":{"path":d.path.relative_to(root).as_posix(),"line":d.line},"source_anchors":c.anchors,"source_relation":c.relation,"signature":d.signature,"has_definition":bool(d.body),"postulated":d.postulated})
    return {"schema":SCHEMA,"schema_version":"1.0.0","title":spec.get("title","DASHI Theory Atlas"),"generated_at":stamp,"counts":counts,"cards":rows,"footer":"Compilation certifies type-correct assembly only. It does not discharge displayed open analytic inputs."}
def svg(data):
    rows=data["cards"];w,cw,ch,gap=1280,1120,180,34;h=330+len(rows)*(ch+gap);x=80;pos={r["id"]:150+i*(ch+gap) for i,r in enumerate(rows)}
    p=[f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}"><rect width="100%" height="100%" fill="#09090b"/><style>text{{font-family:system-ui,sans-serif}}.m{{font-family:monospace}}</style>',f'<text x="80" y="62" fill="#fafafa" font-size="34" font-weight="700">{html.escape(data["title"])}</text>']
    for r in rows:
        for d in r["dependencies"]:
            if d in pos:p.append(f'<path d="M 640 {pos[d]+ch} L 640 {pos[r["id"]]}" stroke="#52525b" stroke-width="3" fill="none"'+(' stroke-dasharray="10 8"' if r["state"]=="proved_conditional" else '')+'/>')
    for r in rows:
        y=pos[r["id"]];fill,stroke=COLOUR[r["state"]];dash=' stroke-dasharray="10 7"' if r["state"]=="open_analytic" else ''
        p += [f'<rect x="{x}" y="{y}" rx="18" width="{cw}" height="{ch}" fill="{fill}" stroke="{stroke}" stroke-width="3"{dash}/>',f'<text x="108" y="{y+38}" fill="{stroke}" font-size="18" font-weight="700">{r["number"]:02d} · {html.escape(r["lane"])}</text>',f'<text x="108" y="{y+72}" fill="#fafafa" font-size="25" font-weight="700">{html.escape(r["title"])}</text>',f'<text class="m" x="108" y="{y+108}" fill="#e4e4e7" font-size="16">{html.escape(r["formula"][:112])}</text>',f'<text class="m" x="108" y="{y+151}" fill="#a1a1aa" font-size="14">{html.escape(r["name"])}</text>',f'<text x="1172" y="{y+38}" fill="{stroke}" text-anchor="end" font-size="15" font-weight="700">{html.escape(r["state_label"])}</text>']
    p += [f'<text x="80" y="{h-64}" fill="#f4f4f5" font-size="17" font-weight="700">{html.escape(data["footer"])}</text>','</svg>']
    return "\n".join(p)+"\n"
def main():
    a=argparse.ArgumentParser();a.add_argument("--repo-root",type=Path,default=Path("."));a.add_argument("--spec",type=Path,default=Path("config/dashi-yang-mills-critical-path-atlas.json"));a.add_argument("--json-output",type=Path,default=Path("artifacts/dashi-yang-mills-critical-path.json"));a.add_argument("--svg-output",type=Path,default=Path("artifacts/dashi-yang-mills-critical-path.svg"));a.add_argument("--generated-at");a.add_argument("--no-strict",action="store_true");a.add_argument("--check",action="store_true");args=a.parse_args();root=args.repo_root.resolve();sp=args.spec if args.spec.is_absolute() else root/args.spec
    spec=json.loads(sp.read_text());
    if spec.get("schema")!=SCHEMA:raise AtlasError("wrong atlas schema")
    cards=build(spec,scan(root/spec.get("scan_root","DASHI")),not args.no_strict);derive(cards,spec);data=make_payload(spec,cards,root,args.generated_at or dt.datetime.now(dt.UTC).replace(microsecond=0).isoformat())
    if args.check:print(json.dumps({"ok":True,"cards":len(cards),"counts":data["counts"]},sort_keys=True));return
    jp=args.json_output if args.json_output.is_absolute() else root/args.json_output;sv=args.svg_output if args.svg_output.is_absolute() else root/args.svg_output;jp.parent.mkdir(parents=True,exist_ok=True);sv.parent.mkdir(parents=True,exist_ok=True);jp.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n");sv.write_text(svg(data));print(f"wrote {jp}\nwrote {sv}")
if __name__=="__main__":main()
