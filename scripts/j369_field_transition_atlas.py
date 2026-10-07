#!/usr/bin/env python3
"""Generated numerical atlas for PR #1053/J369. Numerical matches != recognition."""
import argparse, csv, json, math
from collections import Counter
from pathlib import Path

CARRIERS=(5,9,10,15,24,27,31,80,81,144,225,243,279,729,810,196830)

def is_prime(n):
    if n<2:return False
    if n%2==0:return n==2
    p=3
    while p*p<=n:
        if n%p==0:return False
        p+=2
    return True

def prime_power(n):
    if n<2:return None
    if is_prime(n):return (n,1)
    for p in range(2,math.isqrt(n)+1):
        if not is_prime(p):continue
        x,k=p,1
        while x<n:x*=p;k+=1
        if x==n:return (p,k)
    return None

def bracket_prime_powers(n):
    lo=n-1
    while prime_power(lo) is None:lo-=1
    hi=n+1
    while prime_power(hi) is None:hi+=1
    return lo,hi

def divisors(n):
    ds=[]
    for d in range(1,math.isqrt(n)+1):
        if n%d==0:
            ds.append(d)
            if d*d!=n:ds.append(n//d)
    return sorted(ds)

def phi(n):
    r,x,p=n,n,2
    while p*p<=x:
        if x%p==0:
            while x%p==0:x//=p
            r-=r//p
        p+=1
    if x>1:r-=r//x
    return r

def frobenius_orbit_count(q,m):
    return sum(phi(m//d)*q**d for d in divisors(m))//m

def prime_powers_up_to(limit):
    out=set()
    for p in range(2,limit+1):
        if not is_prime(p):continue
        x=p
        while x<=limit:
            out.add(x)
            if x>limit//p:break
            x*=p
    return sorted(out)

def field_bracket_rows(carriers):
    out=[]
    for n in carriers:
        lo,hi=bracket_prime_powers(n)
        out.append(dict(n=n,below=lo,above=hi,self_prime_power=prime_power(n),
                        multiplicative_upper=n+1 if prime_power(n+1) else None))
    return out

def numeric_candidates(n,q_limit=1000,m_limit=6):
    out=[]
    pp=prime_power(n)
    if pp:out.append((1,'T1',f'GF({n})',{'p':pp[0],'k':pp[1]}))
    if prime_power(n+1):out.append((2,'T2',f'GF({n+1})*',{}))
    for q in prime_powers_up_to(q_limit):
        for m in range(2,m_limit+1):
            upper=q**m
            if frobenius_orbit_count(q,m)==n:
                out.append((3,'T3',f'orbits(GF({upper})/GF({q}))',{'q':q,'m':m,'upper':upper}))
            if m==2:
                fixed,pairs=q,(q*q-q)//2
                if n in (fixed,pairs,q*q):
                    out.append((4,'T4',f'GF({q*q})/GF({q}) fixed/pair split',{'q':q,'fixed':fixed,'pairs':pairs}))
            if upper>max(10_000_000,n*100):break
    lo,hi=bracket_prime_powers(n); nearest=min((lo,hi),key=lambda x:(abs(x-n),x))
    out.append((6,'T6',f'GF({nearest}) bracket',{'distance':abs(nearest-n)}))
    seen=set(); ans=[]
    for x in sorted(out,key=lambda x:(x[0],x[2])):
        if x[2] not in seen:seen.add(x[2]);ans.append(x)
    return ans

# Exact numeric mirror of DASHI.Biology.FRACTRANSSPTransitionExact.firstEnabledStep.
def legacy_first_enabled_step(s):
    a,b,c,d=s
    if a>0:return a-1,b,c+1,d
    if c>0:return a,b,c-1,d+1
    if d>0:return a+1,b,c,d-1
    if b>0:return a+1,b-1,c,d
    return s

def legacy_states_exact_mass(total):
    out=[]
    for a in range(total+1):
        for b in range(total-a+1):
            for c in range(total-a-b+1):out.append((a,b,c,total-a-b-c))
    return out

def svg_head(w,h,title):
    return f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" viewBox="0 0 {w} {h}">\n<rect width="100%" height="100%" fill="white"/>\n<text x="20" y="28" font-family="sans-serif" font-size="18">{title}</text>\n'

def write_transition_svg(path,total=18,cols=37):
    ss=legacy_states_exact_mass(total); ix={s:i for i,s in enumerate(ss)}; rows=math.ceil(len(ss)/cols)
    w=h=1100; L,T,R,B=42,48,25,28; sx=(w-L-R)/(cols-1); sy=(h-T-B)/(rows-1)
    xy=lambda i:(L+(i%cols)*sx,T+(i//cols)*sy)
    z=[svg_head(w,h,f'J369 legacy FRACTRAN graph: mass={total}, nodes={len(ss)}, edges={len(ss)}')]
    for s in ss:
        x1,y1=xy(ix[s]);x2,y2=xy(ix[legacy_first_enabled_step(s)])
        z.append(f'<line x1="{x1:.2f}" y1="{y1:.2f}" x2="{x2:.2f}" y2="{y2:.2f}" stroke="#167d73" stroke-opacity=".24" stroke-width=".65"/>')
    for i in range(len(ss)):
        x,y=xy(i);z.append(f'<circle cx="{x:.2f}" cy="{y:.2f}" r="1.35" fill="#111"/>')
    path.write_text('\n'.join(z+['</svg>\n']))

def segment_cells(r0,c0,r1,c1):
    return {(round(r0+(r1-r0)*k/48),round(c0+(c1-c0)*k/48)) for k in range(49)}

def write_density_svg(path,total=18,cols=37):
    ss=legacy_states_exact_mass(total);ix={s:i for i,s in enumerate(ss)};rows=math.ceil(len(ss)/cols);den=Counter()
    for s in ss:
        i,j=ix[s],ix[legacy_first_enabled_step(s)];r0,c0=divmod(i,cols);r1,c1=divmod(j,cols)
        for cell in segment_cells(r0,c0,r1,c1):den[cell]+=1
    m=max(den.values());cell=22;w=cols*cell+100;h=rows*cell+100;z=[svg_head(w,h,f'J369 edge density: mass={total}, {cols}x{rows}')]
    for r in range(rows):
        for c in range(cols):
            v=den[(r,c)]/m;fill=f'rgb({int(246-150*v)},{int(250-100*v)},{int(248-120*v)})';x=40+c*cell;y=45+r*cell
            z.append(f'<rect x="{x}" y="{y}" width="{cell-1}" height="{cell-1}" fill="{fill}" stroke="#d7ece9" stroke-width=".5"/>')
    path.write_text('\n'.join(z+['</svg>\n']))

def field_relation_edges(carriers):
    e=[]
    for n in carriers:
        lo,hi=bracket_prime_powers(n);e += [(lo,n,'T6-below'),(n,hi,'T6-above')]
        if prime_power(n):e.append((n,n,'T1'))
        if prime_power(n+1):e.append((n+1,n,'T2'))
        for _,t,_,m in numeric_candidates(n):
            if t=='T3':e.append((m['upper'],n,f"T3-q{m['q']}-m{m['m']}"))
    return list(dict.fromkeys(e))

def write_field_relation_svg(path,carriers):
    e=field_relation_edges(carriers);nodes=sorted({x for a,b,_ in e for x in (a,b)});xs={n:math.log(n,3) for n in nodes}
    def yy(n):
        if n in carriers:return 0
        p,k=prime_power(n) or (2,1);return math.log2(p)/5+k/4
    ys={n:yy(n) for n in nodes};xmin,xmax=min(xs.values()),max(xs.values());ymax=max(ys.values());w,h=1200,700
    def xy(n):return 60+(xs[n]-xmin)/(xmax-xmin)*1110,655-ys[n]/ymax*600
    z=[svg_head(w,h,'PR #1053 field/carrier graph — numerical candidates only')]
    for a,b,_ in e:
        x1,y1=xy(a);x2,y2=xy(b);z.append(f'<line x1="{x1:.2f}" y1="{y1:.2f}" x2="{x2:.2f}" y2="{y2:.2f}" stroke="#167d73" stroke-opacity=".35" stroke-width=".8"/>')
    for n in nodes:
        x,y=xy(n);z.append(f'<circle cx="{x:.2f}" cy="{y:.2f}" r="{3.4 if n in carriers else 2.2}" fill="#111"/>')
        if n in carriers:z.append(f'<text x="{x:.2f}" y="{y-7:.2f}" text-anchor="middle" font-family="sans-serif" font-size="9">{n}</text>')
    path.write_text('\n'.join(z+['</svg>\n']))

def write_agda(path,rows):
    b=lambda x:'true' if x else 'false'
    z=['module DASHI.Moonshine.Generated.OggSSPFiniteFieldBracketGenerated where','','-- GENERATED by scripts/j369_field_transition_atlas.py; do not hand-edit.','-- Numerical candidates only: no semantic recognition is asserted.','','open import DASHI.Core.Prelude','open import Agda.Builtin.Bool using (Bool; true; false)','','record FieldBracketRow : Set where','  constructor field-bracket-row','  field','    carrier below above : Nat','    exactPrimePower : Bool','    multiplicativeUpper : Nat','','open FieldBracketRow public','','fieldBracketTable : List FieldBracketRow','fieldBracketTable =']
    for i,r in enumerate(rows):
        q=f'field-bracket-row {r["n"]} {r["below"]} {r["above"]} {b(r["self_prime_power"] is not None)} {r["multiplicative_upper"] or 0}'
        z.append(('  ' if i==0 else '  ∷ ')+q)
    z += ['  ∷ []','','fieldBracketRowCount : Nat','fieldBracketRowCount = 16','','tenQuadraticOrbitNumeratorExact : 2 * 10 ≡ 4 * 4 + 4','tenQuadraticOrbitNumeratorExact = refl','fifteenQuadraticOrbitNumeratorExact : 2 * 15 ≡ 5 * 5 + 5','fifteenQuadraticOrbitNumeratorExact = refl','twentyFourGF81OverGF3OrbitNumeratorExact : 4 * 24 ≡ 2 * 3 + 9 + 81','twentyFourGF81OverGF3OrbitNumeratorExact = refl','twentyFourGF64OverGF4OrbitNumeratorExact : 3 * 24 ≡ 2 * 4 + 64','twentyFourGF64OverGF4OrbitNumeratorExact = refl','','bulkMultiplicativeExact : 196830 + 1 ≡ 196831','bulkMultiplicativeExact = refl','generatorPrime196831 : Bool','generatorPrime196831 = true','','legacyMass18NodeCount legacyMass18EdgeCount : Nat','legacyMass18NodeCount = 1330','legacyMass18EdgeCount = 1330','mass18WeakCompositionNumeratorExact : 1330 * 6 ≡ 21 * 20 * 19','mass18WeakCompositionNumeratorExact = refl','legacyMass18GridDisplacementVectorCount : Nat','legacyMass18GridDisplacementVectorCount = 233','screenshotTwelveVectorCountMatches : Bool','screenshotTwelveVectorCountMatches = false','']
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text('\n'.join(z))

def generate(outdir,total=18,cols=37):
    outdir.mkdir(parents=True,exist_ok=True);rows=field_bracket_rows(CARRIERS)
    with (outdir/'fieldBracketTable.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['n','below','above','self_p','self_k','multiplicative_upper'])
        for r in rows:
            pp=r['self_prime_power'] or ('','');w.writerow([r['n'],r['below'],r['above'],pp[0],pp[1],r['multiplicative_upper'] or ''])
    with (outdir/'fieldCandidates.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['n','rank','test','candidate','metadata'])
        for n in CARRIERS:
            for rank,test,label,meta in numeric_candidates(n):w.writerow([n,rank,test,label,json.dumps(meta,sort_keys=True)])
    ss=legacy_states_exact_mass(total);ix={s:i for i,s in enumerate(ss)}
    with (outdir/f'legacyMass{total}Transitions.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['source_index','a47','b53','c59','d71','target_index','target_a47','target_b53','target_c59','target_d71'])
        for s in ss:
            t=legacy_first_enabled_step(s);w.writerow([ix[s],*s,ix[t],*t])
    vec=Counter()
    for s in ss:
        i,j=ix[s],ix[legacy_first_enabled_step(s)];r,c=divmod(i,cols);r2,c2=divmod(j,cols);vec[(r2-r,c2-c)]+=1
    manifest={'authoritative_carriers':list(CARRIERS),'legacy_transition_source':'DASHI.Biology.FRACTRANSSPTransitionExact.firstEnabledStep','legacy_mass':total,'legacy_nodes':len(ss),'legacy_edges':len(ss),'grid_cols':cols,'grid_rows':math.ceil(len(ss)/cols),'grid_displacement_vector_count':len(vec),'recognition_claimed':False,'t5_subfield_object_shape_inferred':False,'prime_196831':is_prime(196831)}
    (outdir/'atlasManifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    write_transition_svg(outdir/f'legacyMass{total}TransitionGraph.svg',total,cols);write_density_svg(outdir/f'legacyMass{total}EdgeDensity.svg',total,cols);write_field_relation_svg(outdir/'fieldRelationGraph.svg',CARRIERS);write_agda(outdir/'OggSSPFiniteFieldBracketGenerated.agda',rows)
    return manifest

def main():
    p=argparse.ArgumentParser();p.add_argument('--outdir',type=Path,default=Path('generated/j369-field-atlas'));p.add_argument('--mass',type=int,default=18);p.add_argument('--grid-cols',type=int,default=37);a=p.parse_args();print(json.dumps(generate(a.outdir,a.mass,a.grid_cols),sort_keys=True))
if __name__=='__main__':main()
