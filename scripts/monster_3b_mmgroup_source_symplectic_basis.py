#!/usr/bin/env python3
"""Source-derived actual Monster 3B Heisenberg + inertia generator alignment.

2026 primary computational source: Dietrich, Lee, Pisani, Popiel,
"Explicit construction of the maximal subgroups of the Monster",
Journal of Algebra 689 (2026), 862-895, DOI 10.1016/j.jalgebra.2025.10.016.
Source code:
  https://github.com/melissa-maths/MonsterSubgroups/blob/main/subgroups.py
  exact source blob c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2
This adapter reuses their literal L_N=(g3b,h3b) and E generation
x3b,y3b,l,gs,hs and constructs 6+6 SYMPLECTIC generators in the
SAME Monster element coordinates. It only prints a certificate after
checking every relation through mmgroup (which is required, not stubbed).

It DOES NOT compute the Monster W_zeta <-> JFine matrix T or
the final 12+78 multiplicity-space representation/cocycle.
"""
import argparse, json
from pathlib import Path

SOURCE_URL="https://github.com/melissa-maths/MonsterSubgroups/blob/main/subgroups.py"
SOURCE_BLOB_SHA="c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2"
LITERAL_WORDS={"g3b":"M<y_7f7h*x_1b7ah*d_1b2h*p_186721955*l_1*p_1457280*l_2*p_11725977*l_2*t_1*l_1*p_2999040*l_1*p_1415386*l_1*t_2*l_2*p_2597760*l_1*p_22314818*l_2*t_1*l_2*p_1457280*l_1*p_9639*t_1*l_2*p_1943040*l_2*p_42789700*t_1*l_2*p_2597760*l_1*p_85413716*l_1*p_2344320*t_2*l_1*p_467520*l_1*p_2788128*l_1>","h3b":"M<y_13bh*x_1c48h*d_4d9h*p_102050909*l_1*p_80762880*l_1*p_151282608*l_1*t_2*l_1*p_7560960*l_2*p_12439680*l_2*t_1*l_2*p_2597760*l_1*p_22356004*l_2*t_1*l_2*p_2787840*l_2*p_13464*t_2*l_1*p_47498880*l_2*p_42620352*t_2*l_2*p_1985280*l_1*p_64124776*t_2*l_2*p_1985280*l_1*p_42708878*t_2*l_2*p_2956800*l_1*p_64046790>","x3b":"M<y_5d4h*x_17efh*d_0f7eh*p_183231946*l_2*p_2787840*l_2*p_22759172>","y3b":"M<y_4ech*x_0aeeh*d_83bh*p_240916280*l_2*p_2597760*l_1*p_169605*t_2*l_1*p_2027520*l_1*p_22750595*t_2*l_1*p_2640000*l_1*p_178009*t_2*l_1*p_960*l_2*p_53815392*t_2*l_1*p_1415040*l_1*p_2256*l_2*p_76800*t_2*l_2*p_8004480*l_2*p_63909120>","gs":["M<y_58eh*x_8fh*d_2c9h*p_76285619*l_2*p_1457280*l_1*p_32103884*t_2*l_1*p_960*l_2*p_10665888*l_2*p_3763200*t_1*l_1*p_2027520*l_1*p_13020096*l_2*t_1*l_2*p_2956800*l_1*p_53349541*t_2*l_2*p_1415040*l_1*p_466800*l_2*p_3465600*t_1*l_2*p_2386560*l_2*p_42717489*t_2*l_2*p_2956800*l_1*p_85370418>","M<y_662h*x_17f8h*d_0ff0h*p_233651083*l_1*p_543360*t_1*l_1*p_2027520*l_1*p_47239*t_2*l_2*p_1457280*l_1*p_578263*t_1*l_1*p_15100800*t_2*l_2*p_2597760*l_1*p_21426569*t_1*l_2*p_2597760*l_1*p_64078688*t_1*l_1*p_1499520*l_1*p_85328065>","M<y_778h*x_0a7dh*d_0b20h*p_61290019*l_2*p_234220800*t_2*l_2*p_1943040*l_2*p_2352323*l_1*t_2*l_1*p_1858560*l_2*p_23280*l_1*p_2411520*t_2*l_1*p_3823680*t_1*l_1*p_68787840*l_1*p_108704736*t_1*l_2*p_2956800*l_1*p_53814185*t_1*l_2*p_59917440*l_1*p_127776096>","M<y_91h*x_550h*d_8f8h*p_131387342*l_2*p_1900800*l_2*p_21865336*l_2*t_1*l_1*p_1415040*l_1*p_23328*l_2*p_1520640*t_2*l_2*p_1943040*l_2*p_2414887*l_1*t_2*l_1*p_1099200*t_2*l_2*p_2830080*l_2*p_42796362*t_2*l_2*p_1943040*l_2*p_85816867*t_2*l_2*p_2956800*l_1*p_53381152>","M<y_36dh*x_0f60h*d_312h*p_128810854*l_1*p_2640000*l_1*p_21865335*t_1*l_2*p_2830080*l_2*p_21370*l_2*t_2*l_2*p_1985280*l_1*p_32504018*l_2*t_2*l_2*p_1943040*l_2*p_12176258*l_2*t_1*l_2*p_1900800*l_2*p_5763*t_2*l_2*p_2830080*l_2*p_42671248>"],"hs":["M<y_0abh*x_13d0h*d_0f66h*p_197048161*l_1*p_1858560*l_1*p_465936*l_2*p_510720*t_1*l_2*p_24000*l_2*p_488160*t_1*l_2*p_2386560*l_2*p_64036498*t_2*l_2*p_2787840*l_2*p_2800905*l_2*t_2*l_2*p_2787840*l_2*p_11554*t_2*l_1*p_2640000*l_1*p_13458>","M<y_119h*x_75bh*d_8bbh*p_203279177*l_2*p_2830080*l_2*p_10671544*t_1*l_1*p_2027520*l_1*p_22307968*l_1*t_1*l_2*p_2956800*l_1*p_21888592*l_2*t_1*l_1*p_1499520*l_2*p_42677961*t_2*l_2*p_2830080*l_2*p_21336113*t_1*l_1*p_1457280*l_2*p_12994999*l_1*t_1*l_2*p_2830080*l_2*p_21345778>","M<y_1a3h*x_0b74h*d_0a38h*p_201631922*l_2*p_2344320*l_2*p_33013873*l_2*t_1*l_1*p_1499520*l_2*p_467786*l_1*t_2*l_2*p_1393920*l_2*p_3120*l_1*p_1206720*t_1*l_2*p_1900800*l_2*p_3104*t_2*l_2*p_1858560*l_1*p_10665888*l_1*p_699840*t_2*l_2*p_5641920*l_1*t_1*l_2*p_1900800*l_2*p_137698>","M<y_0f2h*x_1c21h*d_0e0fh*p_228919392*l_1*p_80319360*l_2*p_231116160*t_1*l_2*p_1900800*l_2*p_22774569*l_2*t_1*l_2*p_2787840*l_2*p_33013910*l_1*t_1*l_2*p_1943040*l_2*p_33460438*l_1*t_2*l_1*p_2027520*l_1*p_5761*t_2*l_2*p_2830080*l_2*p_42798259>","M<y_4b1h*x_1162h*d_3b3h*p_195698166*l_2*p_2956800*l_1*p_32978354*l_2*t_1*l_1*p_2640000*l_1*p_2859335*l_2*t_1*l_2*p_1900800*l_2*p_2388161*l_1*t_2*l_1*p_467520*l_1*p_85056*t_2*l_1*p_1499520*l_1*p_85820694*t_2*l_2*p_1943040*l_2*p_85367645*t_2*l_2*p_1943040*l_2*p_42729963>"]}

def dot_form(u,v,M):
    return sum(u[i]*M[i][j]*v[j] for i in range(len(u)) for j in range(len(v))) % 3

def rank_f3(rows):
    W=[list(row) for row in rows]
    if not W:return 0
    h=len(W);w=len(W[0]); r=0
    for j in range(w):
        pivot=next((i for i in range(r,h) if W[i][j]%3),None)
        if pivot is None:continue
        W[pivot],W[r]=W[r],W[pivot]
        inv=pow(W[r][j]%3,-1,3)
        W[r]=[(x*inv)%3 for x in W[r]]
        for i in range(h):
            if i!=r:
                t=W[i][j]%3
                W[i]=[(x-t*y)%3 for x,y in zip(W[i],W[r])]
        r+=1
        if r==h:break
    return r

def symplectic_basis(M):
    """Gram-Schmidt over F3, normalized omega(B_i,A_j)=delta_ij."""
    n=len(M)
    if n%2 or any(len(x)!=n for x in M):
        raise ValueError("even-dimensional alternating Gram form required")
    if rank_f3(M)!=n:
        raise ValueError("source E generators fail full symplectic rank")
    basis=[tuple(int(i==j) for j in range(n)) for i in range(n)]
    A,B=[],[]
    def pairing(u,v):return dot_form(u,v,M)
    def lin(u,v,t):return tuple((a+t*b)%3 for a,b in zip(u,v))
    while basis:
        a=basis.pop(0)
        j=next((i for i,b in enumerate(basis) if pairing(b,a)),None)
        if j is None:raise AssertionError("nondegenerate pair unavailable")
        b=basis.pop(j)
        b=tuple(t*pow(pairing(b,a),-1,3)%3 for t in b)
        assert pairing(b,a)==1 and pairing(a,b)==2
        new=[]
        for v in basis:
            w=lin(lin(v,a,pairing(v,b)),b,-pairing(v,a))
            assert pairing(w,a)==pairing(w,b)==0
            new.append(w)
        A.append(a);B.append(b)
        basis=new
    V=A+B
    assert rank_f3(V)==n
    for i in range(n//2):
        for j in range(n//2):
            assert pairing(B[i],A[j])==int(i==j)
            assert pairing(A[i],A[j])==0
            assert pairing(B[i],B[j])==0
    return A,B

def run():
    try:
        from mmgroup import MM
        from importlib.metadata import version
    except ImportError as exc:
        raise RuntimeError("mmgroup unavailable; no synthetic Monster group used") from exc

    L=LITERAL_WORDS
    n1,n2=MM(L["g3b"]),MM(L["h3b"])
    z,y=MM(L["x3b"]),MM(L["y3b"])
    # Original source: r=(g3b**28)*(g3b**28)**h3b,
    # l=(r**(g3b**2)).reduce(); MM convention x**h=h^-1*x*h.
    r=(n1**28)*(n1**28)**n2
    ell=(r**(n1**2)).reduce()
    source=[y,ell]+[MM(w) for w in L["gs"]]+[MM(w) for w in L["hs"]]
    assert len(source)==12
    one=z**0
    if z.order()!=3 or not z.in_G_x0() or z.chi_G_x0()[0]!=53:
        raise RuntimeError("primary source x3b word failed Monster 3B centre recognition")
    for i,g in enumerate(source):
        if g.order()!=3 or z*g!=g*z:
            raise RuntimeError(f"original extraspecial generator {i} not order3 / centre-compatible")

    def exp_comm(g,h):
        for t in range(3):
            if g*h==z**t*h*g:
                return t
        raise ValueError("commutator not a power of selected central z")

    gram=[[exp_comm(g,h) for h in source] for g in source]
    if any(gram[i][i]!=0 or
           any((gram[i][j]+gram[j][i])%3 for j in range(12))
           for i in range(12)):
        raise RuntimeError("nonalternating E commutator pairing")
    if rank_f3(gram)!=12:
        raise RuntimeError("actual extraspecial generating words lack full rank")
    va,vb=symplectic_basis(gram)

    def make_word(v):
        out=one
        for g,t in zip(source,v):
            out=out*(g**t)
        return out
    A=[make_word(v) for v in va]; B=[make_word(v) for v in vb]
    for i in range(6):
        for j in range(6):
            if A[i]*A[j]!=A[j]*A[i] or B[i]*B[j]!=B[j]*B[i]:
                raise RuntimeError("symplectic basis fails isotropic group laws")
            if B[i]*A[j]!=z**int(i==j)*A[j]*B[i]:
                raise RuntimeError("symplectic basis fails exact Weyl commutator")

    def coordinates(g):
        av=[(-exp_comm(g,B[i]))%3 for i in range(6)]
        bv=[exp_comm(g,A[i]) for i in range(6)]
        word=one
        for e,a in zip(A,av):word=word*e**a
        for e,b in zip(B,bv):word=word*e**b
        t=next((i for i in range(3) if g==word*z**i),None)
        if t is None:raise RuntimeError("source image is not an E element in reconstructed basis")
        return dict(a=av,b=bv,t=t)

    # Source claim generator set x3b,y3b,l,gs,hs generates E.
    # Verify exact original generator-word reconstruction in the new basis.
    for g in source:
        c=coordinates(g)
        assert len(c["a"])==len(c["b"])==6

    lift_rows=[]
    for name,h in (("g3b",n1),("h3b",n2)):
        ci=next((t for t in (1,2) if h*z*h**-1==z**t),None)
        if ci is None:raise RuntimeError(f"{name} does not normalize central C3")
        ar=[coordinates(h*g*h**-1) for g in A]
        br=[coordinates(h*g*h**-1) for g in B]
        S=[x["a"]+x["b"] for x in ar+br]  # columns
        if rank_f3(list(zip(*S)))!=12:
            raise RuntimeError(f"{name} induces singular map E/Z(E)")
        lift_rows.append(dict(name=name,word=str(h),central_image=1 if ci==1 else -1,
                              translation_images=ar,modulation_images=br))

    manifest=dict(source_url=SOURCE_URL,source_blob_sha=SOURCE_BLOB_SHA,
                  center_word=str(z),translation_words=[str(g) for g in A],
                  modulation_words=[str(g) for g in B],
                  normalizer_lifts=lift_rows)
    # Reuse existing exact MM word checker: verifies all 36 Weyl pairs plus
    # 24 normalizer generator images in a DIFFERENT implementation path.
    from monster_3b_mmgroup_weyl_word_alignment import check_words
    checked=check_words(manifest)
    # SAME source copy of N(3B), acting on the actual 196884-dimensional
    # Monster vector module over F7 (primitive third root zeta=2).
    # This checks real zeta eigenspace transport, NOT 12+78 in char zero.
    from mmgroup import MMV
    V7=MMV(7)
    specs=[("A",0,0),("A",0,1),("B",0,1),("C",0,1),
           ("T",0,0),("X",1,0),("Y",1,0),("Z",1,0)]
    nonzero_samples=0
    for tag,i,j in specs:
        v=V7(tag,i,j)
        projected=5*(v+4*(v*z)+2*(v*(z**2)))
        if projected*z!=2*projected:
            raise RuntimeError("actual MMV(7) zeta projector eigenrelation failed")
        if projected==0*v:
            continue
        nonzero_samples+=1
        for g in (A[0],A[1],B[0],B[1]):
            if (projected*g)*z!=2*(projected*g):
                raise RuntimeError("actual E generator does not preserve zeta sector")
        for lift in lift_rows:
            h=MM(lift["word"])
            expected=2 if lift["central_image"]==1 else 4
            if (projected*h)*z!=expected*(projected*h):
                raise RuntimeError("actual normalizer lift has wrong phase transport")
    if not nonzero_samples:
        raise RuntimeError("no sampled nonzero actual Monster zeta vectors")
    checked.update(
        actual_MMV7_nonzero_zeta_samples=nonzero_samples,
        actual_MMV7_phase_transport_checked=True,
        characteristic_zero_12_78_inferred_from_F7=False,
        # Characteristic 7 divides |Suz|, so semisimplicity for the
        # full normalizer is not inferred from this modular representation.
        source_blob_sha=SOURCE_BLOB_SHA,rank_commutator_form=rank_f3(gram),
                   normalizer_generators=[x["name"] for x in lift_rows],
                   characteristic_7_vector_action_available=True,
                   observed_actual_mmgroup_execution=True,
                   Wzeta_to_JFine_intertwiner=False,
                   actual_Hom_12_78_character=False,
                   mmgroup_version=version("mmgroup"))
    return manifest,checked

def selftest():
    I=[[0]*12 for _ in range(12)]
    for i in range(6):
        I[i+6][i]=1
        I[i][i+6]=2
    A,B=symplectic_basis(I)
    assert rank_f3(A+B)==12
    return dict(status="local_pure_F3_symplectic_selftest",matrix_rank=12,
                full_D4_or_Monster_action_tested=False)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--selftest",action="store_true")
    parser.add_argument("--manifest",type=Path)
    parser.add_argument("--receipt",type=Path)
    args=parser.parse_args()
    if args.selftest: result=selftest()
    else:
        manifest,result=run()
        if args.manifest:args.manifest.write_text(json.dumps(manifest,indent=2)+"\n")
    if args.receipt:args.receipt.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
if __name__=="__main__":main()
