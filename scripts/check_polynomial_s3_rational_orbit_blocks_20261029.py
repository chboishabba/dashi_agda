#!/usr/bin/env python3
"""Exact native 27-code rational S3 block audit for PR #1414.

No third-party dependency. Reads ACTUAL checked-out Agda matrix / code
tables, checks two-sided exact scaled integer inverse certificates,
all 216 regular-block intertwining cases, all 162 native S3 actions,
and nonzero exact determinants of the seven 1/2/3/6 orbit blocks.

This is computational proof-support evidence, not an Agda kernel
receipt, global polynomial Galois proof, or Monster3B same-object claim.
Classical S3 representation theory predates these implementation files.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[1]
PROOFS=ROOT/"DASHI"/"Foundations"
NAMES=[
    "PolynomialS3RegularRationalBlockCertificateExact",
    "PolynomialS3SmallRationalBlockCertificateExact",
    "PolynomialS3RegularOrbitToNativeCodeExact",
    "PolynomialS3TwentySevenOrbitBlockAssemblyExact",
]

def owner(name):
    f=PROOFS/(name+".agda")
    assert f.is_file(), f"missing Agda owner {f}"
    return f.read_text(encoding="utf-8")

def integer_matrices(source,name,n,prefix):
    pat=re.compile(r"^"+name+r" "+prefix+r"([0-9]) "+prefix+
                   r"([0-9]) = (pos|negsuc) ([0-9]+)$",re.M)
    a=[[None for _ in range(n)] for _ in range(n)]
    for i,j,mode,v in pat.findall(source):
        i,j,v=int(i),int(j),int(v)
        assert a[i][j] is None
        a[i][j]=v if mode=="pos" else -v-1
    assert all(isinstance(x,int) for row in a for x in row),(name,a)
    return a

def dot(A,B,i,j):
    return sum(A[i][k]*B[k][j] for k in range(len(A)))

def determinant(A):
    n=len(A);M=[[Fraction(t) for t in row] for row in A];result=Fraction(1)
    for j in range(n):
        pivot=next((k for k in range(j,n) if M[k][j]),None)
        assert pivot is not None, "singular block"
        if pivot!=j:
            M[j],M[pivot]=M[pivot],M[j]
            result=-result
        d=M[j][j];result*=d
        for k in range(j+1,n):
            scale=M[k][j]/d
            for l in range(j,n):
                M[k][l]-=scale*M[j][l]
    return result

PERMS=((0,1,2),(1,2,0),(2,0,1),(1,0,2),(2,1,0),(0,2,1))
CODE=(0,1,2)
REPS=((0,1,2),(1,2,0),(0,2,1),(0,0,0),(0,0,1),(0,0,2),(1,0,0))
SHAPES=("identityBlock","cycleBlock","transpositionBlock","constantBlock",
        "oneFixedBlock","twoFixedBlock","twoCycleBlock")
WORDS={"low":0,"mid":1,"high":2}

def inverse(p):
    return tuple(p.index(i) for i in CODE)

def multiply(p,q):
    return tuple(p[q[i]] for i in CODE)

def conjugate(p,f):
    ip=inverse(p)
    return tuple(p[f[ip[i]]] for i in CODE)

def parity(p):
    return (-1)**sum(p[i]>p[j] for i in CODE for j in CODE if i<j)

def rho(p):
    cols=[]
    for u in (0,1):
        x=[int(i==u)-int(i==2) for i in CODE]
        y=[x[inverse(p)[i]] for i in CODE]
        assert sum(y)==0
        cols.append(y[:2])
    return [[cols[j][i] for j in (0,1)] for i in (0,1)]

def test():
    reg,small,native,assembly=map(owner,NAMES)
    B6=integer_matrices(reg,"basis6",6,"slot")
    C6=integer_matrices(reg,"scaledInverse6",6,"slot")
    B3=integer_matrices(small,"basis3",3,"axis")
    C3=integer_matrices(small,"scaledInverse3",3,"axis")
    B2=integer_matrices(small,"basis2",2,"pair")
    C2=integer_matrices(small,"scaledInverse2",2,"pair")
    for B,C,factor in ((B2,C2,2),(B3,C3,3),(B6,C6,54)):
        for i,j in product(range(len(B)),repeat=2):
            target=factor*int(i==j)
            assert dot(B,C,i,j)==target
            assert dot(C,B,i,j)==target
    assert [determinant(M) for M in (B2,B3,B6)]==[-2,3,-54]

    for p in PERMS:
        T=[[0]*6 for _ in range(6)]
        T[0][0]=1
        T[1][1]=parity(p)
        R=rho(p)
        for r,c in product(range(2),repeat=2):
            T[2+r][2+c]=R[r][c]
            T[4+r][4+c]=R[r][c]
        for i,j in product(range(6),repeat=2):
            gi=PERMS[i]
            pi=inverse(p)
            left=PERMS.index(multiply(pi,gi))
            assert B6[left][j]==dot(B6,T,i,j),(p,i,j)
    for p in PERMS:
        M2=[[1,0],[0,parity(p)]]
        for i,j in product(range(2),repeat=2):
            pi=i if parity(p)==1 else 1-i
            assert B2[pi][j]==dot(B2,M2,i,j)
        M3=[[1,0,0],[0,rho(p)[0][0],rho(p)[0][1]],
            [0,rho(p)[1][0],rho(p)[1][1]]]
        for i,j in product(range(3),repeat=2):
            pi=inverse(p)[i]
            assert B3[pi][j]==dot(B3,M3,i,j)

    # Actual 27 native-code label proof, not a numeric-orbit count.
    labels={}
    rx=re.compile(
        r"^codeToBlock \(Base\.tri-(low|mid|high) , "
        r"\(Base\.tri-(low|mid|high) , Base\.tri-(low|mid|high)\)\)"
        r" = (.+)$",re.M)
    for a,b,c,part in rx.findall(assembly):
        code=(WORDS[a],WORDS[b],WORDS[c])
        assert code not in labels
        labels[code]=part
    assert len(labels)==27
    canonical={}
    canonical[REPS[0]]="identityBlock"
    for i,cy in enumerate(((1,2,0),(2,0,1))):
        canonical[cy]=f"cycleBlock Small.pair{i}"
    for title,code_list in (
        ("transpositionBlock",((0,2,1),(2,1,0),(1,0,2))),
        ("constantBlock",((0,0,0),(1,1,1),(2,2,2)))):
        for i,c in enumerate(code_list):
            canonical[c]=f"{title} Small.axis{i}"
    for title,rep in zip(SHAPES[4:],REPS[4:]):
        for i,p in enumerate(PERMS):
            canonical[conjugate(p,rep)]=f"{title} Regular.Block.slot{i}"
    assert labels==canonical

    for p in PERMS:
        for c in canonical:
            observed=labels[conjugate(p,c)]
            part=labels[c]
            if part=="identityBlock":
                expected=part
            elif part.startswith("cycleBlock"):
                index=int(part[-1])
                expected=f"cycleBlock Small.pair{index if parity(p)==1 else 1-index}"
            elif part.startswith(("transpositionBlock","constantBlock")):
                index=int(part[-1])
                expected=part[:-1]+str(p[index])
            else:
                index=int(part[-1])
                next_index=PERMS.index(multiply(p,PERMS[index]))
                expected=part[:-1]+str(next_index)
            assert observed==expected,(p,c,observed,expected)

    det_product=determinant([[1]])
    for M in (B2,B3,B3,B6,B6,B6):
        det_product*=determinant(M)
    assert det_product!=0
    assert abs(det_product)==2834352
    assert len(re.findall(r"^regularBlockIntertwines Perm\.perm\w+ slot\d slot\d = refl$",reg,re.M))==216
    assert len(re.findall(r"^nativeBlockActionByShape Shape\.perm\w+",assembly,re.M))==162
    assert len(re.findall(r"^regularCodeFree ",native,re.M))==108
    print("PASS exact 2x2/3x3/6x6 scaled integer inverses")
    print("PASS rational determinants: 1, -2, 3, 3, ±54, ±54, ±54")
    print("PASS 216 regular and 24+54 small-block intertwining cases")
    print("PASS 27 native code labels and 162 original S3 actions")
    print(f"PASS full Q^27 block basis, absolute determinant {abs(det_product)}")
    print("NO CLAIM: Agda kernel acceptance; generic Galois/Monster same-object theorem")

if __name__=="__main__":
    test()
