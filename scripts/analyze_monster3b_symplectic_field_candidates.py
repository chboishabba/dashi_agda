#!/usr/bin/env python3
"""Analyze imported 12x12 GF(3) ATLAS generators for the Monster 3B normalizer.

Consumes integer generator rows emitted by `acquire_monster3b_suzuki12_atlas.g`.
It does not manufacture source matrices.

Once matrices are present the script:
  * solves A^T S A = S for the common invariant alternating form;
  * constructs P with P^T S P = J_std on X6 + X6*;
  * conjugates generators into the repository standard symplectic basis;
  * derives/checks the central Heisenberg cocycle correction by polarization;
  * searches short normalizer words stabilizing the chosen X6 Lagrangian;
  * factors their 6x6 characteristic polynomials over GF(3), flagging
    irreducible degree-six field-generator candidates.

The direct ATLAS 12-dimensional module is absolutely irreducible, so the full
2.Suz:2 action cannot preserve a nonzero six-dimensional submodule.  The field
search is intentionally element/stabilizer-local, not a global X6 action claim.
"""
from __future__ import annotations
import argparse, ast, json, re
from collections import deque
from pathlib import Path
import sympy as sp

MOD=3; N=12; HALF=6

def mod(x): return int(x)%MOD
def eye(n): return [[1 if i==j else 0 for j in range(n)] for i in range(n)]
def transpose(A): return [list(x) for x in zip(*A)]
def matmul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(len(B)))%MOD for j in range(len(B[0]))] for i in range(len(A))]
def matvec(A,v): return [sum(a*b for a,b in zip(row,v))%MOD for row in A]
def flatten(A): return tuple(x for row in A for x in row)
def pairing(v,S,w): return sum(v[i]*S[i][j]*w[j] for i in range(len(v)) for j in range(len(w)))%MOD

def rank_mod(A):
    A=[list(map(mod,r)) for r in A]
    if not A:return 0
    m,n=len(A),len(A[0]);r=0
    for c in range(n):
        p=next((i for i in range(r,m) if A[i][c]),None)
        if p is None:continue
        A[r],A[p]=A[p],A[r];inv=1 if A[r][c]==1 else 2;A[r]=[(inv*x)%MOD for x in A[r]]
        for i in range(m):
            if i!=r and A[i][c]:
                q=A[i][c];A[i]=[(x-q*y)%MOD for x,y in zip(A[i],A[r])]
        r+=1
        if r==m:break
    return r

def inverse_mod(A):
    n=len(A);M=[list(map(mod,row))+eye(n)[i] for i,row in enumerate(A)]
    for c in range(n):
        p=next((i for i in range(c,n) if M[i][c]),None)
        if p is None:raise ValueError('singular matrix')
        M[c],M[p]=M[p],M[c];inv=1 if M[c][c]==1 else 2;M[c]=[(inv*x)%MOD for x in M[c]]
        for i in range(n):
            if i!=c and M[i][c]:
                q=M[i][c];M[i]=[(x-q*y)%MOD for x,y in zip(M[i],M[c])]
    return [r[n:] for r in M]

def nullspace_mod(A):
    A=[list(map(mod,r)) for r in A];m=len(A);n=len(A[0]) if m else 0;r=0;piv=[]
    for c in range(n):
        p=next((i for i in range(r,m) if A[i][c]),None)
        if p is None:continue
        A[r],A[p]=A[p],A[r];inv=1 if A[r][c]==1 else 2;A[r]=[(inv*x)%MOD for x in A[r]]
        for i in range(m):
            if i!=r and A[i][c]:
                q=A[i][c];A[i]=[(x-q*y)%MOD for x,y in zip(A[i],A[r])]
        piv.append(c);r+=1
        if r==m:break
    free=[c for c in range(n) if c not in piv];out=[]
    for f in free:
        v=[0]*n;v[f]=1
        for rr,c in reversed(list(enumerate(piv))):v[c]=(-sum(A[rr][j]*v[j] for j in free))%MOD
        out.append(v)
    return out

PAIRS=[(i,j) for i in range(N) for j in range(i+1,N)]
def skew_basis(k):
    i,j=PAIRS[k];S=[[0]*N for _ in range(N)];S[i][j]=1;S[j][i]=2;return S

def invariant_form(gens):
    bs=[skew_basis(k) for k in range(len(PAIRS))];eq=[]
    for A in gens:
        At=transpose(A);trs=[matmul(matmul(At,S),A) for S in bs]
        for i,j in PAIRS:eq.append([(trs[k][i][j]-bs[k][i][j])%MOD for k in range(len(bs))])
    ns=nullspace_mod(eq)
    if not ns:raise ValueError('no invariant alternating form')
    trials=list(ns)+[[(a+b)%MOD for a,b in zip(ns[i],ns[j])] for i in range(len(ns)) for j in range(i+1,len(ns))]
    for c in trials:
        S=[[0]*N for _ in range(N)]
        for z,(i,j) in zip(c,PAIRS):S[i][j]=(S[i][j]+z)%MOD;S[j][i]=(S[j][i]-z)%MOD
        if rank_mod(S)==N:return S,len(ns)
    raise ValueError('invariant form space found but no nondegenerate trial')

def independent(vs):
    out=[]
    for v in vs:
        if rank_mod([list(x) for x in zip(*(out+[v]))])>len(out):out.append(v)
    return out

def symplectic_basis(S):
    work=eye(N);es=[];fs=[]
    while work:
        v=work[0];wi=next((i for i,w in enumerate(work[1:],1) if pairing(v,S,w)),None)
        if wi is None:raise ValueError('degenerate residual')
        w=work[wi]
        if pairing(v,S,w)==2:w=[2*x%MOD for x in w]
        new=[]
        for k,u in enumerate(work[1:],1):
            if k==wi:continue
            a=pairing(u,S,w);b=pairing(u,S,v);up=[(u[t]-a*v[t]+b*w[t])%MOD for t in range(N)]
            if any(up):new.append(up)
        es.append(v);fs.append(w);work=independent(new)
    P=[list(r) for r in zip(*(es+fs))]
    J=[[0]*N for _ in range(N)]
    for i in range(HALF):J[i][HALF+i]=1;J[HALF+i][i]=2
    if matmul(matmul(transpose(P),S),P)!=J:raise ValueError('symplectic normalization failed')
    return P,J

def block(M,r0,r1,c0,c1):return [r[c0:c1] for r in M[r0:r1]]
def is_zero(M):return all(x%MOD==0 for r in M for x in r)
def charpoly_info(A):
    x=sp.symbols('x');p=sp.Poly(sp.Matrix(A).charpoly(x).as_expr(),x,modulus=3);fac=sp.factor_list(p,modulus=3)[1]
    deg=[]
    for f,e in fac:deg += [int(sp.degree(f))]*e
    irr=len(fac)==1 and fac[0][1]==1 and sp.degree(fac[0][0])==len(A)
    return str(p.as_expr()),sorted(deg),bool(irr)
def cocycle(x,y):return sum(b*a for b,a in zip(x[HALF:],y[:HALF]))%MOD
def correction(M,x):
    Mx=matvec(M,x);d=(cocycle(Mx,Mx)-cocycle(x,x))%MOD
    return 2*d%MOD   # 1/2 = 2 in F3
def correction_check(M):
    tests=[[0]*N]+eye(N)
    for x in tests:
        for y in tests:
            xy=[(a+b)%MOD for a,b in zip(x,y)]
            lhs=(correction(M,xy)+cocycle(x,y))%MOD
            rhs=(correction(M,x)+correction(M,y)+cocycle(matvec(M,x),matvec(M,y)))%MOD
            if lhs!=rhs:return False
    return True

def parse_dump(path):
    text=Path(path).read_text();mats=[]
    for m in re.finditer(r'generator_(\d+)_int\s*=\s*(\[\[.*?\]\])\s*(?:\n|$)',text,re.S):mats.append((int(m.group(1)),ast.literal_eval(m.group(2))))
    if not mats:
        data=json.loads(text);raw=data['generators'] if isinstance(data,dict) else data;mats=[(i+1,A) for i,A in enumerate(raw)]
    mats=[[[mod(x) for x in r] for r in A] for _,A in sorted(mats)]
    if any(len(A)!=N or any(len(r)!=N for r in A) for A in mats):raise ValueError('expected 12x12 matrices')
    return mats

def search(gens,depth):
    letters=[(f'g{i+1}',A) for i,A in enumerate(gens)]+[(f'g{i+1}^-1',inverse_mod(A)) for i,A in enumerate(gens)]
    I=eye(N);q=deque([(I,[])]);seen={flatten(I)};hits=[]
    while q:
        M,w=q.popleft();C=block(M,HALF,N,0,HALF)
        if w and is_zero(C):
            A=block(M,0,HALF,0,HALF);cp,degs,irr=charpoly_info(A);hits.append({'word':' '.join(w),'length':len(w),'charpoly':cp,'factor_degrees':degs,'irreducible_degree6':irr})
        if len(w)>=depth:continue
        for name,G in letters:
            H=matmul(G,M);key=flatten(H)
            if key not in seen:seen.add(key);q.append((H,w+[name]))
    return hits,len(seen)

def analyze(gens,depth):
    S,dim=invariant_form(gens);P,J=symplectic_basis(S);Pinv=inverse_mod(P);std=[matmul(matmul(Pinv,A),P) for A in gens]
    assert all(matmul(matmul(transpose(A),J),A)==J for A in std)
    hits,visited=search(std,depth)
    return {'field_order':3,'dimension':12,'generator_count':len(gens),'invariant_alternating_form_space_dimension':dim,'invariant_form':S,'symplectic_basis_columns':P,'all_conjugated_generators_symplectic':True,'central_correction_basis_pair_checks':[correction_check(A) for A in std],'search_depth':depth,'distinct_words_or_elements_visited':visited,'chosen_lagrangian_stabilizer_hits':hits,'irreducible_degree6_hits':[h for h in hits if h['irreducible_degree6']],'full_normalizer_x6_invariant_claim':False,'interpretation':'full 12D module is absolutely irreducible; degree-six tests are element/stabilizer-local'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--matrix-dump',required=True);ap.add_argument('--search-depth',type=int,default=4);ap.add_argument('--output',default='monster3b_symplectic_field_candidates.json');args=ap.parse_args()
    out=analyze(parse_dump(args.matrix_dump),args.search_depth);Path(args.output).write_text(json.dumps(out,indent=2)+'\n');print('symplectic=',out['all_conjugated_generators_symplectic']);print('lagrangian_hits=',len(out['chosen_lagrangian_stabilizer_hits']));print('irreducible_degree6_hits=',len(out['irreducible_degree6_hits']))
if __name__=='__main__':main()
