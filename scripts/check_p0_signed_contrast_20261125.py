from fractions import Fraction as Q
from math import isqrt
from itertools import product
from random import Random
from heapq import heappush, heappop, heapify
from check_p0_budgeted_residual_20261125 import cap as source_cap, pair_source
from check_pnp_signed_component_histogram import component_bounds
from check_pnp_signed_boundary_energy import boundary_contrast
from check_pnp_f3_syndrome_boundary import syndrome_contrast
from check_pnp_f3_normal_fold import normal_contrast
from check_pnp_dual_syndrome_fourier import dual_contrast
from check_pnp_quadratic_phase import structured_contrast
from check_pnp_mobius_character import mobius_contrast
from check_pnp_mobius_prefix import prefix_portfolio

# Each source sector: CNF, affine rows/target, one observable trit, signed weight.
def canon(F):
    return tuple(sorted({tuple(sorted(set(c))) for c in F if not any(-x in c for x in c)}))
def restrict(F,i,b):
    l=(i+1)*(1 if b else -1)
    return canon(tuple(x for x in c if x!=-l) for c in F if l not in c)
def add(a,b,k=1):return tuple((x+k*y)%3 for x,y in zip(a,b))
def basis(cols):
    B={}
    for v in cols:
        for i,u in sorted(B.items()):v=add(v,u,-v[i])
        if any(v):
            i=next(i for i,x in enumerate(v) if x);B[i]=tuple(v[i]*x%3 for x in v)
    return B
def member(B,v):
    for i,u in sorted(B.items()):v=add(v,u,-v[i])
    return not any(v)
def cell(F,cols,target,offset,remaining,w,conditioned=True,component_width=6,boundary_width=3,syndrome_budget=16384,normal_budget=16384,dual_budget=16384,dual_probes=32,phase_budget=65536,mobius_budget=65536,prefix_budget=65536):
    # Unit propagation keeps both target and observable offset on original indices.
    while True:
        if () in F:return None
        u=next((c[0] for c in F if len(c)==1),None)
        if u is None:break
        i=abs(u)-1;b=int(u>0);remaining=tuple(j for j in remaining if j!=i)
        target=add(target,cols[i][:-1],-b);offset=(offset+b*cols[i][-1])%3;F=restrict(F,i,b)
    B=basis(cols[i][:-1] for i in remaining)
    if not member(B,target):return None
    J=basis(cols[i] for i in remaining)
    labels=[z for z in range(3) if member(J,target+((z-offset)%3,))]
    if not labels:return None
    C=2**(len(remaining)-len(B))
    # Exact mass only for an unconstrained Boolean cube; otherwise [0,C].
    exact=not F and not any(target) and not any(any(cols[i][:-1]) for i in remaining)
    if exact:
        H=[int(z==offset) for z in range(3)]
        for i in remaining:H=[H[z]+H[(z-cols[i][-1])%3] for z in range(3)]
        a=tuple(w*(3*h-C) for h in H)
        return (F,cols,target,offset,remaining,w,a,a)
    if not conditioned:
        a=[[w*(3*int(z==d)-1) for z in labels] for d in range(3)]
        return (F,cols,target,offset,remaining,w,tuple(C*min(0,*q) for q in a),tuple(C*max(0,*q) for q in a))
    # Refine the old common cap by the original source's disjoint-free-
    # clause cap, then condition on the ACTUAL observable label.  The
    # two signed contributions are bounded separately, preserving the
    # common-mode cancellation and avoiding a global magnitude envelope.
    C=min(C,source_cap(F,remaining,[v[:-1] for v in cols],target))
    if not C:return None
    label_caps=[min(C,source_cap(F,remaining,cols,target+((d-offset)%3,)))
                if d in labels else 0 for d in range(3)]
    C=min(C,sum(label_caps))
    if not C:return None
    # Exact multiplicative mass / additive label fold. A refused component
    # still contributes its certified cap; no global assignment expansion.
    E=None
    if component_width is not None:
        done,cc,hh,E=component_bounds(F,cols,target,offset,remaining,component_width,spectral=True)
        if not cc:return None
        if E==0:
            a=(Q(0),)*3
            return (F,cols,target,offset,remaining,w,a,a)
        if done:
            a=tuple(w*(3*h-cc) for h in hh)
            return (F,cols,target,offset,remaining,w,a,a)
        C=min(C,cc)
        label_caps=[min(C,a,b) for a,b in zip(label_caps,hh)]
        C=min(C,sum(label_caps))
        if not C:return None
    lo=[];hi=[]
    for d in range(3):
        positive=2*min(C,label_caps[d])
        negative=min(C,sum(label_caps[j] for j in range(3) if j!=d))
        # Exact contrast w*(2*N_d-N_other); both masses are nonnegative.
        a,b=-w*negative,w*positive
        lo.append(min(a,b));hi.append(max(a,b))
    if E is not None:
        # Each contrast is an integer multiple of w and its square is <=4E.
        # No floating point or absolute mass reconstruction needed.
        radius=abs(w)*isqrt(4*E)
        lo=[max(a,-radius) for a in lo];hi=[min(a,radius) for a in hi]
    if E is not None and boundary_width is not None and any(a!=b for a,b in zip(lo,hi)):
        cert=boundary_contrast(F,cols,target,offset,remaining,w,component_width,boundary_width)
        if cert is not None:
            a,b,_=cert
            lo=[max(x,y) for x,y in zip(lo,a)];hi=[min(x,y) for x,y in zip(hi,b)]
            assert all(x<=y for x,y in zip(lo,hi))
    # Intrinsic syndrome cut: coupling through the original affine image
    # rather than a shared list of Boolean variables. The attempt is
    # independently capped; on refusal retain the prior certificate.
    if E is not None and boundary_width is not None and syndrome_budget and any(a!=b for a,b in zip(lo,hi)):
        cert=syndrome_contrast(F,cols,target,offset,remaining,w,component_width,boundary_width,syndrome_budget)
        if cert is not None:
            a,b,_=cert
            lo=[max(x,y) for x,y in zip(lo,a)];hi=[min(x,y) for x,y in zip(hi,b)]
            assert all(x<=y for x,y in zip(lo,hi))
    # Collective factor-normal join after the prior source certificates.
    # The same original affine chart supplies every coordinate guard.
    if E is not None and boundary_width is not None and normal_budget and any(a!=b for a,b in zip(lo,hi)):
        cert=normal_contrast(F,cols,target,offset,remaining,w,component_width,boundary_width,normal_budget)
        if cert is not None:
            a,b,_=cert
            assert all(x<=y<=z for x,y,z in zip(lo,a,hi))
            lo,hi=list(a),list(b)
    # Source-derived dual probes: absolute Parseval tail, not an oracle
    # for the heavy frequencies. Independent attempt cap.
    if E is not None and dual_budget and any(a!=b for a,b in zip(lo,hi)):
        cert=dual_contrast(F,cols,target,offset,remaining,w,component_width,dual_probes,dual_budget)
        if cert is not None:
            a,b,_=cert
            lo=[max(x,y) for x,y in zip(lo,a)];hi=[min(x,y) for x,y in zip(hi,b)]
            assert all(x<=y for x,y in zip(lo,hi))
    # Verified structured phase generator, then signed overlapping-clause
    # intersections with low-rank cube characters. Independent caps;
    # refused attempts leave the previous certified interval intact.
    if E is not None and phase_budget and any(a!=b for a,b in zip(lo,hi)):
        cert=structured_contrast(F,cols,target,offset,remaining,w,component_width,64,phase_budget,degree_cap=3,phase_branch_cap=64)
        if cert is not None:
            a,b,_=cert
            assert all(x<=y<=z for x,y,z in zip(lo,a,hi))
            lo,hi=list(a),list(b)
    if mobius_budget and any(a!=b for a,b in zip(lo,hi)):
        cert=mobius_contrast(F,cols,target,offset,remaining,w,4,4096,mobius_budget)
        if cert is not None:
            a,b,_=cert
            assert all(x<=y<=z for x,y,z in zip(lo,a,hi))
            lo,hi=list(a),list(b)
    # A completed prefix is exact even when the full signed intersection
    # expansion refuses. The removed mass is bounded label by label.
    if prefix_budget and any(a!=b for a,b in zip(lo,hi)):
        cert=prefix_portfolio(F,cols,target,offset,remaining,w,4096,prefix_budget)
        if cert is not None:
            a,b,_=cert
            lo=[max(x,y) for x,y in zip(lo,a)];hi=[min(x,y) for x,y in zip(hi,b)]
            assert all(x<=y for x,y in zip(lo,hi))
    return (F,cols,target,offset,remaining,w,tuple(lo),tuple(hi))
def sector(F,n,rows,target,obs,w,order=None,offset=0):
    cols=tuple(tuple(r[i]%3 for r in rows)+(obs[i]%3,) for i in range(n))
    return cell(canon(F),cols,tuple(target),offset,tuple(range(n)) if order is None else tuple(order),w)
def refine(roots,eps,budget,focus=True,exact_probe_budget=0):
    lo=[Q(0)]*3;hi=lo.copy();heap=[];serial=0;done=0
    def account(c,sign):
        for d in range(3):lo[d]+=sign*c[-2][d];hi[d]+=sign*c[-1][d]
    def push(c):
        nonlocal serial
        if c is None:return
        account(c,1)
        widths=[b-a for a,b in zip(c[-2],c[-1])]
        if max(widths):
            assert c[4];serial+=1;heappush(heap,(-max(widths),serial,c))
    for c in roots:push(c)
    bestlo=lo.copy();besthi=hi.copy()
    while True:
        # Intersect previous certificates and exploit exact zero-sum plane.
        a=[max(lo[d],bestlo[d]) for d in range(3)];b=[min(hi[d],besthi[d]) for d in range(3)]
        bestlo=[max(a[d],-sum(b[j] for j in range(3) if j!=d)) for d in range(3)]
        besthi=[min(b[d],-sum(a[j] for j in range(3) if j!=d)) for d in range(3)]
        choices=[d for d in range(3) if bestlo[d]>=-eps]
        if choices or not heap:return bestlo,besthi,choices,done
        if done>=budget:
            # Retire expensive frontier cells by a bounded exact chart fold.
            # All local free dimensions sum to the ambient nullity, so
            # len(R)*2^nullity dominates the total enumerated local points.
            # Polynomial elimination/CNF evaluation overhead is separate.
            candidates=[]
            d=max(range(3),key=lambda j:bestlo[j])
            for index,(_,sid,c) in enumerate(heap):
                F,cols,t,o,R,w,clo,chi=c
                free=len(R)-len(basis(cols[i][:-1] for i in R))
                cost=max(1,len(R))*(1<<free)
                if cost<=exact_probe_budget:
                    candidates.append(((chi[d]-clo[d])/cost,-cost,-sid,index,free))
            if not candidates:return bestlo,besthi,choices,done
            _,negcost,_,index,free=max(candidates)
            _,_,c=heap.pop(index);heapify(heap);account(c,-1)
            F,cols,t,o,R,w,_,_=c
            exact_probe_budget+=negcost
            ok,C,H,E=component_bounds(F,cols,t,o,R,free,spectral=True)
            assert ok
            a=tuple(w*(3*h-C) for h in H)
            account((F,cols,t,o,R,w,a,a),1)
            continue
        if focus:
            d=max(range(3),key=lambda j:bestlo[j])
            index=max(range(len(heap)),key=lambda i:(heap[i][2][-1][d]-heap[i][2][-2][d],-heap[i][0],-heap[i][1]))
            _,_,c=heap.pop(index);heapify(heap)
        else:_,_,c=heappop(heap)
        account(c,-1);F,cols,t,o,R,w,_,_=c;i=R[0]
        for bit in (0,1):push(cell(restrict(F,i,bit),cols,add(t,cols[i][:-1],-bit),(o+bit*cols[i][-1])%3,R[1:],w))
        done+=1

def pair(F,n,j,sign=None):
    G=list(F)+[tuple((abs(l)+n)*(1 if l>0 else -1) for l in c) for c in F]
    for i in range(j):G.extend(((i+1,-(n+i+1)),(-(i+1),n+i+1)))
    G.extend(((j+1,n+j+1),(-(j+1),-(n+j+1))))
    if sign is not None:G.append(((j+1)*sign,))
    return G

def diff(r):return list(r)+[-x for x in r]
def matrix(n,k,p):return [[p[n-1+i-j] if n-1+i-j<len(p) else 0 for j in range(n)] for i in range(k)]
def coefficient(F,n,k,p,compact=True,symmetric=True):
    A=matrix(n,k,p);roots=[];order=[i for j in range(n) for i in (j,n+j)]
    for j in range(n):
        t=len(p)-n+1+j
        if not 0<=t<k:continue
        for sign in ((1,) if compact and symmetric else (-1,1)):
            # Pair swap preserves the zero-difference prefix and the signed
            # observable: both the first-difference sign and delta reverse.
            w=-Q(6 if compact and symmetric else 3,3**(2*k-t))
            if compact:
                # The donor substitutes y_i=x_i (i<j), y_j=1-x_j.
                # Read the last affine row as an observable, NOT as a pin.
                G,N,rows,target=pair_source(F,n,A[:t+1],first=j)
                roots.append(sector(G+[((j+1)*sign,)],N,rows[:-1],target[:-1],
                    [-sign*a for a in rows[-1]],w,offset=sign*target[-1]%3))
            else:
                roots.append(sector(pair(F,n,j,sign),2*n,[diff(r) for r in A[:t]],(0,)*t,[-sign*x for x in diff(A[t])],w,order))
    return roots

def translation(F,n,k,p,b,compact=True,symmetric=True):
    A=matrix(n,k,p);e=len(b);D=3**(k-e-1);order=[i for j in range(n) for i in (j,n+j)]
    roots=[sector(F,n,A[:e],b,A[e],Q(1,D))]
    for j in range(n):
        if compact:
            G,N,rows,target=pair_source(F,n,A,A[:e],b,first=j)
            # A(x)=A(y), hence swapping the pair preserves the prefix and
            # the observed label. First-difference orientation is free.
            if symmetric:G=G+[((j+1),)]
            roots.append(sector(G,N,rows,target,A[e]+[0]*(N-n),-Q(2 if symmetric else 1,D)))
        else:
            roots.append(sector(pair(F,n,j),2*n,[diff(r) for r in A]+[r+[0]*n for r in A[:e]],(0,)*k+tuple(b),A[e]+[0]*n,-Q(1,D),order))
    return roots

def accepts(F,x):return all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)
def value(S,n,k,p,b=()):
    A=matrix(n,k,p);D=3**(k-len(b));H={}
    if len(p)<n+k-1:
        ans=Q(len(S),3**k)
        for x in S:
            for y in S:
                if x==y:continue
                j=next(i for i in range(n) if x[i]!=y[i]);t=min(k,max(0,len(p)-n+1+j))
                if all(sum(r[i]*(x[i]-y[i]) for i in range(n))%3==0 for r in A[:t]):ans-=Q(1,3**(2*k-t))
        return ans
    for x in S:
        v=tuple(sum(a*z for a,z in zip(r,x))%3 for r in A)
        if v[:len(b)]==tuple(b):H[v]=H.get(v,0)+1
    return Q(sum(h*(2-h) for h in H.values()),D)

def main():
    rng=Random(369);checks=0;success={0:0,4:0,32:0,4096:0};promises=0;baseline={0:0,4:0,32:0,4096:0};descents=0;steps=0;witnesses=0
    for n in range(1,6):
        for _ in range(20):
            F=canon(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,min(n,3)+1))) for _ in range(rng.randrange(6)))
            S=[x for x in product(range(2),repeat=n) if accepts(F,x)];k=rng.randrange(1,4);L=n+2*k-1;eps=Q(1,8*L)
            p=tuple(rng.randrange(3) for _ in range(n+k-1));q=rng.randrange(len(p));e=rng.randrange(k);b=tuple(rng.randrange(3) for _ in range(e))
            for roots,vs in ((coefficient(F,n,k,p[:q]),[value(S,n,k,p[:q]+(d,)) for d in range(3)]),(translation(F,n,k,p,b),[value(S,n,k,p,b+(d,)) for d in range(3)])):
                v=sum(vs)/3;delta=[3*(x-v) for x in vs];assert sum(delta)==0;promises+=v>Q(1,24)
                for budget in success:
                    lo,hi,c,_=refine(roots,eps,budget);assert all(a<=x<=z for a,x,z in zip(lo,delta,hi));assert all(delta[d]>=-eps for d in c);checks+=3
                    success[budget]+=bool(c) and v>Q(1,24)
                    a,z,cc,_=refine(roots,eps,budget,False);assert all(l<=x<=h for l,x,h in zip(a,delta,z));assert all(delta[d]>=-eps for d in cc);checks+=3
                    baseline[budget]+=bool(cc) and v>Q(1,24)
                    if budget==4096:assert c and cc
            # End-to-end original seed descent, on an actually positive root.
            if value(S,n,k,())<=Q(1,24):continue
            P=();B=();descents+=1
            for i in range(L):
                roots=coefficient(F,n,k,P) if len(P)<n+k-1 else translation(F,n,k,P,B)
                _,_,c,_=refine(roots,eps,4096);assert c;d=c[0]
                if len(P)<n+k-1:P+=(d,)
                else:B+=(d,)
                steps+=1;assert value(S,n,k,P,B)>0
            # Reference checks terminal uniqueness; not a polynomial witness producer.
            A=matrix(n,k,P);W=[x for x in S if tuple(sum(a*z for a,z in zip(r,x))%3 for r in A)==B];assert len(W)==1;witnesses+=1
    print(dict(fixtures=100,contrast_bounds=checks,positive_parents=promises,certified=success,global_width_baseline=baseline,descents=descents,steps=steps,reference_unique_witnesses=witnesses))
if __name__=='__main__':main()
