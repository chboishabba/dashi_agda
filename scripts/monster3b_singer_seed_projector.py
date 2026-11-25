#!/usr/bin/env python3
"""Source-only, good-prime certificate for the compact char0 seed projector.

The actual target must first have a genuine integral modular Hom attachment.
This tests source coefficients and emits an exact expression recipe, not
numerical characteristic-zero Monster matrices or an evaluated determinant.
"""
import numpy as np
from monster3b_singer_cyclic_hom import orbit, wheel, word, rank_mod, mm, ident, require, W, P
from monster3b_lindsey_actual_mod31_join import source_matrices, dual
from monster3b_actual_projective_sym2_intertwiner import inverse

def detmod(A):
    A=A.copy()%P;d=1;n=len(A)
    for i in range(n):
        j=next((j for j in range(i,n) if A[j,i]),None)
        if j is None:return 0
        if i!=j:A[[i,j]]=A[[j,i]];d=-d
        a=int(A[i,i]);d=d*a%P
        A[i+1:]=(A[i+1:]-((A[i+1:,i]*pow(a,-1,P))%P)[:,None]*A[i])%P
    return d%P

def recipe(data,q):
    T=source_matrices(data,q);U={g:dual(T[g],g=="C") for g in T};out={}
    for n,src in ((12,T),(78,U)):
        plus={g:src[g][:n,:n] for g in ("D","E")}
        minus={g:src[g][n:,n:] for g in ("D","E")}
        B,words,r=orbit(plus);Gp,_=wheel(plus,n);Gm,_=wheel(minus,n)
        wp=np.stack([word({**plus,"G":Gp},w) for w in words])
        wm=np.stack([word({**minus,"G":Gm},w) for w in words])
        wi=np.stack([inverse(M) for M in wp])
        Bm=wm[:,:,0].T;Bmi=inverse(Bm);Bpi=inverse(B)
        S=np.zeros((n,n),dtype=np.int64)
        for g in ("D","E"):
            coeff=mm(Bpi,mm(plus[g],B));conj=mm(Bmi,mm(minus[g],Bm));gi=inverse(plus[g])
            for i in range(n):
                R=(mm(plus[g],wp[i])-np.tensordot(coeff[:,i],wp,axes=1))%P
                Ra=(mm(wi[i],gi)-np.tensordot(conj[:,i],wi,axes=1))%P
                require(not np.any(R[:,0]),"source residual does not kill marked seed")
                S=(S+mm(Ra,R))%P
        ranks=[rank_mod(S),rank_mod(mm(S,S))]
        require(ranks==[n-1,n-1],"source seed projector has bad reduction")
        # S kills e0. Adding e0*e0^T gives eigenvalue 1 on its kernel
        # and does not change its induced operator on the quotient.
        J=S.copy();J[0,0]=(J[0,0]+1)%P
        p0=(-1)**(n-1)*detmod(J)%P
        require(p0!=0,"source projector denominator not a local unit")
        out[str(n)]={**r,"word_basis":words,"source_seed":"e0","macro_G":W*3,
            "right_action_words":True,"ranks_S_S2_mod31":ranks,"p0_mod31":p0,
            "polynomial_degree":n-1,"residual_count":2*n,
            "exact_B":"columns A(w_i)e0 over Q(zeta); invert using original ordinary matrices",
            "exact_R":"R_hi(L)=L(h)L(w_i)-sum_j (B^-1 A(h) B)_ji L(w_j)",
            "star":"invert every literal group word and conjugate each Q(zeta) coefficient",
            "exact_S":"sum_hi R_hi^* R_hi; source S_A evaluated in A, target S_L in L",
            "exact_p":"det(t I_n - S_A)/t over Q(zeta), using original source n-dimensional matrices",
            "projector":"P_L=p(S_L)/p(0)",
            "vacuum_sector":"(I-L(C^2))/2" if n==12 else "(I+L(C^2))/2",
            "positive_seed":"y=P_L P_sector P_zeta P_B lift(ambient_rows)^T lift(basis_coordinates[:,0])",
            "positive_F":"columns L(w_i)y multiplied on right by B^-1",
            "negative_F":"L(C)_(plus->minus) F_plus A(C)_(plus->minus)^-1"}
    return out
if __name__=="__main__":
    import json
    from pathlib import Path
    source=Path(__file__).resolve().parents[1]/"Docs/support/reference/Monster3BLindseyOrdinaryCD20261124.json"
    data=json.loads(source.read_text())
    for q in range(3):
        r=recipe(data,q)
        print(q,{n:{k:x[k] for k in ("ranks_S_S2_mod31","p0_mod31","polynomial_degree")} for n,x in r.items()})
