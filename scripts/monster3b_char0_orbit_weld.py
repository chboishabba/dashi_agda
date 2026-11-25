"""Exact Q(zeta3) source and target orbit maps, without a target modular lift."""
from sympy import QQ
from sympy.polys.matrices import DomainMatrix as DM
from itertools import combinations_with_replacement
from functools import lru_cache

K=QQ.cyclotomic_field(3); Z=K.unit


def require(ok,msg):
    if not ok:raise ValueError(msg)


def mat(rows):return DM(rows,(len(rows),len(rows[0])),K).to_dense()
def eye(n):return DM.eye(n,K).to_dense()
def col(v):return mat([[x] for x in v])
def columns(xs):return mat(xs).transpose()
def pairs(n):return list(combinations_with_replacement(range(n),2))


def sym2(A):
    a=A.to_list();ix=pairs(A.shape[0]);zero=K.zero
    return mat([[a[u][i]*a[v][j]+(a[v][i]*a[u][j] if u!=v else zero)
                 for i,j in ix] for u,v in ix])


def source(data,q):
    require(data.get('schema')=='monster3b-lindsey-ordinary-CD-compact-v1' and q in (0,1,2),'source schema/phase')
    def ev(g,s):
        r=data[g];rows=r['numerator_rows'];d=K.convert(r['denominator'])
        require(len(rows)==12 and all(len(a)==24 for a in rows),'source dimensions')
        return mat([[(K.convert(a[i])+Z**s*K.convert(a[i+1]))/d for i in range(0,24,2)] for a in rows]).transpose()
    C={s:ev('C',s) for s in (1,2)}
    D={s:ev('D',s).scalarmul(Z**(s*q)) for s in (1,2)}
    E={s:C[s].inv()*D[3-s]*C[s] for s in (1,2)}
    S={g:a for g,a in (('C',C),('D',D),('E',E))}
    U={g:{s:sym2(a[s].inv().transpose()) for s in (1,2)} for g,a in S.items()}
    return {12:S,78:U}


def word_chart(ops):
    n=ops['D'].shape[0]; A=dict(ops)
    A['d']=A['D'].inv();A['e']=A['E'].inv()
    @lru_cache(None)
    def word(w):return A[w[-1]]*word(w[:-1]) if w else eye(n)
    A['G']=word('DEdeDeDEDEdedEd'*3)
    return word


def exact_orbit(source_ops,target_ops,words,index):
    """F maps ordinary -> actual, selecting a nonzero exact target seed."""
    n=source_ops['D'].shape[0];v=eye(n).extract(list(range(n)),[0])
    A=word_chart(source_ops);L=word_chart(target_ops)
    B=columns([(A(w)*v).transpose().to_list()[0] for w in words]);Bi=B.inv()
    c=(Bi*source_ops['D']*B).extract(list(range(n)),[index]).to_list()
    R=target_ops['D']*L(words[index])
    for w,a in zip(words,c):
        if a[0]:R=R-L(w).scalarmul(a[0])
    N=R.nullspace();require(N.shape==(1,n),'actual exact seed nullity')
    y=N.transpose()
    T=columns([(L(w)*y).transpose().to_list()[0] for w in words])
    F=T*Bi;Fi=F.inv()
    require(all(F*source_ops[g]==target_ops[g]*F and source_ops[g]*Fi==Fi*target_ops[g] for g in ('D','E')),'exact source generator mismatch')
    return F,Fi


def coordinates(B,Y):
    _,piv=B.transpose().rref();n=B.shape[1]
    require(len(piv)==n,'singular exact chart')
    cols=list(range(Y.shape[1]));X=B.extract(list(piv),list(range(n))).inv()*Y.extract(list(piv),cols)
    require(B*X==Y,'exact ambient block residual')
    return X


def signed_from_positive(D,E,J):
    """Negative basis is L(C) applied to the positive basis; right-action words."""
    I=eye(J.shape[0]);require(J*J==I,'positive parity square')
    require(J*D==D*J and J*E==E*J,'positive parity not central')
    return {'C':{1:I,2:J},'D':{1:D,2:E},'E':{1:E,2:J*D*J}}


def signed_weld(actual,ordinary,orbits):
    """actual C,D,E are 90D phase maps; source ordinary is 12/78.
    C is indexed by source phase. Return actual->ordinary & inverse.
    """
    J={s:actual['C'][3-s]*actual['C'][s] for s in (1,2)}
    n=J[1].shape[0];I=eye(n)
    require(all(J[s]*J[s]==I for s in (1,2)),'actual C4')
    basis={d:{s:(J[s]+I.scalarmul(K.convert(1 if d==12 else -1))).nullspace().transpose() for s in (1,2)} for d in (12,78)}
    out={}
    for d,S in ordinary.items():
        require(all(basis[d][s].shape==(n,d) for s in (1,2)),'actual sign-sector rank')
        L={g:{s:coordinates(basis[d][3-s if g=='C' else s],a[s]*basis[d][s]) for s in (1,2)} for g,a in actual.items()}
        words,index=orbits[d]
        Fp,_=exact_orbit({g:S[g][1] for g in ('D','E')},{g:L[g][1] for g in ('D','E')},words,index)
        F={1:Fp,2:L['C'][1]*Fp*S['C'][1].inv()}
        for g in ('C','D','E'):
            for s in (1,2):
                t=3-s if g=='C' else s
                require(F[t]*S[g][s]==L[g][s]*F[s],'full signed characteristic-zero generator weld')
        out[d]={s:basis[d][s]*F[s] for s in (1,2)}
    maps={}
    for s in (1,2):
        F=out[12][s].hstack(out[78][s]); maps[s]=(F.inv(),F)
    return maps


def serialize(A):
    return [[list(map(str,([K.dom.zero]*(2-len(x.to_list()))+x.to_list())[::-1])) for x in row] for row in A.to_list()]
