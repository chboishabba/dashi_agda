#!/usr/bin/env python3
"""S4c.6: situated linear consumers of native flux histories, not clinical assays."""
from sympy import Matrix, eye, zeros, __version__
from reactive_pnp_369 import POINTS, BONDS


def check():
    B=zeros(len(POINTS),len(BONDS))
    for j,(a,b) in enumerate(BONDS):
        B[a,j],B[b,j]=-1,1
    A=B[:26,:]
    K=A.T*(A*A.T).inv(method='DM')
    Z=Matrix.hstack(*A.nullspace())
    G=eye(54)[[i for i in range(54) if i not in A.rref()[1]],:]
    H=G*(eye(54)-K*A)
    assert A*K==eye(26) and H*Z==eye(28)
    assert K*A+Z*H==eye(54)
    # Two chronological windows. The retained coarse observation is SUM divergence.
    coarse=A.row_join(A)
    total=eye(54).row_join(eye(54))
    N=Matrix.vstack(Z,zeros(54,28)).row_join(Matrix.vstack(zeros(54,28),Z))
    N=N.row_join(Matrix.vstack(K,-K))
    assert coarse*N==zeros(26,82) and N.to_DM().rank()==82
    e=eye(54)[0,:]
    # Fixed spatial location, plus context-dependent consumer windows.
    F={
        'aggregate_divergence': A[0,:].row_join(A[0,:]),
        'integrated_local_edge': e.row_join(e),
        'early_local_edge': e.row_join(zeros(1,54)),
        'late_local_edge': zeros(1,54).row_join(e),
        'early_divergence': A[0,:].row_join(zeros(1,54)),
        'early_and_late_edge': Matrix.vstack(e.row_join(zeros(1,54)),zeros(1,54).row_join(e)),
    }
    # Use section S of the retained coarse observer, not an invented measurement.
    S=Matrix.vstack(K,zeros(54,26))
    assert coarse*S==eye(26)
    results={}
    for name,f in F.items():
        R=f-f*S*coarse
        rank=(f*N).to_DM().rank()
        assert R.to_DM().rank()==rank
        # Independent residual rows, exact reconstruction using pivot columns.
        ix=R.T.rref()[1]
        Q=R[list(ix),:] if ix else zeros(0,108)
        if ix:
            piv=list(Q.rref()[1])
            D=R[:,piv]*Q[:,piv].inv(method='DM')
        else:
            D=zeros(f.rows,0)
        assert f==f*S*coarse+D*Q
        # Every retained row can be accumulated by its window-specific coefficients.
        v=Matrix([i%7-3 for i in range(108)])
        streamed=Q[:,:54]*v[:54,0]+Q[:,54:]*v[54:,0]
        assert f*v==f*S*coarse*v+D*streamed
        results[name]=rank
    assert results=={'aggregate_divergence':0,'integrated_local_edge':1,
                     'early_local_edge':1,'late_local_edge':1,
                     'early_divergence':1,'early_and_late_edge':2}
    # Same aggregate flux (stronger than same aggregate divergence), distinct early target.
    z=next(Z[:,i] for i in range(28) if (e*Z[:,i])[0]!=0)
    collision=Matrix.vstack(z,-z)
    assert total*collision==zeros(54,1)
    assert F['early_local_edge']*collision != zeros(1,1)
    # Even keeping both windows' cycle coordinates cannot recover early divergence.
    g=K[:,0]
    hidden=Matrix.vstack(g,-g)
    assert total*hidden==zeros(54,1) and H*g==zeros(28,1)
    assert F['early_divergence']*hidden==Matrix([1])
    # Spatial region net inward flux descends through divergence with zero cycle residue.
    region=Matrix([[int(p[0]==-1) for p in POINTS]])
    L=region*B
    assert L*Z==zeros(1,28)
    # Pullback error budget: exact coefficient identity for each window.
    for f in F.values():
        for offset in (0,54):
            l=f[:,offset:offset+54]
            assert l==l*K*A+l*Z*H
    print('SymPy',__version__,'situated ranks',results)
    print('6/6 exact decoders; 2/2 context collisions; region cut and 12/12 pullbacks PASS')


if __name__=='__main__':
    check()
