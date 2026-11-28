"""BR295 nonlinear replay of BR293 with BR294's three-mode lift."""
import argparse
import inspect
import check_hopf369_br293_cmc_york as donor


def run(n,lift):
    s=inspect.getsource(donor.run).replace('BR293','BR295')
    s=s.replace('lap,J,pairs=base.operators(n,dx); lap=lap[:,ids]; J=', 'lap,J,pairs=base.operators(n,dx); lap=lap[:,ids]; N=n**3; outer=np.setdiff1d(np.arange(N),ids); Jo=J[:,np.concatenate([outer+i*N for i in range(6)])]; J=')
    s=s.replace('rank=np.linalg.matrix_rank(A.toarray(),tol=1e-10)', '''rank=np.linalg.matrix_rank(A.toarray(),tol=1e-10)
    c=np.zeros(3)
    if lift:
        assert n%2==1 and rank==3*m-3
        p=np.zeros((n-2,)*3);p[::2,::2,::2]=1;Z=np.kron(np.eye(3),p.reshape(-1,1));Z/=np.linalg.norm(Z,axis=0)
        Q=kron(csr_matrix(P@np.diag(1/weights)),eye(len(outer)))@Jo.T@Z; B=Jo@Q; G=Z.T@B
        assert np.linalg.matrix_rank(G)==3
    else:
        assert n%2==0 and rank==3*m
        Q=np.zeros((6*len(outer),3))''')
    s=s.replace('def state(u,w):','def state(u,w,c):').replace('g=g0.copy();', '''qout=(Q@c).reshape(6,-1)
        assert np.max(abs(diag@qout))<1e-12
        for k,(i,j) in enumerate(pairs):
            Y.reshape(N,3,3)[outer,i,j]+=qout[k]
            if i!=j:Y.reshape(N,3,3)[outer,j,i]+=qout[k]
        g=g0.copy();''')
    s=s.replace('v=base.jets(g,K,dx);','''if lift:K.reshape(N,3,3)[outer]=(Y/psi[...,None,None]**2+tau[...,None,None]*g[...,1:,1:]/3).reshape(N,3,3)[outer]
        v=base.jets(g,K,dx);''')
    s=s.replace('state(u,w);','state(u,w,c);').replace('range(16)','range(24)').replace('dw=lsqr(A,rhs,','dc=np.linalg.solve(G,Z.T@rhs) if lift else np.zeros(3);dw=lsqr(A,rhs-B@dc if lift else rhs,').replace('A@dw-rhs','A@dw+(B@dc if lift else 0)-rhs').replace('state(u+a*du,w+a*dw)','state(u+a*du,w+a*dw,c+a*dc)').replace('u+=a*du;w+=a*dw;','u+=a*du;w+=a*dw;c+=a*dc;')
    s=s.replace('and np.array_equal(K[mask],K0[mask])','and (lift or np.array_equal(K[mask],K0[mask]))').replace("'boundary fixed',True","'boundary K correction',np.max(abs(K[mask]-K0[mask]))").replace('assert np.linalg.norm(r)<=np.linalg.norm(initial) and margin>0','assert np.max(abs(r))<1e-8 and max(values[:2])<2e-8 and margin>0')
    ns=dict(vars(donor),lift=lift);exec(s,ns);ns['run'](n)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=6);p.add_argument('--lift',action='store_true');a=p.parse_args();run(a.n,a.lift)
