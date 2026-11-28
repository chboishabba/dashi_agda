"""BR302 time-consistent boundary comparator, not physical exterior conditions.
Use one-sided outer derivatives; evolve every node, including matter.
"""
import argparse
import inspect
import numpy as np
import check_hopf369_br297_299_history_regions as regions
import check_hopf369_br287_289_g4_audit as audit
import check_hopf369_br283_284_g4_coupled as d

def derivative(a,axis,dx):
    return np.gradient(a,dx,axis=axis,edge_order=2)

def second(a,axis,dx):
    out=(np.roll(a,1,axis=axis)-2*a+np.roll(a,-1,axis=axis))/dx**2
    f=np.moveaxis(a,axis,0); z=np.moveaxis(out,axis,0)
    z[0]=(2*f[0]-5*f[1]+4*f[2]-f[3])/dx**2
    z[-1]=(2*f[-1]-5*f[-2]+4*f[-3]-f[-4])/dx**2
    return out

def run(n,steps,dt):
    original_run=d.run; original_acc=d.acc
    # BR240 acceleration uses one-sided first and mixed derivatives already.
    src=inspect.getsource(d.vac.acceleration)
    old='(np.roll(g,1,axis=i-1)-2*g+np.roll(g,-1,axis=i-1))/dx**2'
    assert old in src
    ns=dict(original_acc.__globals__,edge_second=second)
    exec(src.replace(old,'edge_second(g,i-1,dx)'),ns)
    d.acc=ns['acceleration']
    src=inspect.getsource(original_run)
    old='du-=(np.roll(fi,-1,axis=i)-np.roll(fi,1,axis=i))/(2*dx)'
    assert old in src
    src=src.replace(old,'du-=derivative(fi,i,dx)')
    start=src.index('        for i in range(3):\n            for k in (0,-1):')
    end=src.index('        return vv,a,du,m,source',start)
    src=src[:start]+src[end:]
    ns=dict(vars(d),derivative=derivative)
    exec(src,ns)
    # regions.capture calls inspect.getsource; avoid dynamically compiled source
    # lookup by capturing directly in the replay function here.
    records=[]
    def save(g,v,U,dx):records.append((g.copy(),v.copy(),U.copy(),dx))
    src=src.replace('    b0=divB(U);','    save(g,v,U,dx)\n    b0=divB(U);').replace('margin=min(margin,m,mm);','save(g,v,U,dx);margin=min(margin,m,mm);')
    old_replay=audit.run
    def replay(nn,ss,dd):
        ns=dict(vars(d),derivative=derivative,save=save)
        exec(src,ns);ns['run'](nn,ss,dd)
    try:
        audit.run=replay
        regions.history.run(n,steps,dt)
        k=steps//2;g,v,U,dx=records[k];gm,vm,_,_=records[k-1];gp,vp,_,_=records[k+1]
        vfd=(gp-gm)/(2*dt);afd=(gp-2*g+gm)/dt**2
        field=regions.evaluate(records[k],afd,vfd)
        idx=np.indices((n,)*3);dist=np.min(np.minimum(idx,n-1-idx),axis=0)
        for label,mask in [('boundary-jet',dist==0),('outer-band',dist==1),('core',dist>=2)]:
            err=np.max(abs(vfd-v)[mask]);print('BR302',n,label,'velocity discrepancy',err,flush=True)
            if label!='boundary-jet':print('BR302',n,label,'H M C reduced',np.max(field[mask],axis=0).tolist(),flush=True)
        assert np.max(abs(vfd-v)[dist==0])<1e-5
    finally:
        d.acc=original_acc;audit.run=old_replay
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=7);p.add_argument('--steps',type=int,default=4);p.add_argument('--dt',type=float,default=.001);a=p.parse_args();run(a.n,a.steps,a.dt)
