"""Evolve both BR295 constraint branches without subsequent projection."""
import argparse, inspect
import check_hopf369_br295_cmc_lift as donor
import check_hopf369_br287_289_g4_audit as audit

def run(n,steps,dt):
    # Replay the actual donor and expose its accepted state, not a new solve.
    s=inspect.getsource(donor.run)
    marker="ns=dict(vars(donor),lift=lift);exec(s,ns);ns['run'](n)"
    assert marker in s
    s=s.replace(marker,"ns=dict(vars(donor),lift=lift);exec(s+'\\n    return g,v,U,dx\\n',ns);return ns['run'](n)")
    ns=dict(vars(donor));exec(s,ns)
    initial=ns['run'](n,bool(n%2))
    old=audit.d.initial
    try:
        audit.d.initial=lambda nn: initial if nn==n else old(nn)
        audit.run(n,steps,dt)
    finally:audit.d.initial=old
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=6);p.add_argument('--steps',type=int,default=4);p.add_argument('--dt',type=float,default=.001);a=p.parse_args();run(a.n,a.steps,a.dt)
