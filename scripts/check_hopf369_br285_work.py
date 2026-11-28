"""Retain physical port dissipation and numerical entropy defect separately."""
import inspect
import numpy as np
import check_hopf369_br241_metric_consumer as mat
from check_hopf369_br277_278_actual_reciprocal import assembly

def run():
    def assemble(g):return assembly(g,np.zeros_like(g))[0],mat.assembly(g)[1]
    source=inspect.getsource(mat.material)
    source=source.replace('worst=0.; hwtotal=0.; vwtotal=0.','worst=0.; hwtotal=0.; vwtotal=0.; heat=0.; numerical=0.; E0=energy(n0,x,H,V)')
    marker='        n0,x,surf,H,V=nn,xn,sn,H1,V1; hwtotal+=hw; vwtotal+=vw'
    assert marker in source
    source=source.replace(marker,marker+'\n        heat+=diss; numerical+=rem\n        closure=energy(n0,x,H,V)+heat+numerical-E0-hwtotal-vwtotal\n        assert abs(closure)<1e-8\n        print("BR285",heat,numerical,closure,flush=True)')
    ns=dict(vars(mat),assembly=assemble);exec(source,ns);ns['material'](11)
if __name__=='__main__':run()
