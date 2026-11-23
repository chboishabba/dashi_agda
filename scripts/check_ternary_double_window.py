"""Two finite temporal windows, phase-bearing scattering and memory controls.

Normalized, source-driven open 3x3 and 3x3x3 models, not ITO measurements.
Uses exact work-conserving discrete-gradient polarization with separately
accounted source resistor and material-modulation work.
"""
import numpy as np
import sympy as sp
from check_ternary_temporal_material import solve, A, incidence

PERIOD=12
WIDTH=2
HEIGHT=.30


def window(start, width=WIDTH, period=PERIOD):
    result=np.zeros(period)
    for offset in range(width):
        result[(start+offset)%period]=1.
    return result


def coherent(a):
    return np.fft.fft(np.asarray(a,dtype=float))/len(a)


def run_case(dim,beta,second_start):
    base=solve(dim,beta,0.,0.,period=PERIOD,return_history=True)
    first=window(2);second=window(second_start)
    assert not np.any(first*second)
    prof1=A+HEIGHT*first;prof2=A+HEIGHT*second;both=A+HEIGHT*(first+second)
    x=solve(dim,beta,0.,0.,period=PERIOD,material_profile=prof1,return_history=True)
    y=solve(dim,beta,0.,0.,period=PERIOD,material_profile=prof2,return_history=True)
    xy=solve(dim,beta,0.,0.,period=PERIOD,material_profile=both,return_history=True)
    n=3**dim;m=incidence(dim).shape[1]
    # Polarization is the sensitive state carrier; near-site E can be much smaller.
    extract=lambda r:r['midpoints'][:,n+m] - base['midpoints'][:,n+m]
    f1=coherent(extract(x));f2=coherent(extract(y));fpair=coherent(extract(xy))
    k=1
    relative_nonadd=abs(fpair[k]-f1[k]-f2[k])/max(abs(fpair[k]),abs(f1[k])+abs(f2[k]),1e-30)
    wave=coherent(window(0))[k]
    # The TWO window envelopes have a known exact DFT interference factor.
    ideal=(HEIGHT*wave)*(np.exp(-2j*np.pi*k*2/PERIOD)+np.exp(-2j*np.pi*k*second_start/PERIOD))
    assert abs(coherent(HEIGHT*(first+second))[k]-ideal)<1e-14
    assert abs(fpair[k])>1e-10,(dim,beta,second_start,fpair[k])
    for case in (base,x,y,xy):
        assert case['defect']<1e-9 and case['ledger']<1e-9
        assert abs(case['external']+case['modulation']-case['source_loss']-case['load']-case['relax'])<1e-9
    assert abs(base['modulation'])<1e-13
    assert abs(x['modulation'])>1e-9
    assert abs(y['modulation'])>1e-9
    assert abs(xy['modulation'])>1e-9
    return dict(coherent=fpair[k],sum_single=f1[k]+f2[k],nonadd=relative_nonadd,
                envelope=ideal, mod=xy['modulation'],sideband=abs(fpair[2]),
                signal=extract(xy))


def main():
    w,T,tau=sp.symbols('w T tau',real=True,nonzero=True)
    single=2*sp.sin(w*T/2)/w
    slit=single*(1+sp.exp(-sp.I*w*tau))
    assert sp.trigsimp(sp.expand_complex(slit*sp.conjugate(slit))-single**2*(2+2*sp.cos(w*tau)))==0
    checks=1
    for dim in (2,3):
        for beta in (0.,.45):
            a=run_case(dim,beta,6)
            b=run_case(dim,beta,8)
            assert abs(a['coherent']-b['coherent'])>1e-10;checks+=1
            assert abs(a['envelope']-b['envelope'])>1e-6;checks+=1
            assert a['nonadd']<.10 and b['nonadd']<.10,(dim,beta,a['nonadd'],b['nonadd']);checks+=1
            assert np.isfinite(a['sideband']) and np.isfinite(b['sideband']);checks+=1
            # Each response has memory: nonzero state perturbation outside windows.
            mask=np.maximum(window(2),window(6))
            assert max(abs(a['signal'][mask==0]))>1e-10;checks+=1
            print(f'{dim}D beta={beta}: separation 4 -> {a["coherent"]:.6g}; 6 -> {b["coherent"]:.6g}; nonadd={a["nonadd"]:.4g},{b["nonadd"]:.4g}; modulation work={a["mod"]:.6g}')
    print(f'{checks}/{checks} PASS finite temporal windows; SymPy {sp.__version__}')


if __name__=='__main__':main()
