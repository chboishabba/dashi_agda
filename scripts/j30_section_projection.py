#!/usr/bin/env python3
"""J30: rigorous correlated final U-off event state via affine section projection.

Exact rational/source-owned J29 state; only proves sixth J24 original box if assertions pass.
"""
import sys,json
from pathlib import Path
from fractions import Fraction as F
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.path.insert(0,str(HERE))
import j29_u_only as y
z=y.z; w=y.w; c=y.c; p=y.p; I=y.I;S=y.S

def analyze(data, target='4.9287514068571'):
    t0=F(data['t']);tref=F(target);h=tref-t0
    assert F(0)<h<F('.006')
    # Baseline exact affine enclosure at the reference time, with all-time Picard proof.
    ref=y.step(data,h,bracket_u=True)
    assert F(ref['t'])==tref
    root=list(map(F,ref['root']))
    noise=list(map(F,ref['symbol_radii']))
    rem=list(map(F,ref['remainder']))
    H=[[w.decode(v) for v in row] for row in ref['H']]
    # Preserved validated sixth event bracket, exact rational mean value tightening.
    receipt=json.loads((ROOT/'receipts/J29_SIXTH_MVT_REFINED.json').read_text())
    tl,tr=map(F,receipt['mean_value_refined_bracket'])
    assert tl<tref<tr
    # Entire proven virtual U-active interval through root; actual flow matches it up to root.
    hR=tr-t0;hL=tl-t0
    P,eps=z.residual_uv(52,t0,list(map(F,data['root'])),hR,True,False)
    old_noise=list(map(F,data['symbol_radii']))
    old_rem=[w.up(q) for q in data['remainder']]
    old_H=[[w.decode(q) for q in row] for row in data['H']]
    old_err=[sum((w.mag(a)*n for a,n in zip(row,old_noise)),old_rem[i]) for i,row in enumerate(old_H)]
    for rr in ('.00001','.0001','.001'):
        R=F(rr)
        tube=[c.evalpoly(poly,I(0,hR)).expand(R) for poly in P]
        J=z.J_signed(tube,True,False)
        E=c.bound_exp(z.majorant(J),hR,old_err,eps)
        slope=y.guard_slope_taylor(P,J,E,eps,hR)
        if all(e<R for e in E) and slope.b<0 and (tube[3]-tube[4]-p['Vd']).b<0 and (tube[4]-p['Voff']).a>0:
            break
    else:raise AssertionError('no validated event tube for projection')
    # More precise state tube restricted to tight event time; same all-time E conservative.
    event_poly=[c.evalpoly(row,I(hL,hR)).expand(e) for row,e in zip(P,E)]
    fs=z.f_rhs(tl,tr,event_poly,True,False)
    gs=slope  # strictly negative derivative of original g=u-b-Vd on entire interval
    assert gs.b<0
    # Mean value theorem: x_i(te)=x_i(tref) - f_i(s_i) * g(tref)/g'(theta).
    # x_i(tref) = root_i + H_i xi + err_i; g(tref) = centre_g+(H_u-H_b)xi+err_g.
    gc=I(root[2]-root[4])-p['Vd']
    Hg=[a-b for a,b in zip(H[2],H[4])]
    rg=rem[2]+rem[4]
    event=[]; diagnostics=[]
    for i,fi in enumerate(fs):
        ratio=fi/gs
        # Freeze ratio at an exact rational midpoint to retain affine cancellation.
        # The difference from the true MVT ratio is bounded separately.
        rpoint=F(ratio.a+ratio.b,2*S)
        rerr=w.mag(ratio-I(rpoint))
        line=[hi-I(rpoint)*hg for hi,hg in zip(H[i],Hg)]
        gmax=w.mag(gc)+sum((w.mag(a)*n for a,n in zip(Hg,noise)),rg)
        error=sum((w.mag(a)*n for a,n in zip(line,noise)),rem[i]+abs(rpoint)*rg+rerr*gmax)
        nominal=I(root[i])-I(rpoint)*gc
        box=nominal.expand(error)
        event.append(box)
        diagnostics.append(dict(i=i,nominal=[float(nominal.a/S),float(nominal.b/S)],half_error=float(error),ratio=[float(ratio.a/S),float(ratio.b/S)],event=[float(box.a/S),float(box.b/S)]))
    j24=json.loads((ROOT/'Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json').read_text(),parse_float=F,parse_int=F)['events'][5]
    comparison=[q.subset(I(x-F('.0001'),x+F('.0001'))) for q,x in zip(event,j24['x'])]
    print('ref',float(tref),'bracket',[float(tl),float(tr)],'slope',[float(gs.a/S),float(gs.b/S)],'root membership',comparison,flush=True)
    for d in diagnostics:print(d,flush=True)
    result=dict(status='J30_SECTION_PROJECTED_SIXTH_BOX_PASS' if all(comparison) else 'J30_SECTION_PROJECTED_SIXTH_BOX_INCOMPLETE',projected_event_state=[[str(x.a),str(x.b)] for x in event],inside_original_J24_sixth_box=comparison,centres=j24['x'],t_ref=str(tref),root_time_bracket=[str(tl),str(tr)],original_J29_last_event_source=receipt['status'],slope_bounds=[str(gs.a),str(gs.b)],diagnostics=diagnostics,exact_periodic_orbit_proved=False)
    (ROOT/'receipts/J30_SECTION_PROJECTION.json').write_text(json.dumps(result,indent=2,default=str)+'\n')
    return result
if __name__=='__main__':
    r=analyze(json.loads((ROOT/'receipts/J29_U_60.json').read_text()))
    print('status',r['status'])
