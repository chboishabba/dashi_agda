#!/usr/bin/env python3
"""J29 exact two-track tube + affine-noise interval matrix transport.

The flow tube is proved with monotone |J| majorant over [0,h]. The signed
Peano-Baker matrix is used *only for the endpoint*, carrying original uncertain
coordinates as affine labelled symbols across all steps. Exact integer outward
rounding 1e30. Endpoint errors carry both labelled linear and residual terms.
"""
from fractions import Fraction as F
import sys,json,argparse
sys.set_int_max_str_digits(200000)
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent if HERE.name=='scripts' else HERE
sys.path.insert(0,str(HERE if HERE.name=='scripts' else HERE/'scripts'))
import check_smith_filsinger_j28b_signed_peano_baker_20261123 as v
c=v.c;I=v.I;S=v.S

def mag(x): return F(max(abs(x.a),abs(x.b)),S)
def up(x):
    v=F(x);return F((v.numerator*S+v.denominator-1)//v.denominator,S)

def decode(x):
    return I(int(x[0]),int(x[1]),raw=True)

def encode(x):return [str(x.a),str(x.b)]

def initialize(inp):
  x=json.loads(Path(inp).read_text())
  assert x['status']=='J28B_PASS_CORRELATED_SPARK_ON_HANDOFF'
  return dict(status='J29_AFFINE_START',t=x['t'],nsteps=0,
              root=x['root'],symbol_radii=[str(up(z)) for z in x['delta']],remainder=['0']*9,
              H=[[encode(I(int(i==j))) for j in range(9)] for i in range(9)],
              source_J28B_handoff=x['status'])

def step(x,h=F('.01'),force_radius=None):
  t=F(x['t']);root=list(map(F,x['root']));h=F(h)
  noise=list(map(F,x['symbol_radii']))
  rem=[up(a) for a in x['remainder']]
  H=[[decode(z) for z in row] for row in x['H']]
  envelope=[sum((mag(m)*w for m,w in zip(row,noise)),rem[i]) for i,row in enumerate(H)]
  P,eps=v.j27.residual_v(52,t,root,h)
  radii=['.000001','.00001','.0001','.001','.01'] if force_radius is None else [str(force_radius)]
  diagnostics=[]
  for r in radii:
    R=F(r)
    X=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
    gu,gv,gs=c.guards(X)
    A=v.j27.get_A_v(X)
    Eflow=c.bound_exp(A,h,envelope,eps) # monotone all-time, NOT signed end bound
    ok=(all(e<R for e in Eflow) and gu.b<0 and gv.a>0 and gs.a>0)
    diagnostics.append((r,float(max(Eflow)),float(gu.b/S)))
    if ok:break
  if not ok:raise AssertionError(("No validated flow tube",str(t),diagnostics))
  J=v.jsigned(X)
  Phi,L,tail=v.exp_bound_signed(J,h,N=8) # at *endpoint* h only
  Hnew=v.mmul(Phi,H)
  forcing=c.bound_exp(A,h,[F(0)]*9,eps)
  residual=[sum((mag(a)*b for a,b in zip(row,rem)),f) for row,f in zip(Phi,forcing)]
  endpoint=[c.evalpoly(row,I(h)) for row in P]
  root_next, roundoff=c.rational_recenter(endpoint)
  rem_next=[up(a+b) for a,b in zip(residual,roundoff)]
  final_err=[sum((mag(a)*b for a,b in zip(row,noise)),r) for row,r in zip(Hnew,rem_next)]
  # Signed endpoint propagation must still be safely enclosed in monotone full-time tube
  assert all(e<=R for e in final_err),(t,R,max(final_err))
  return dict(status='J29_AFFINE_VALIDATED_STEP',t=str(t+h),nsteps=x['nsteps']+1,
              root=list(map(str,root_next)),symbol_radii=list(map(str,noise)),
              remainder=list(map(str,rem_next)),H=[[encode(z) for z in row] for row in Hnew],
              last=dict(radius=str(R),max_fulltime_error=float(max(Eflow)),
                        max_endpoint_error=float(max(final_err)),
                        max_initial_symbol_error=float(max(envelope)),
                        max_remainder=float(max(rem_next)),
                        max_peano_tail=float(tail),
                        lower_V=float(gv.a/S),upper_U=float(gu.b/S),lower_spark=float(gs.a/S)),
              full_step_validated_by_nonnegative_majorant=True,
              signed_propagator_used_only_at_endpoint=True)

def advance(data,count):
 x=data;out=[]
 for i in range(count):
  x=step(x)
  out.append(x['last'])
  print(x['nsteps'],x['t'],x['last']['max_endpoint_error'],flush=True)
 x['step_summaries']=out
 return x

def isolate(data):
  assert data['nsteps']==75 and F(data['t'])==F('4.26534095')
  # Event brackets using the strict two-track state envelope and signed propagation
  t=F(data['t']);root=list(map(F,data['root']))
  noise=list(map(F,data['symbol_radii']));rem=list(map(F,data['remainder']))
  H=[[decode(z) for z in row] for row in data['H']]
  envelope=[sum((mag(m)*w for m,w in zip(row,noise)),rem[i]) for i,row in enumerate(H)]
  results=[]
  for h in (F('.0098'),F('.0104')):
   P,eps=v.j27.residual_v(52,t,root,h)
   for r in ('.00001','.0001','.001'):
    R=F(r);X=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
    Eflow=c.bound_exp(v.j27.get_A_v(X),h,envelope,eps)
    gu,gv,gs=c.guards(X);slope=v.diode_U_slope(X)
    if all(e<R for e in Eflow) and gv.a>0 and gs.a>0 and slope.a>0:break
   else: raise AssertionError(('event tube failed',str(h)))
   Phi,_,_=v.exp_bound_signed(v.jsigned(X),h,8)
   Hnew=v.mmul(Phi,H)
   forcing=c.bound_exp(v.j27.get_A_v(X),h,[F(0)]*9,eps)
   remainder=[sum((mag(a)*b for a,b in zip(row,rem)),z) for row,z in zip(Phi,forcing)]
   endpoint=[c.evalpoly(row,I(h)) for row in P]
   err=[sum((mag(a)*b for a,b in zip(row,noise)),z) for row,z in zip(Hnew,remainder)]
   event_state=[z.expand(e) for z,e in zip(endpoint,err)]
   guard=event_state[2]-event_state[4]-v.p['Vd']
   results.append((h,guard,err,slope,root,X,eps))
  assert results[0][1].b<0 and results[1][1].a>0
  # Enclose state over uncertain root time: bound Taylor variation via interval polynomial at h in [hL,hR]
  hL,hR=results[0][0],results[1][0]
  P,eps=v.j27.residual_v(52,t,root,hR)
  R=F('.001')
  X=[c.evalpoly(row,I(0,hR)).expand(R) for row in P]
  Eflow=c.bound_exp(v.j27.get_A_v(X),hR,envelope,eps)
  assert all(e<R for e in Eflow)
  Phi,_,_=v.exp_bound_signed(v.jsigned(X),hR,8)
  Hnew=v.mmul(Phi,H)
  forcing=c.bound_exp(v.j27.get_A_v(X),hR,[F(0)]*9,eps)
  remainder=[sum((mag(a)*b for a,b in zip(row,rem)),z) for row,z in zip(Phi,forcing)]
  err=[sum((mag(a)*b for a,b in zip(row,noise)),z) for row,z in zip(Hnew,remainder)]
  # Endpoint Phi only, so cannot use at uncertain time! use monotone Eflow for uncertain root state
  state=[c.evalpoly(row,I(hL,hR)).expand(e) for row,e in zip(P,Eflow)]
  path=ROOT/'Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json'
  events=json.loads(path.read_text(),parse_float=F,parse_int=F)['events']
  memb=[z.subset(I(vv-F('.0001'),vv+F('.0001'))) for z,vv in zip(state,events[3]['x'])]
  return dict(status='J29_AFFINE_FIRST_FOURTH_DIAGNOSTIC',bracket=[str(t+hL),str(t+hR)],
     left_guard=[str(results[0][1].a),str(results[0][1].b)],
     right_guard=[str(results[1][1].a),str(results[1][1].b)],
     state_box_membership=memb,paid=sum(memb),
     uncertainty_for_root_state='monotone all-time bound (rather than invalid endpoint bound)',
     envelope_max=float(max(Eflow)),
     periodic_orbit_proved=False)

def refine(data):
    assert data['nsteps']==75 and F(data['t'])==F('4.26534095')
    t=F(data['t']);root=list(map(F,data['root']))
    noise=list(map(F,data['symbol_radii']));rem=[up(q) for q in data['remainder']]
    H=[[decode(z) for z in row] for row in data['H']]
    envelope=[sum((mag(z)*a for z,a in zip(row,noise)),rem[i]) for i,row in enumerate(H)]
    cache={}
    def assess(h):
        if h in cache:return cache[h]
        P,eps=v.j27.residual_v(52,t,root,h)
        for r in ('.000001','.00001','.0001','.001'):
            R=F(r);X=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
            gu,gv,gs=c.guards(X)
            Eflow=c.bound_exp(v.j27.get_A_v(X),h,envelope,eps)
            slope=v.diode_U_slope(X)
            if all(e<R for e in Eflow) and gv.a>0 and gs.a>0 and slope.a>0:break
        else:raise AssertionError(('uncertified fourth event tube',str(h)))
        Phi,L,_=v.exp_bound_signed(v.jsigned(X),h,8)
        Hnew=v.mmul(Phi,H)
        Fforce=c.bound_exp(v.j27.get_A_v(X),h,[F(0)]*9,eps)
        remnew=[sum((mag(z)*a for z,a in zip(row,rem)),f) for row,f in zip(Phi,Fforce)]
        Eend=[sum((mag(z)*a for z,a in zip(row,noise)),r) for row,r in zip(Hnew,remnew)]
        state=[c.evalpoly(row,I(h)).expand(e) for row,e in zip(P,Eend)]
        guard=state[2]-state[4]-v.p['Vd']
        cache[h]=dict(h=h,guard=guard,flow=Eflow,endpoint=Eend,slope=slope,P=P,
                      eps=eps,X=X,R=R,oldroot=root,L=L)
        return cache[h]
    left=F('.0098');right=F('.0104')
    assert assess(left)['guard'].b<0 and assess(right)['guard'].a>0
    history=[]
    for k in range(28):
        mid=(left+right)/2
        a=assess(mid)
        if a['guard'].b<0:
            left=mid;decision='L'
        elif a['guard'].a>0:
            right=mid;decision='R'
        else:
            decision='ambiguous';history.append(dict(step=k,mid=str(mid),decision=decision));break
        history.append(dict(step=k,mid=str(mid),decision=decision,width=float(right-left)))
    assert assess(left)['guard'].b<0 and assess(right)['guard'].a>0
    r=assess(right)
    P=r['P']
    # True state at unknown root time. For all-time uncertainty, use the
    # nonnegative comparison bound, NOT the signed endpoint transition.
    state=[c.evalpoly(row,I(left,right)).expand(e) for row,e in zip(P,r['flow'])]
    original=json.loads((ROOT/'Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json').read_text(),parse_float=F,parse_int=F)['events']
    assert original[3]['kind']=='diode' and original[3]['name']=='U'
    members=[q.subset(I(z-F('.0001'),z+F('.0001'))) for q,z in zip(state,original[3]['x'])]
    margins=[]
    for q,z in zip(state,original[3]['x']):
       lo=I(z-F('.0001')).a;hi=I(z+F('.0001')).b
       margins.append([str(q.a-lo),str(hi-q.b)])
    return dict(status='J29_REFINED_FOURTH_EVENT_VALIDATED' if all(members) else 'J29_REFINED_FOURTH_EVENT_J24_BOX_UNPAID',
        U_activation_time_bracket=[str(t+left),str(t+right)],
        time_width_model_units=str(right-left),
        left_guard_exact_grid=[str(assess(left)['guard'].a),str(assess(left)['guard'].b)],
        right_guard_exact_grid=[str(r['guard'].a),str(r['guard'].b)],
        signed_slope_grid=[str(r['slope'].a),str(r['slope'].b)],
        positive_slope_through_entire_0_to_right=True,
        all_time_Picard_error_grid=[str(c.j25.ceil_div(e.numerator*S,e.denominator)) for e in r['flow']],
        all_time_Picard_error_max=float(max(r['flow'])),
        event_state_grid=[[str(q.a),str(q.b)] for q in state],
        J24_original_event_state_coordinate_membership=members,
        J24_original_event_state_coordinate_margins_integer_grid=margins,
        original_J24_fourth_box_paid=all(members),
        validated_crossings=4,original_J24_event_boxes_paid=4 if all(members) else 3,
        bisection_history=history,
        true_ODE_after_fourth_diode_switch_integrated=False,
        periodic_orbit_proved=False,synthetic_source_only=True,CI_used=False)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('mode',choices=('init','advance','event','refine'));ap.add_argument('--input',required=True);ap.add_argument('--count',type=int,default=10);ap.add_argument('--out',required=True)
 a=ap.parse_args();x=json.loads(Path(a.input).read_text()) if a.mode!='init' else initialize(a.input)
 o=advance(x,a.count) if a.mode=='advance' else isolate(x) if a.mode=='event' else refine(x) if a.mode=='refine' else x
 Path(a.out).write_text(json.dumps(o,indent=2)+'\n')
 print('STATUS',o['status'],o.get('t'),o.get('nsteps'),flush=True)
if __name__=='__main__':main()
