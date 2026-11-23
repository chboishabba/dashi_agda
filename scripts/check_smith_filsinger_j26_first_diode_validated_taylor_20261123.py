#!/usr/bin/env python3
"""J26 certified nominal first diode-V event from rational J23 initial state.

Exact Fraction and directed 1e30 integer interval Taylor defects; no SciPy,
interval trajectory wrapping, or sampling in the proof. Reuses J25 original-
equation rational interval primitive. No periodic-orbit or 5D parameter claim.
"""
import json, math
from fractions import Fraction as F
from pathlib import Path
import check_smith_filsinger_j25_first_segment_validated_interval_20261123 as j25
I,S,p=j25.I,j25.S,j25.PARAM

def mul(a,b):
    v=[I(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for k,y in enumerate(b):v[i+k]=v[i+k]+x*y
    return v

def coeff(a,b,n):
    return sum((a[i]*b[n-i] for i in range(n+1) if i<len(a) and n-i<len(b)),I(0))

def evalpoly(poly,t):
    t=j25.iv(t);acc=I(0)
    for v in reversed(poly):acc=acc*t+v
    return acc

def supabs(x):return max(abs(x.a),abs(x.b))

def evalabs(poly,h):
    h=j25.iv(h);acc=I(0)
    for c in reversed(poly):
        acc=acc*h+I(0,j25.F(supabs(c),S))
    return acc.b

def coef(j,n):return j[n] if len(j)>n else I(0)

def coeff_series_rhs(P,SS,CC,N):
    i,j,u,v,b,q,r,ih,c=P
    out=[]
    for n in range(N+1):
        ci=lambda x:coef(x,n)
        a=-p['R1']*ci(i);bb=ci(u)-ci(v)-p['R2']*ci(j)
        left=-ci(j)+p['k']*ci(q)+p['kh']*ci(ih);right=ci(j)
        vals=[(p['L2']*a-p['M']*bb)/I('2.64'),(-p['M']*a+p['L1']*bb)/I('2.64'),
           (I('1.55')*left+right)/I('1.17'),(left+I('1.4')*right)/I('1.17'),
           (-p['Gbleed']*ci(b)-ci(ih))/p['Cb'],
           p['omega']*ci(r)-(p['gamma_rad']+p['gamma_internal'])*ci(q)-p['k']*ci(u)/I(2)+j25.RAD*p['source_amp']*coef(CC,n),
           -p['omega']*ci(q)-(p['gamma_rad']+p['gamma_internal'])*ci(r)-j25.RAD*p['source_amp']*coef(SS,n),
           (ci(b)-ci(c)-(p['Rcoil']+p['Rgap'])*ci(ih)-p['kh']*ci(u))/p['Lh']]
        out.append(vals)
    return out

def get_A(tube):
    p=j25.PARAM; c=tube[8];ih=tube[7]
    z=I(0); J=[[z for _ in range(9)] for _ in range(9)]
    J[0][0]=-p['R1']*I('1.5')/I('2.64')
    J[0][1]=p['M']*p['R2']/I('2.64')
    J[0][2]=-p['M']/I('2.64'); J[0][3]=p['M']/I('2.64')
    J[1][0]=p['M']*p['R1']/I('2.64')
    J[1][1]=-p['L1']*p['R2']/I('2.64')
    J[1][2]=p['L1']/I('2.64');J[1][3]=-p['L1']/I('2.64')
    J[2][1]=-I('.55')/I('1.17')
    J[2][5]=I('1.55')*p['k']/I('1.17')
    J[2][7]=I('1.55')*p['kh']/I('1.17')
    J[3][1]=I('.4')/I('1.17')
    J[3][5]=p['k']/I('1.17'); J[3][7]=p['kh']/I('1.17')
    J[4][4]=-p['Gbleed']/p['Cb'];J[4][7]=-I(1)/p['Cb']
    J[5][2]=-p['k']/I(2)
    J[5][5]=-p['gamma_rad']-p['gamma_internal'];J[5][6]=p['omega']
    J[6][5]=-p['omega'];J[6][6]=-p['gamma_rad']-p['gamma_internal']
    J[7][2]=-p['kh']/p['Lh'];J[7][4]=I(1)/p['Lh']
    J[7][7]=-(p['Rcoil']+p['Rgap'])/p['Lh'];J[7][8]=-I(1)/p['Lh']
    g=I(1)+I('1.5')*c**2
    J[8][7]=I(1)/(p['Ch']*g)
    J[8][8]=-p['Gload']/(p['Ch']*g)-(ih-p['Gload']*c)*I(3)*c/(p['Ch']*g**2)
    return [[F(supabs(x),S) for x in row] for row in J]

def trig_exact(x,K=55):
 x=F(x)
 sn=sum(((-1)**k * x**(2*k+1)/math.factorial(2*k+1) for k in range(K+1)),F(0))
 cs=sum(((-1)**k * x**(2*k)/math.factorial(2*k) for k in range(K+1)),F(0))
 sr=abs(x)**(2*K+2)/math.factorial(2*K+2)
 cr=abs(x)**(2*K+1)/math.factorial(2*K+1)
 return I(sn-sr,sn+sr),I(cs-cr,cs+cr)

def make_poly(N,t0,root):
 states=[[I(x)] for x in root]
 sin0,cos0=trig_exact(F('.3')+F('1.1')*t0)
 ss=[sin0];cc=[cos0]
 rho=p['gamma_rad']+p['gamma_internal']
 for n in range(N):
  i,j,u,v,b,q,r,ih,x=states
  ci=lambda X:coef(X,n)
  a=-p['R1']*ci(i)
  bb=ci(u)-ci(v)-p['R2']*ci(j)
  di=(p['L2']*a-p['M']*bb)/I('2.64')
  dj=(-p['M']*a+p['L1']*bb)/I('2.64')
  left=-ci(j)+p['k']*ci(q)+p['kh']*ci(ih);right=ci(j)
  du=(I('1.55')*left+right)/I('1.17')
  dv=(left+I('1.4')*right)/I('1.17')
  db=(-p['Gbleed']*ci(b)-ci(ih))/p['Cb']
  dq=p['omega']*ci(r)-rho*ci(q)-p['k']*ci(u)/I(2)+j25.RAD*p['source_amp']*cc[n]
  dr=-p['omega']*ci(q)-rho*ci(r)-j25.RAD*p['source_amp']*ss[n]
  dih=(ci(b)-ci(x)-(p['Rcoil']+p['Rgap'])*ci(ih)-p['kh']*ci(u))/p['Lh']
  D=[];inv=[]
  for k in range(n+1):
   D.append((I(1) if k==0 else I(0))+I('1.5')*coeff(x,x,k))
   if k==0:inv.append(I(1)/D[0])
   else:inv.append(-sum((D[j]*inv[k-j] for j in range(1,k+1)),I(0))/D[0])
  dc=sum(((coef(ih,k)-p['Gload']*coef(x,k))*inv[n-k] for k in range(n+1)),I(0))/p['Ch']
  for s,vv in zip(states,[di,dj,du,dv,db,dq,dr,dih,dc]):s.append(vv/I(n+1))
  ss.append(p['omega']*cc[n]/I(n+1)); cc.append(-p['omega']*ss[n]/I(n+1))
 return states,ss,cc

def residual(N,t0,root,h):
 P,SS,CC=make_poly(N,t0,root)
 rhs=coeff_series_rhs(P,SS,CC,N)
 polys=[]
 for j in range(8):
  res=[]
  for n in range(N+1):
   der=P[j][n+1]*I(n+1) if n+1<len(P[j]) else I(0)
   res.append(der-rhs[n][j])
  polys.append(res)
 i,j,u,v,b,q,r,ih,c=P
 D=mul(c,c)
 D=[I('1.5')*x+(I(1) if k==0 else I(0)) for k,x in enumerate(D)]
 cd=[x*I(k+1) for k,x in enumerate(c[1:])]
 res=mul(D,cd)
 for k in range(len(res)):res[k]=p['Ch']*res[k]-(coef(ih,k)-p['Gload']*coef(c,k))
 bound=[evalabs(x,I(h)) for x in polys]
 bound.append(j25.ceil_div(evalabs(res,I(h))*S,p['Ch'].a))
 forc=F('.21')*F('1.1')**N*h**N/F(math.factorial(N))
 tail=I(0,forc).b
 bound[5]+=tail;bound[6]+=tail
 return P,[F(x,S) for x in bound]

def bound_exp(A,h,delta,eps,order=90):
 h=F(h);v=[x+h*y for x,y in zip(delta,eps)]
 norm=max(map(sum,A)); assert (h*norm)<order+2
 zn=v[:];ys=v[:]
 for n in range(1,order+1):
  zn=[h*sum(A[i][j]*zn[j] for j in range(len(A))) / n for i in range(len(A))]
  ys=[x+y for x,y in zip(ys,zn)]
 tail=max(v)*(h*norm)**(order+1)/math.factorial(order+1)/(1-h*norm/F(order+2))
 return [x+tail for x in ys]

def rational_recenter(intervals,digits=23):
 factor=10**digits
 centers=[]; rounding=[]
 for x in intervals:
  k=(x.a+x.b)*factor//(2*S)
  ci=F(k,factor)
  centers.append(ci)
  grid=I(ci)
  rounding.append(F(max(abs(x.a-grid.a),abs(x.b-grid.b)),S))
 return centers,rounding

def guards(tube):
 gu=tube[2]-tube[4]-p['Vd'];gv=tube[3]-tube[4]-p['Vd'];gs=tube[4]-p['Voff']
 return gu,gv,gs

def gV_slope(tube):
 i,j,u,v,b,q,r,ih,c=tube
 left=-j+p['k']*q+p['kh']*ih
 right=j
 dv=(left+I('1.4')*right)/I('1.17')
 db=(-p['Gbleed']*b-ih)/p['Cb']
 return dv-db

def step(t0,h,root,delta,N=44,R=F('0.00001'),accept_if_slope=False):
 h=F(h);t0=F(t0)
 P,res=residual(N,t0,root,h)
 entire=[evalpoly(row,I(0,h)) for row in P]
 tube=[x.expand(R) for x in entire]
 g=guards(tube)
 A=get_A(tube)
 E=bound_exp(A,h,delta,res)
 isincl=all(q<R for q in E)
 # guards must have expected signs, unless active root bracket request
 gc=(g[0].b<0 and g[2].a>0)
 if not accept_if_slope:gc=gc and g[1].b<0
 sl=gV_slope(tube)
 if accept_if_slope:gc=gc and sl.a>0
 endpoint=[evalpoly(row,I(h)) for row in P]
 endpoint_box=[z.expand(e) for z,e in zip(endpoint,E)]
 rc,rround=rational_recenter(endpoint_box)
 guard_end=guards(endpoint_box)
 result={
  't0':str(t0),'t1':str(t0+h),'N':N,'radius':float(R),'picard_trunc_res_max':float(max(res)),
  'error_upper_max':float(max(E)),'error_vector':[float(e) for e in E],
  'parameter_mode':'nominal_only','isinc':isincl,'guards':gc,
  'gV_whole':[float(g[1].a/S),float(g[1].b/S)],
  'gV_end':[float(guard_end[1].a/S),float(guard_end[1].b/S)],
  'gU_whole':[float(g[0].a/S),float(g[0].b/S)],
  'spark_whole':[float(g[2].a/S),float(g[2].b/S)],
  'gV_slope_whole':[float(sl.a/S),float(sl.b/S)],
  'rounding_max':float(max(rround)),
  'exact_witness':dict(guards_U=[str(g[0].a),str(g[0].b)],
  guards_V=[str(g[1].a),str(g[1].b)],
  guards_spark=[str(g[2].a),str(g[2].b)],
  crossing_derivative=[str(sl.a),str(sl.b)],
  endpoint_V=[str(guard_end[1].a),str(guard_end[1].b)],
  residual_vector=[str(q) for q in res],
  comparison_error=[str(q) for q in E])}
 return result,rc,rround

def run():
    # Original J23 corrected numerical seed, represented as exact decimal rationals.
    root=[F(x) for x in j25.ROOT]
    delta=[F(0) for _ in root]
    t=F(0);rows=[]
    steps=[F(1,10)]*33 + [F(1,50)]*4
    for idx,h in enumerate(steps):
        chosen=None
        for rr in ('0.000000001','0.00000001','0.0000001','0.000001','0.00001'):
            row,nxt,err=step(t,h,root,delta,N=52,R=F(rr))
            if row['isinc'] and row['guards']:
                chosen=row,nxt,err;break
        assert chosen is not None,(idx,str(t),row)
        row,root,delta=chosen
        assert row['gV_whole'][1]<0 and row['gU_whole'][1]<0 and row['spark_whole'][0]>0
        rows.append(row);t+=h
    assert t==F('3.38') and len(rows)==37
    left=step(t,F('.009367008'),root,delta,N=52,R=F('0.00000001'),accept_if_slope=True)[0]
    right=step(t,F('.009367010'),root,delta,N=52,R=F('0.00000001'),accept_if_slope=True)[0]
    assert left['isinc'] and left['guards'] and right['isinc'] and right['guards']
    assert left['gV_end'][1]<0 and right['gV_end'][0]>0
    assert left['gV_slope_whole'][0]>0 and right['gV_slope_whole'][0]>0
    assert left['gU_whole'][1]<0 and right['gU_whole'][1]<0
    assert left['spark_whole'][0]>0 and right['spark_whole'][0]>0
    # Discharge the FIRST J24 conditional event-state box using the entire
    # isolated root-time bracket, with exact Fraction parsing of JSON decimals.
    event_path=(Path(__file__).resolve().parents[1] / 'Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json')
    centres=json.loads(event_path.read_text(),parse_float=F,parse_int=F)['events']
    assert centres[0]['kind']=='diode' and centres[0]['name']=='V'
    h_left=F('.009367008'); h_right=F('.009367010')
    P,eps=residual(52,t,root,h_right)
    whole=[evalpoly(row,I(0,h_right)).expand(F('.00000001')) for row in P]
    E=bound_exp(get_A(whole),h_right,delta,eps)
    certified_event_state=[evalpoly(row,I(h_left,h_right)).expand(e) for row,e in zip(P,E)]
    original_box=[I(x-F('.0001'),x+F('.0001')) for x in centres[0]['x']
    assert all(state.subset(box) for state,box in zip(certified_event_state,original_box))
    event_box_inclusion_grid=[[str(x.a),str(x.b)] for x in certified_event_state]
    return dict(status='PASS_EXACT_RATIONAL_NOMINAL_FIRST_DIODE_V_EVENT',
        proof_source='independent transcription of native J18 in J25 interval primitive',
        fixed_initial_state_exact_decimal_rationals=j25.ROOT,
        nominal_parameters_only=True,initial_spark_mode='ON',
        pre_event_time_reached='3.38',guard_free_accepted_steps=len(rows),
        first_diode_V_event_enclosure=['3.389367008','3.389367010'],
        event_unique_by_positive_guard_derivative=True,
        left_endpoint=left,right_endpoint=right,
        all_37_step_witnesses=rows,
        first_J24_event_state_box_included_all_9_coordinates=True,
        certified_first_event_state_grid=event_box_inclusion_grid,
        interval_arithmetic_grid_scale=str(S),
        source_input_is_synthetic_unmeasured=True,
        physical_after_crossing_not_integrated=True,
        original_periodic_orbit_certified=False,
        original_five_parameter_periodic_family_certified=False,
        github_actions_ci_run=False)

if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
