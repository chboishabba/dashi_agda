#!/usr/bin/env python3
"""J31 validated complete spark-OFF event2->event3 smooth physical source leg.

Exactly four rational Picard + Taylor2 slabs. Start/end event-clock intervals
independent; internal times fixed rational. Original 9-state nonlinear cap and
sin/cos wave unchanged, and physical guards paid conditionally on terminal
spark-ON zero. No full 69D Jacobian or exact periodic orbit.
"""
import argparse,json
from fractions import Fraction as F
from pathlib import Path
import check_smith_filsinger_j31_pb8_anisotropic_six_time_20261124 as pp
src=pp.src;I=src.I


def smooth_leg(nslabs=4, pb_order=12):
    assert nslabs==4 and pb_order==12
    k=2;tc0=F(src.TIMES[k]);tc1=F(src.TIMES[k+1]);dt=F(1,200000)
    initial_time=I(tc0-dt,tc0+dt)
    final_time=I(tc1-dt,tc1+dt)
    assert initial_time.b<final_time.a
    # J26–J29 event 2/3 original root-time interval coverage is checked,
    # but their independent nominal-IVP certificates are external.
    for j,t in ((1,initial_time),(2,final_time)):
        lo,hi=map(F,src.BRACKETS[j]);assert t.a<lo<hi<t.b
    X0=[I(F(z)-F('0.0001'),F(z)+F('0.0001')) for z in src.STATES[2]]
    event3_centre=list(map(F,src.STATES[3]))
    nominal=[tc0+(tc1-tc0)*F(i,nslabs) for i in range(1,nslabs)]
    interface_times=[initial_time]+[I(t) for t in nominal]+[final_time]
    P=[[I(int(i==j)) for j in range(9)] for i in range(9)]
    Xcurrent=X0;stages=[];picard_count=0;source_guards=0
    for stage in range(nslabs):
        ta,tb=interface_times[stage:stage+2];duration=tb-ta
        assert duration.a>0
        tbox=I(ta.a,tb.b)
        mids=[(x.a+x.b)/2 for x in Xcurrent]
        radii=[(x.b-x.a)/2+F('0.00000001') for x in Xcurrent]
        # Directed rational monotone envelope, with 1% width headroom.
        # This is a *local producer*, not a claimed optimal enclosure.
        for it in range(128):
            X=[I(c-r,c+r) for c,r in zip(mids,radii)]
            fx,J=src.fJ(X,tbox,src.MODES[2])
            needed=[max(x.b-c,c-x.a)+duration.b*v.mag()
                    for x,c,v in zip(Xcurrent,mids,fx)]
            new=[max(r, F(101,100)*n) for r,n in zip(radii,needed)]
            if new==radii:break
            radii=new
        else:
            raise AssertionError(('no convergent finite tube for slab',stage))
        X=[I(c-r,c+r) for c,r in zip(mids,radii)]
        fx,J=src.fJ(X,tbox,src.MODES[2])
        candidate=[x+I(0,duration.b)*v for x,v in zip(Xcurrent,fx)]
        assert all(x.within(y) for x,y in zip(candidate,X)),('no strict fulltime Picard',stage)
        picard_count+=1
        Phi,tail,first,L,q=pp.pb8(J,duration,pb_order)
        P=pp.matmul(Phi,P)  # chronological ordered product, never reverse
        f0=src.f(Xcurrent,ta,src.MODES[2]);sin,cos=src.phase(tbox)
        ft=[I(0) for _ in range(9)]
        ft[5]=-src.PARAM['omega']*src.K*sin
        ft[6]=-src.PARAM['omega']*src.K*cos
        acceleration=[ft[i]+sum((J[i][j]*fx[j] for j in range(9)),I(0)) for i in range(9)]
        finish=[Xcurrent[i]+duration*f0[i]+duration.square()/F(2)*acceleration[i] for i in range(9)]
        assert all(x.within(y,strict=False) for x,y in zip(finish,X))
        # The original spark-OFF branch is physically admissible until its
        # next ON threshold, conditional on the original last guard zero.
        U_off=src.guard(3,X);V_on=src.guard(0,X)
        assert U_off.b<0 and V_on.a>0
        # The bank must increase strictly (including on the terminal slab).
        assert fx[4].a>0
        bank=X[4]-F('0.006')
        if stage<nslabs-1:assert bank.b<0
        source_guards+=1
        stages.append(dict(stage=stage,source_mode=[0,1,0],
            fulltime=[str(tbox.a),str(tbox.b)],
            start_time=ta.record(),end_time=tb.record(),duration=duration.record(),
            strict_picard=True,source_J24_original_state_box_at_first_start=stage==0,
            tube_radii=[str(r) for r in radii],
            uniform_source_u_diode_off=U_off.record(),uniform_source_v_diode_on=V_on.record(),
            bank_derivative_strict_positive=fx[4].record(),
            bank_below_spark_on_on_whole_slab=(stage<nslabs-1),
            source_spark_on_at_last_endpoint_conditional=stage==nslabs-1,
            q=str(q),PB12_tail_radius=str(tail),
            verified_PB12_subset_first_order_9x9=True,
            fulltime_state_tube=[x.record() for x in X],
            end_state_taylor2=[x.record() for x in finish]))
        Xcurrent=finish
    # The independent clock interval derivative of the entire physical-mode
    # smooth leg obeys classical end-flow vector-field identities.
    start_f=src.f(X0,initial_time,src.MODES[2])
    end_f=src.f(Xcurrent,final_time,src.MODES[2])
    dt0=[-sum((P[i][j]*start_f[j] for j in range(9)),I(0)) for i in range(9)]
    # If g_sparkON=0 at the true event3 root, strictly positive bank slope
    # plus earlier below-threshold slab tubes excludes premature spark ON.
    bank_last=stages[-1]['bank_derivative_strict_positive']
    assert F(bank_last[0])>0
    centre_included=[u.a<=v<=u.b for u,v in zip(Xcurrent,event3_centre)]
    assert all(centre_included)
    return dict(status='PASS_J31_ONE_COMPLETE_ORIGINAL_SOURCE_SPARK_OFF_SMOOTH_MODE_4_SLABS_NOT_PERIODIC',
        segment='original event 2 spark OFF -> event 3 spark ON',
        mode=[0,1,0],source_event_t0=initial_time.record(),
        source_event_t1=final_time.record(),source_exact_root_brackets_external=True,
        original_start_state_box_halfwidth='1/10000',original_J24_event2_box_input=True,
        original_J24_event3_numeric_centre_in_terminal_interval=centre_included,
        original_J24_event3_full_box_contained=False,
        exact_full_smooth_physical_source_segment_duration=True,
        strict_Picard_slabs=picard_count,full_source_guard_slabs=source_guards,
        all_u_off_and_v_on=True,all_spark_bank_slopes_strict_positive=True,
        all_earlier_slabs_strictly_below_spark_on=True,
        physical_spark_mode_for_root_conditional_on_terminal_guard_zero=True,
        full_smooth_flow_source_Dx_Phi_9x9_interval=[list(map(I.record,row)) for row in P],
        full_smooth_flow_source_partial_t0=[z.record() for z in dt0],
        full_smooth_flow_source_partial_t1=[z.record() for z in end_f],
        final_source_state_interval=[z.record() for z in Xcurrent],
        certified_seven_original_segments=1,
        full_original_seven_source_segments_proved=False,
        full_original_69D_F_and_DF_proved=False,strict_original_69D_Krawczyk=False,
        exact_periodic_orbit_proved=False,hardware_source_measured=False,
        source_all_six_event_state_boxes_proved=False,slabs=stages)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args();r=smooth_leg()
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:r[k] for k in ('status','strict_Picard_slabs',
      'full_source_guard_slabs','certified_seven_original_segments',
      'full_original_69D_F_and_DF_proved','exact_periodic_orbit_proved')},indent=2))
    for s in r['slabs']:
        print('slab',s['stage'],'q',float(F(s['q'])),
         'bank-slope-lower',float(F(s['bank_derivative_strict_positive'][0])))
if __name__=='__main__':main()
