"""Original mode3 producer with a separately fingerprinted sufficient CFL.
Reuses historical capture wrapper; never substitutes historical step receipts.
Cooperative checkpoint exit 75; actual parity capture on completed run only.
"""
import argparse,json,math
from pathlib import Path

LABELS=('A0','A1','C0','C1')
DEFAULT_WORK='.local-f8-safe-clock'


def configuration(label):
    if label not in LABELS:raise ValueError('source label')
    dr=.008 if label[0]=='A' else .006
    dy=.012
    dt=.9/(7/dr+10/dy+400)
    assert dt*(7/dr+10/dy+400)<1
    assert dt<min(dr*math.sqrt(3/44),dy*.45)
    return dict(dr=dr,dy=dy,dt=dt,eps=.04,final_t=12.,pulse=.065,inside_chord=.012,r_outer=3.01,y_outer=2.01,normal_order=3,conservative_source=True,weak_source_load=label[1]=='1')


def arguments():
    p=argparse.ArgumentParser()
    p.add_argument('label',choices=LABELS)
    p.add_argument('--work',type=Path,default=Path(DEFAULT_WORK))
    p.add_argument('--budget',type=float,default=12.)
    a=p.parse_args()
    if not 0<a.budget<=90:p.error('positive cooperative budget <= 90 seconds')
    return a


def driver():
    from ksw668_f8_tt_multipole import propagate,F
    a=arguments();a.work.mkdir(parents=True,exist_ok=True);c=configuration(a.label)
    try:
        result=propagate(**c,checkpoint=a.work/(a.label+'.npz'),budget=a.budget,checkpoint_every=16)
    except InterruptedError as e:
        print(e,flush=True)
        return 75
    n=math.ceil((F(12.)-F(1.))/c['dt'])
    if result['steps']!=n or not result['step_time']*(7/c['dr']+10/c['dy']+400)<1:
        raise ValueError('wrong safe-clock production identity')
    if bool(result['weak_source_load'])!=c['weak_source_load']:raise ValueError('wrong source representative')
    path=a.work/(a.label+'.json');tmp=path.with_suffix('.tmp')
    tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(path)
    return 0


def main():
    from run_f8_p0_native_receiver_state_capture import main as capture_main
    from check_f8_parity_capture_tail import capture
    a=arguments()
    status=capture_main(driver_main=driver,driver_name='run_f8_safe_source_capture.driver',default_work=DEFAULT_WORK)
    if status!=0:return status
    result=capture(a.work/(a.label+'.npz'),a.work/(a.label+'.receiver-state.npz'),a.work/(a.label+'.json'))
    path=a.work/(a.label+'.packets.json');tmp=path.with_suffix('.tmp')
    tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(path)
    print(path,flush=True)
    return 0


if __name__=='__main__':raise SystemExit(main())
