"""Direct native cone-scheduler tests; no spherical/continuum promotion."""
import numpy as np
from solar_physical_cone import timed_step

def run():
    mesh=dict(positions_m=[[0,0,0],[1,0,0],[2,0,0]],coordinate_site=[0,1,1,2],
        faces=[dict(id='a',source=0,target=1,normal=[1,0,0],area_m2=1),
               dict(id='b',source=1,target=2,normal=[1,0,0],area_m2=1)],
        front_speed_m_s=100.)
    h=.25; atlas=((0,1),(1,3)); z=np.zeros(4)
    H=np.zeros((4,4));H[1,3]=-.5;H[3,1]=.5
    P=H.copy();P[1:3,1:3]=[[-1,-2],[2,-1]]
    A=np.zeros_like(H);A[0,1]=-1;A[1,0]=1
    x=np.array([1.,0.,0.,0.]);dx=z.copy()
    for _ in range(2):
        x,receipt=timed_step(x,H,z,h,mesh,atlas_pairs=atlas,
            jvp=(dx,A,z),right_limit=P)
        dx=np.asarray(receipt['state_jvp'])
    exact=np.array([0,54823/132098,24/257,5512/66049])
    assert np.allclose(dx,exact,rtol=1e-12,atol=1e-14)
    assert np.array_equal(x,[1.,0.,0.,0.])
    assert receipt['arrival_s']==[0.,None,None,None]
    assert receipt['directional_arrival_s'][3] is not None
    first=timed_step(x,H,z,h,mesh,atlas_pairs=atlas,
        jvp=(z,A,z),right_limit=P)[1]
    assert first['directional_arrival_s'][1]==.2
    assert first['directional_arrival_s'][3]==.25
    assert [e['face_id'] for e in first['events']]==[None,None,None,'a','b']
    errors=[]
    for eps in (1e-2,1e-3,1e-4,1e-5):
        y=x.copy()
        for _ in range(2):
            y,_=timed_step(y,P+eps*A,z,h,mesh,atlas_pairs=atlas)
        errors.append(float(np.linalg.norm((y-x)/eps-dx)))
    assert errors[-1]<1e-5 and errors[-1]<errors[0]/100
    legacy,_=timed_step(x,H,z,h,mesh)
    assert np.array_equal(legacy,x)
    for opts,dt in [
        (dict(atlas_pairs=((1,3),),jvp=(z,A,z),right_limit=P),h),
        (dict(atlas_pairs=atlas,jvp=(z,A,z),right_limit=P),.01),
        (dict(atlas_pairs=atlas,jvp=(z,A,z),right_limit=P),h)]:
        # Last negative control has nonzero current in the newly activated block.
        bad=x if dt!=h or len(opts['atlas_pairs'])==1 else np.array([1.,1.,0.,0.])
        try: timed_step(bad,H,z,dt,mesh,**opts)
        except ValueError: pass
        else: raise AssertionError('invalid chart admitted')
    print(dict(status='NATIVE_COMMON_ATLAS_PASS',errors=errors,
               directional=dx.tolist(),physical_admission=False))

if __name__=='__main__': run()
