"""Source-explicit ORIGINAL moving-AdS z^-3 weighted-SBP4 forward stage.

A separate, conservative F8 mode4 donor: the source-pinned original
ksw668_f8_tt_multipole.stage does NOT implement normal_order=4 (it
falls through its legacy branch). DO NOT patch that source in place:
NativeCheckpoint source hashes and historical LV/LVI remain unchanged.

This function implements the pre-existing LXXV original weighted split
  D_w f = z^(3/2) D_y(z^(-3/2) f) + 3f/(2z)
including the same original FV radial, SAT Israel and outer terms.
The wrapper maps order3 to original.stage, and order4 here.
Neither branch proves full SSPRK3 stability, Weyl convergence or physics.
"""
from numba import njit
from ksw668_f8_tt_multipole import stage as original_mode3

@njit(cache=True)
def weighted_stage4(U,P,M,outU,outP,outM,dr,dy,b,v,amp,src,cp,cm,normal_order=4):
    if normal_order!=4:
        raise ValueError("weighted_stage4 requires explicit normal_order=4")
    nm,ny,nr=U.shape
    if nm!=3 or ny<3 or nr<4:
        raise ValueError("wrong original F8 mode4 geometry")
    dr2=dr*dr
    for q in range(3):
        d=3+4*q
        for iy in range(ny):
            z=b+iy*dy
            for ir in range(nr):
                p=P[q,iy,ir]
                m=M[q,iy,ir]
                if ir==nr-1:
                    outU[q,iy,ir]=0.
                    outP[q,iy,ir]=0.
                    outM[q,iy,ir]=0.
                    continue
                if ir==0:
                    radial=2*d*(U[q,iy,1]-U[q,iy,0])/dr2
                else:
                    radial=(cp[q,ir]*(U[q,iy,ir+1]-U[q,iy,ir])-
                            cm[q,ir]*(U[q,iy,ir]-U[q,iy,ir-1]))/dr2
                w=(p-m)/2
                force=radial-3*w/z
                outU[q,iy,ir]=((1+v)*p+(1-v)*m)/2
                if iy==0:
                    dpy=((z/(z+dy))**1.5*P[q,iy+1,ir]-p)/dy+1.5*p/z
                    dmy=((z/(z+dy))**1.5*M[q,iy+1,ir]-m)/dy+1.5*m/z
                elif iy==ny-1:
                    dpy=(p-(z/(z-dy))**1.5*P[q,iy-1,ir])/dy+1.5*p/z
                    dmy=(m-(z/(z-dy))**1.5*M[q,iy-1,ir])/dy+1.5*m/z
                else:
                    dpy=(((z/(z+dy))**1.5*P[q,iy+1,ir]-
                         (z/(z-dy))**1.5*P[q,iy-1,ir])/(2*dy)+1.5*p/z)
                    dmy=(((z/(z+dy))**1.5*M[q,iy+1,ir]-
                         (z/(z-dy))**1.5*M[q,iy-1,ir])/(2*dy)+1.5*m/z)
                outP[q,iy,ir]=(1+v)*dpy+force
                outM[q,iy,ir]=(v-1)*dmy+force
                if iy==ny-1:
                    outP[q,iy,ir]-=2*(1+v)*p/dy
                if iy==0:
                    target=(2*amp*src[q,ir]-(1+v)*p)/(v-1)
                    outM[q,iy,ir]+=2*(1-v)*(target-m)/dy

def matched_stage(U,P,M,outU,outP,outM,dr,dy,b,v,amp,src,cp,cm,order):
    """One source-owned dispatcher; order4 cannot silently mean legacy mode2."""
    if order==3:
        return original_mode3(U,P,M,outU,outP,outM,dr,dy,b,v,amp,src,cp,cm,3)
    if order==4:
        return weighted_stage4(U,P,M,outU,outP,outM,dr,dy,b,v,amp,src,cp,cm,4)
    raise ValueError("separate F8 matched donor only supports mode3 or weighted mode4")
