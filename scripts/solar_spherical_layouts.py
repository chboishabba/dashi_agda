"""Physical receiver support families on the original spherical edge complex.
Equal projected footprint area, explicit discretization discrepancy.
The unrestricted family is all eligible edges, not arbitrary continuous topology.
"""
import numpy as np
from solar_spherical_whitney import shell_mesh

def layouts(radii,level,normal,tangent,area_m2,orientations=(0.,)):
    xyz,s,m,d=shell_mesh(radii,level)
    n=np.asarray(normal,float); u=np.asarray(tangent,float)
    assert n.shape==u.shape==(3,) and np.isclose(n@n,1) and np.isclose(u@u,1) and np.isclose(n@u,0)
    v=np.cross(n,u); radius=float(radii[0])
    assert 0<area_m2<radius**2
    # Inner boundary edges only; use their exact original IDs.
    ids=np.array([i for i,e in enumerate(s[1]) if np.allclose(np.linalg.norm(xyz[list(e)],axis=1),radius,rtol=1e-12,atol=1e-9)])
    midpoint=np.array([xyz[list(s[1][i])].mean(axis=0) for i in ids])
    direction=midpoint/np.linalg.norm(midpoint,axis=1)[:,None]
    front=direction@n>0
    ids=ids[front]; direction=direction[front]
    # Gnomonic tangent coordinates, explicitly not surface area.
    coords=radius*np.column_stack((direction@u,direction@v))/(direction@n)[:,None]
    result=[]
    for name,ratio in [('square',1.),('3:2',1.5),('golden',(1+np.sqrt(5))/2)]:
        a=np.sqrt(area_m2*ratio); b=area_m2/a
        for angle in orientations:
            co,si=np.cos(angle),np.sin(angle)
            q=coords@np.array([[co,-si],[si,co]])
            inside=(abs(q[:,0])<=a/2)&(abs(q[:,1])<=b/2)
            selected=ids[inside]
            # Empty layout is an unresolved resolution issue, not a fabricated receiver.
            result.append(dict(id=f'{name}:{angle:.12g}',receiver_edges=selected.tolist(),
                projected_area_m2=float(a*b),ratio=ratio,angle_rad=float(angle),
                resolved=bool(len(selected)),scope='edge midpoint membership in gnomonic rectangle'))
    result.append(dict(id='unrestricted',receiver_edges=ids.tolist(),resolved=bool(len(ids)),
        scope='all eligible inner-boundary hemisphere edges; same load budget, not equal footprint area'))
    return result

def compare_trajectory(fine,coarse,R,L):
    """Preserve signed spatial and temporal complements, including DC.
    Caller supplies physically licensed intermesh restriction and equal clocks.
    """
    from solar_physical_refinement import compare
    if fine['elapsed_s']!=coarse['elapsed_s']:
        raise ValueError('campaign clocks differ')
    x=np.asarray(fine['history']); y=np.asarray(coarse['history'])
    if x.ndim!=2 or y.ndim!=2:raise ValueError('retain_history required')
    # Periodic Fourier comparison is inappropriate for a nonperiodic campaign.
    # Use nested endpoint samples, plus every omitted fine time coordinate.
    if len(x)%len(y):raise ValueError('nested endpoint grids required')
    from solar_physical_refinement import split
    z,detail=split(x,R,L)
    stride=len(x)//len(y); ix=np.arange(stride-1,len(x),stride)
    signed=z[ix]-y; temporal=z.copy(); temporal[ix]=0
    recovered=temporal.copy(); recovered[ix]=y+signed
    reconstructed=recovered@np.asarray(L).T+detail
    assert np.allclose(reconstructed,x)
    return dict(signed_residual=signed,spatial_complement=detail,temporal_complement=temporal,
        zero_mode=z.mean(axis=0),reconstruction_error=float(np.max(abs(reconstructed-x))))
