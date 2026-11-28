"""Original spherical indexed support geometry; independent of campaign/data imports."""
import numpy as np
from scipy.constants import c
from solar_spherical_material_weld import assembly_mesh

def geometry(radii,level,nested_depth=0):
    xyz,s,m,d=assembly_mesh(tuple(radii),int(level),int(nested_depth))
    # One material owner per tetrahedron: no instant shared remote material.
    vol=np.array([abs(np.linalg.det((xyz[list(t)][1:]-xyz[t[0]]).T))/6 for t in s[3]])
    pos=np.array([xyz[list(t)].mean(axis=0) for k in (1,2,3) for t in s[k]])
    ne,nf,nt=map(len,s[1:]); faces=[]
    def link(i,j,key,area):
        delta=pos[j]-pos[i]; length=np.linalg.norm(delta)
        assert length>0 and area>0
        faces.append(dict(id=key,source=i,target=j,normal=(delta/length).tolist(),area_m2=float(area)))
    for f,tri in enumerate(s[2]):
        p=xyz[list(tri)]; area=np.linalg.norm(np.cross(p[1]-p[0],p[2]-p[0]))/2
        for e in np.flatnonzero(d[1][f]):
            link(int(e),ne+f,'edge-face:%d:%d'%(e,f),area)
    from itertools import combinations
    for o,t in enumerate(s[3]):
        for e in combinations(t,2):
            j=m[1][e]; length=np.linalg.norm(xyz[e[1]]-xyz[e[0]])
            link(j,ne+nf+o,'edge-cell:%d:%d'%(j,o),vol[o]/length)
    mesh=dict(positions_m=pos.tolist(),coordinate_site=list(range(ne+nf))+np.repeat(np.arange(ne+nf,ne+nf+nt),9).tolist(),
              faces=faces,front_speed_m_s=c,scope='barycentric support graph; area is geometric support weight, not exterior flux')
    return vol,mesh,ne,nf
