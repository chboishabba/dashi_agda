#!/usr/bin/env python3
"""Same ORIGINAL 27 indexed across Higgs global-form stages.

Source owner: first-Tits 27 #1106 and KK orbifold #1241.
New finite index/charge handoff, Johl Brown with OpenAI assistance.
This executes three actual owning scripts, not a second independent
27 action. Classical group stabilizer checks only, NOT quantum EFT.
"""
from pathlib import Path
import runpy, io, contextlib
root=Path(__file__).resolve().parents[1]/"scripts"

def owner(name):
    with contextlib.redirect_stdout(io.StringIO()) as o:
        out=runpy.run_path(str(root/name))
    assert 'PASS' in o.getvalue(),(name,o.getvalue())
    return out
k=owner('check_kk_e6_k_global_z6_selection.py')
sm=owner('check_kk_e6_post_e32_sm_global_z6.py')
em=owner('check_kk_e6_post_e21_u3_photon.py')
assert len(k['entries'])==len(sm['states'])==len(em['states'])==27

def rdelta(ri):return (3,-3,0)[ri]
def ldelta(li):return (-3,3,0)[li]
for ko,so,eo in zip(k['entries'],sm['states'],em['states']):
    b,ci,li,ri,t,sL,sR,qk=ko
    assert so[:4]==ko[:4] and eo[:4]==ko[:4]
    assert so[4]==eo[4]==t and so[-1]==eo[-1]
    qs=so[-2]
    qe=eo[-2]
    if b=='A':
        assert qs==qk and qe==qs-ldelta(li)
    elif b=='B':
        assert qs==qk+rdelta(ri) and qe==qs
    else:
        assert qs==qk-rdelta(ri) and qe==qs+ldelta(li)
    assert k['correct'](t,sL,sR,qk)
    assert sm['phase'](t,sL,qs,1,1,5)==0
    assert qe%2==0 and (t-qe//2)%3==0
print('PASS 27 original source states transported K -> global SM/Z6 -> color/EM U3')
print('PASS all R/L Higgs stabilizer charge shifts and orbifold chirality labels')
print('OPEN 5D eta/CS/WZ, dynamical three-VEV vacuum, full KK and LARES source')
