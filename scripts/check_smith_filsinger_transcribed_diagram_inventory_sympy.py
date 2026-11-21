#!/usr/bin/env python3
"""Exact source-indexed Filsinger/Smith transcription checks, not measurements.

Read with the source ledger Artifacts/smith-filsinger/source_indexed_transcript_diagram_values_20261122.json.
These are independent arithmetic counterfactuals, not one electrical circuit.
"""
from sympy import Rational as R, pi, simplify

n=0
def check(label,claim):
    global n
    assert bool(claim),label
    n+=1

scope={'shunt':'DfiqPnkPnP5','earth':'Dfi1D7CPzyM',
       'midpoint':'Dfu9Jseviz9 candidate','white':'earlier narration',
       'driver':'unpaired earlier','smith':'Kelly/Darrer 147 pages'}
for a,b in [('shunt','earth'),('shunt','midpoint'),('earth','midpoint'),
            ('earth','smith'),('white','earth'),('driver','earth')]:
    check('source identity '+a+' vs '+b,scope[a]!=scope[b])
C=R(333,100)*R(1,10**6)
check('white cap 3.33uF nominal',C==R(333,10**8))
check('shunt 3.3uF is only approximate to white value',C!=R(33,10**7))
check('1500V if on white cap has 3.74625J',C*1500**2/2==R(2997,800))
for r,p in [(10**6,R(9,4)),(2*10**6,R(9,8)),(4*10**6,R(9,16))]:
    check('conditional shunt V2/R '+str(r),R(1500**2,r)==p)
check('three simultaneous 1M shunts would require 6.75W DC',3*R(9,4)==R(27,4))
check('6.7W earlier input not exactly 6.75W shunt',R(67,10)!=R(27,4))
check('1500V sinusoidal peak draws half DC shunt power',R(1500**2,2*10**6)==R(9,8))
check('20kV at 1uF example holds 200J if reached',R(20000**2,2*10**6)==200)
check('10kV at 2uF example holds 100J if reached',2*R(10000**2,2*10**6)==100)
check('midpoint capacitor alternative examples differ in joules',200!=100)
check('midpoint narrated diode count 4',4==2+2)
check('midpoint 4kV output description not 20kV rating',4000!=20000)
check('earth three electrodes not four midpoint diodes',3!=4)
v,p=R(38,10),R(4,10)
check('3.8V conditional same-port 0.4W current',p/v==R(2,19))
check('3.8V conditional same-port 0.4W resistance',v*v/p==R(361,10))
check('48V capacitor display not Earth 3.8V',R(48)!=v)
each48=2*C*48**2/2
series48=R(1,2)*C*48**2/2
check('48V individually on two assumed 3.33uF capacitors',each48==R(2997,390625))
check('48V across their series pair',series48==R(2997,1562500))
check('48V same text supports 4x different energy',each48/series48==4)
check('15V and 6W conditional current',R(6,15)==R(2,5))
check('15V and 7.3W conditional current',R(73,150)==R(73,10)/15)
check('15V earlier and 3.8V Earth reading distinct',R(15)!=v)
check('audio frequency 7.8kHz not 7.83Hz Schumann',R(7800)!=R(783,100))
check('5Hz audio relative drift =1/1560',R(5,7800)==R(1,1560))
check('Smith distinct F10/F11/F40 PDF pages',len({28,29,65})==3)
check('Smith 17+17 secondary sections',17+17==34)
check('40inch L1:160inch selected L2 wire is 1:4',R(40,160)==R(1,4))
check('40in on 2.25inch diameter ~5.659 turns',abs(float(40/(pi*R(225,100)))-5.65884)<0.00001)
check('5 and two thirds geometric turns corresponds approx 240deg final offset',R(17,3)%1==R(2,3))
check('40inch/160inch wire ratio not 17/34 turns ratio',R(40,160)!=R(17,34))
check('optional Smith 47nF not 3.33uF',R(47,10**9)!=C)
check('Smith 47nF at claimed 2kV stores 0.094J conditional',R(47,10**9)*2000**2/2==R(47,500))
check('Smith 2kV*3A is 6000 VA not established watts',2000*3==6000)
check('Smith separate 8kV*20A would be 160kVA',8000*20==160000)
check('Smith separate 12V*1A would be 12VA',12*1==12)
check('Smith hypothetical real power gap if both true',160000-12==159988)
print(f'{n}/{n} PASS source-separated transcript and diagram math, not physical acceptance')
