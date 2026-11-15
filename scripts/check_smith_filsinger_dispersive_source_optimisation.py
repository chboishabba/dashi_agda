#!/usr/bin/env python3
"""Finite-reservoir source-feed and useful-load co-optimisation.
All numeric impedance units are normalised model parameters, not
Filsinger's measured shunt values or an Earth conductivity estimate.
"""
from dataclasses import replace
import numpy as np
from check_smith_filsinger_dispersive_finite_line import Params,run

def sweep():
 p=Params()
 rows=[]
 for feed in (.1,.25,.5,.75,1.5,3.):
  for load in (.4,.8,1.6,3.2,6.4):
   r=run(0,replace(p,Gfeed=feed,Rload=load))
   available=(r['source_initial']-r['source_final'])+r['source_recharge']+r['driver_work']+r['material_modulation_work']
   assert available>0 and abs(r['total_balance_residual'])<1e-8
   rows.append(dict(feed_conductance=feed,load_resistance=load,
      useful_load=r['useful_load'],source_feed_loss=r['source_feed_loss'],
      donor_depletion=r['source_initial']-r['source_final'],
      captured_useful_fraction=r['useful_load']/available))
 return rows

if __name__=='__main__':
 import json
 rows=sweep()
 best=max(rows,key=lambda r:r['useful_load'])
 assert best['feed_conductance']==3. and best['load_resistance']==.8
 print(json.dumps(dict(baseline=next(r for r in rows if r['feed_conductance']==.75 and r['load_resistance']==1.6),
                       best=best,rows=rows),indent=2))
 print('PASS joint finite-source/receiver impedance sweep (30 cases)')
