#!/usr/bin/env python3
"""Same-model finite donor versus genuinely repeatable natural replenishment.
Physical original apparatus source-strength receipt remains OPEN.
"""
from dataclasses import replace
import json
from check_smith_filsinger_dispersive_finite_line import Params,run

def periodic_requirement(gfeed,load,phase=0):
 r=run(phase,replace(Params(),Gfeed=gfeed,Rload=load))
 needed=(r['useful_load']+r['distributed_loss']+r['source_feed_loss']
         -r['driver_work']-r['material_modulation_work'])
 missing=needed-r['source_recharge']
 assert abs(missing-(r['total_energy_initial']-r['total_energy_final']))<1e-8
 return dict(gfeed=gfeed,load=load,required_natural_recharge=needed,
       actual_natural_recharge=r['source_recharge'],
       required_to_actual=needed/r['source_recharge'],
       missing_replenishment=missing,
       observed_stored_energy_depletion=r['total_energy_initial']-r['total_energy_final'],
       useful_load=r['useful_load'])

def check():
 a=periodic_requirement(.75,1.6);b=periodic_requirement(24,.8)
 assert b['useful_load']>a['useful_load']
 assert b['required_natural_recharge']>10*b['actual_natural_recharge']
 assert abs(b['required_natural_recharge']-17.652594920713483)<1e-7
 assert abs(b['missing_replenishment']-17.47566332724294)<1e-7
 return dict(baseline=a,best_tested=b)
if __name__=='__main__':
 print(json.dumps(check(),indent=2))
 print('PASS source-replenishment requirement for matched repeatable cycle')
