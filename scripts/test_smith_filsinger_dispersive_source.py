#!/usr/bin/env python3
"""Exact source-consistent finite-line tests. Normalised physics only."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import numpy as np
from dataclasses import replace
from check_smith_filsinger_dispersive_port_symbolic import (
 nonlinear_material,hall_pedersen,telegrapher,two_worlds)
from check_smith_filsinger_dispersive_finite_line import Params,run,check,modulation
from check_smith_filsinger_dispersive_causal_cone import check as cone_check

def test_nonlinear_memory():nonlinear_material()
def test_hall_pedersen_real_work():hall_pedersen()
def test_line_energy_invariant():telegrapher(6)
def test_matched_world_differences():two_worlds()
def test_source_work_backaction():
 a=run(0)
 assert a['natural_source_to_line']>0
 assert a['source_initial']>a['source_final']
 assert abs(a['donor_balance_residual'])<1e-8
def test_controller_energy_port():
 a=run(np.pi/2)
 assert abs(a['material_modulation_work'])>.001
 assert abs(a['total_balance_residual'])<1e-8
def test_no_reservoir_control():
 a=run(0);b=run(0,with_source=False)
 assert a['useful_load']>1
 assert b['useful_load']<.001 and b['source_recharge']==0
def test_zero_initialized_no_pump():
 p=replace(Params(),source_initial_voltage=0.,natural_recharge_current=0.,drive_amplitude=0.)
 for phase in (0,1.3):
  r=run(phase,p)
  assert abs(r['useful_load'])<1e-12
  assert abs(r['material_modulation_work'])<1e-12
def test_smooth_modulation_endpoints():
 p=Params()
 for ph in (0,np.pi/2,np.pi):
  for t in (0,p.mod_until,p.mod_until+1):assert modulation(t,ph,p)==(0.,0.)
def test_normalised_phase_scan():
 rows=check()
 assert len(rows)==16
 assert max(abs(v['total_balance_residual']) for v in rows)<1e-8
def test_causal_numerical_cone():cone_check()
