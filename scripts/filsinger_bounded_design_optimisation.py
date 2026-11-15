#!/usr/bin/env python3
"""Bounded ideal-component optimization. Conditional physics ONLY.

Requires Python 3 standard library, no CI, no field measurement claims.
The model uses an *assumed* electrical f=7800Hz equal to observed audio peak.
A voltage transfer ratio is assumed feasible rather than established.
"""
from math import pi, sqrt
import csv, json
from itertools import product
from pathlib import Path
import unittest

P, F, V, CSTORE = 6.7, 7800., 1500., 3.33e-6
CVALUES = (50., 75., 100., 150., 220., 330., 470., 680.) # nF
GAINS = (5., 8., 10., 12., 15., 20.)
QS = (30., 50., 80., 100., 150., 200.)
EFFS = (.60, .75, .85, .90)
OVERHEAD = .5
E_STORED = .5*CSTORE*V*V

def scenario(c_nf, gain, q, eff, overhead=OVERHEAD):
    c = c_nf*1e-9
    l = 1/((2*pi*F)**2*c)
    v_tank = V/gain
    u_tank = .5*c*v_tank*v_tank
    p_loss = 2*pi*F*u_tank/q
    p_charge = eff*(P-overhead-p_loss)
    return dict(c_nF=c_nf, gain=gain, q=q, efficiency=eff,
                L_mH=1000*l, tank_peak_V=v_tank,
                stored_tank_J=u_tank, tank_loss_W=p_loss,
                overhead_W=overhead, charge_power_W=p_charge,
                charge_time_s=E_STORED/p_charge if p_charge>0 else float('inf'),
                feasible=p_charge>0)

def enumerate_feasible():
    return [r for x in product(CVALUES,GAINS,QS,EFFS)
            if (r:=scenario(*x))['feasible']]

def pareto(rows):
    # Pareto-minimize charge time, gain, loaded-Q, inductance.
    keys = ('charge_time_s','gain','q','L_mH')
    result=[]
    for r in rows:
        if not any(all(s[k]<=r[k] for k in keys) and any(s[k]<r[k] for k in keys)
                   for s in rows): result.append(r)
    return result

class Tests(unittest.TestCase):
    def test_energy(self): self.assertAlmostEqual(E_STORED,3.74625)
    def test_lower_bound(self): self.assertAlmostEqual(E_STORED/P,.559141791,places=8)
    def test_selected_loss(self): self.assertAlmostEqual(scenario(100,10,100,.75)['tank_loss_W'],.551349510705,places=9)
    def test_selected_time(self): self.assertAlmostEqual(scenario(100,10,100,.75)['charge_time_s'],.8842820085,places=8)
    def test_selected_inductor(self): self.assertAlmostEqual(scenario(100,10,100,.75)['L_mH'],4.163427993,places=7)
    def test_power_all(self):
        for r in enumerate_feasible():
            self.assertLessEqual(r['tank_loss_W']+r['overhead_W']+
                                 r['charge_power_W']/r['efficiency'],P+1e-10)
    def test_no_below_ideal(self):
        self.assertTrue(all(r['charge_time_s']>=E_STORED/P for r in enumerate_feasible()))
    def test_q_monotonic(self):
        self.assertLess(scenario(100,10,200,.75)['tank_loss_W'],scenario(100,10,50,.75)['tank_loss_W'])
    def test_gain_monotonic(self):
        self.assertLess(scenario(100,20,100,.75)['tank_loss_W'],scenario(100,10,100,.75)['tank_loss_W'])
    def test_efficiency_monotonic(self):
        self.assertLess(scenario(100,10,100,.9)['charge_time_s'],scenario(100,10,100,.6)['charge_time_s'])
    def test_capacitance_monotonic(self):
        self.assertGreater(scenario(220,10,100,.75)['tank_loss_W'],scenario(100,10,100,.75)['tank_loss_W'])
    def test_overhead_monotonic(self):
        self.assertGreater(scenario(100,10,100,.75,1)['charge_time_s'],scenario(100,10,100,.75,.5)['charge_time_s'])
    def test_infeasible(self): self.assertFalse(scenario(680,5,30,.6)['feasible'])
    def test_white_as_tank_requires_large_q(self):
        self.assertGreater(2*pi*F*E_STORED/P,27000)
    def test_full_loss_each_cycle(self): self.assertGreater(E_STORED*F,29000)
    def test_reference_countermodel(self):
        self.assertEqual((1500-1000)-( -1000),(1500-1600)-(-1600))
    def test_ambient_nonidentifiability(self):
        self.assertAlmostEqual(6.7+0-2-4.7,0)
        self.assertAlmostEqual(6.7+1-2-5.7,0)
    def test_pareto_not_empty(self): self.assertTrue(pareto(enumerate_feasible()))
    def test_grid_count(self): self.assertEqual(len(enumerate_feasible()),1028)
    def test_best_grid_corner(self):
        best=min(enumerate_feasible(),key=lambda r:r['charge_time_s'])
        self.assertEqual((best['c_nF'],best['gain'],best['q'],best['efficiency']),(50.,20.,200.,.9))

if __name__ == '__main__':
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(Tests)
    test=unittest.TextTestRunner(verbosity=2).run(suite)
    if not test.wasSuccessful():raise SystemExit(1)
    rows=enumerate_feasible()
    print('Feasible:',len(rows),'Pareto:',len(pareto(rows)))
    print('Illustrative:',json.dumps(scenario(100,10,100,.75),indent=2))
