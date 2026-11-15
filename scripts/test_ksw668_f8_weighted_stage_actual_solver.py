#!/usr/bin/env python3
import unittest
import numpy as np
from ksw668_f8_full_coupled_weighted_sbp_energy import setup,full_energy_derivative,coeff
from ksw668_f8_tt_multipole import stage,enforce
class ActualOriginalThreeMultipoleStage(unittest.TestCase):
 def test_full_weighted_energy_operator_is_actual_stage(self):
  for t in (1,4/3,2):
   d=setup(ny=9,nr=7,t=t,dy=.02,dr=.03,seed=round(t*17))
   b,v,vt,a,c=coeff(t)
   U=np.pad(d['U'],((0,0),(0,0),(0,1)))
   P=np.pad(d['P'],((0,0),(0,0),(0,1)))
   M=np.pad(d['M'],((0,0),(0,0),(0,1)))
   G=np.zeros((3,U.shape[-1]))
   cp=np.zeros_like(G);cm=cp.copy()
   for q in range(3):
    dim=3+4*q
    for j in range(1,U.shape[-1]):
     hi=j+.5;lo=j-.5;den=hi**dim-lo**dim
     cp[q,j]=dim*hi**(dim-1)/den;cm[q,j]=dim*lo**(dim-1)/den
   du=U.copy();dp=U.copy();dm=U.copy()
   enforce(U,P,M,v,1,G,4)
   stage(U,P,M,du,dp,dm,d['dr'],d['dy'],b,v,1,G,cp,cm,4)
   ref=full_energy_derivative(d,return_derivatives=True)
   for key,arr in (('Udot',du),('Pdot',dp),('Mdot',dm)):
    self.assertLess(np.max(abs(arr[:,:,:-1]-ref[key])),1e-10)
if __name__=='__main__':unittest.main(verbosity=2)
