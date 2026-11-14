"""Exact-source CP SU3 Wilson and conditional horn regularity controls.

Source roots: Aharonov–Bohm, Wilson, Hatcher Example 2B.2,
Gotô 1949; previous DASHI SUNWilsonClassFunction and
NeutrinoHornedSU3RootExact. Unpolarized abstract qutrit two-arm
interferometer is a deliberately chosen MODEL, not observed physics.

The conditional shrinking-loop theorem is for bounded unitary
connections with uniformly short representatives in compatible
frames. The actual wild embedding has NOT supplied that geometry.
"""
import unittest
from fractions import Fraction as F
import math
import numpy as np
from test_neutrino_existing_cp_sector_bridge import add
from test_neutrino_horned_su3_positive_bridge import residual_target
from test_neutrino_existing_cp_sector_bridge import pmns

def field_complex(z):
    return complex(float(z[0])-float(z[1])/2,
                   math.sqrt(3)*float(z[1])/2)

def to_np(M):
    return np.array([[field_complex(z) for z in row] for row in M])

def selected():
    return residual_target()[2]

def fringe(U,phi):
    amp=(np.eye(3)+np.exp(1j*phi)*U)/2
    return float(np.trace(amp@amp.conj().T).real)/3

def level_leaf_lower_bound(root_gap,n):
    return 0.5*math.exp(math.log(2*root_gap)/2**n)

class HornWilsonRegularityTests(unittest.TestCase):
    def test_exact_source_wilson_trace_and_fringe(self):
        A=selected()
        tr=(sum(A[i][i][0] for i in range(3)),
            sum(A[i][i][1] for i in range(3)))
        D=181846007130841
        self.assertEqual(tr,(F(176093404722400,D),
                             -F(19836986431118,D)))
        self.assertEqual(2*tr[0]-tr[1],F(372023795875918,D))
        P0=F(1,2)+(2*tr[0]-tr[1])/12
        self.assertEqual(P0,F(434928608401,648677790003))
        self.assertAlmostEqual(fringe(to_np(A),0),float(P0),places=13)

    def test_general_two_arm_amplitude_and_visibility(self):
        W=to_np(selected()); I=np.eye(3)
        tr=np.trace(W)
        self.assertAlmostEqual(abs(tr)/3,.3424207192088653,places=12)
        for phi in (0,.2,.7,math.pi/2,math.pi):
            self.assertAlmostEqual(fringe(W,phi),
                .5+.5*np.real(np.exp(1j*phi)*tr/3),places=13)
            self.assertTrue(0<=fringe(W,phi)<=1)
        self.assertNotAlmostEqual(fringe(W,0),fringe(I,0),places=8)

    def test_joint_gauge_conjugation_invariance(self):
        W=to_np(selected())
        T=np.diag((1,np.exp(2j*math.pi/3),np.exp(4j*math.pi/3)))
        for G in (T,to_np(pmns())):
            Wg=G@W@G.conj().T
            for phi in (0,.3,math.pi/2,math.pi):
                self.assertAlmostEqual(fringe(Wg,phi),fringe(W,phi),places=12)

    def test_commutator_bound_on_unitary_samples(self):
        rng=np.random.default_rng(1949)
        I=np.eye(3)
        for _ in range(30):
            X,Y=[],[]
            matrices=[]
            for j in range(2):
                m=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3))
                q,_=np.linalg.qr(m)
                q=q/np.linalg.det(q)**(1/3)
                matrices.append(q)
            X,Y=matrices
            C=X@Y@X.conj().T@Y.conj().T
            left=np.linalg.norm(C-I,2)
            right=2*np.linalg.norm(X-I,2)*np.linalg.norm(Y-I,2)
            self.assertLessEqual(left,right+1e-12)

    def test_shrinking_loop_regularization_lower_bound(self):
        W=to_np(selected())
        gap=np.linalg.norm(W-np.eye(3),2)
        self.assertGreater(gap,1)
        for n in (1,2,3,5,8,12):
            eps=level_leaf_lower_bound(gap,n)
            self.assertGreater(eps,.5)
            self.assertGreater(eps/(2**(-n)),2**(n-1))
        # Uniform leaf holonomy -> I would contradict fixed nonzero root.
        # That premise does NOT follow from abstract group existence.

    def test_flat_yang_mills_action_and_topological_specificity(self):
        # F=0 -> tr(F†F)=0 for all flat holonomies;
        # pure classical YM does not select the supplied W.
        for W in (np.eye(3),to_np(selected())):
            Fzero=np.zeros_like(W)
            self.assertEqual(np.trace(Fzero.conj().T@Fzero).real,0)
        # pi1(S1)=Z can map its generator to the very same W;
        # a one-loop trace never diagnoses wild horn geometry.
        self.assertNotAlmostEqual(np.trace(to_np(selected())).real,3,places=8)

if __name__=="__main__":
    unittest.main()
