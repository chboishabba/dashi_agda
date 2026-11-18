module DASHI.Mathematics.Topology.KKHopfSpinExistingOwnerWeldExact where

-- Exact P2/P5 prior-art reuse cut. This is NOT a KK particle theorem.
-- Existing Hopf owner proves U(1)-phase invariance of a quaternion-axis map;
-- existing spin owner proves the finite central-sign 360/720 relations.
-- They remain two independent facts. In particular, neither the Hopf charge
-- nor the existence of a U(1) fibre supplies a fermionic soliton
-- quantization, whose configuration-space rotation loop remains open.

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.Topology.HopfQuaternionAxisProjectionExact as Hopf
import DASHI.Mathematics.Topology.HopfU1CosetOrbitExact as Orbit
import DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact as U1
import DASHI.Algebra.FiniteQuaternionDoubleCover as Q8
import DASHI.Mathematics.Topology.AlexanderHornedSpin360720Exact as Spin
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Irrep
open import Data.Empty using (⊥)

-- No duplicate circle-fibre computation: exact identity via the
-- canonical Hopf projection already owned by the topology module.
hopfAxisInvariantUnderPhase :
  (g : Orbit.Total) (u : U1.U1TorusElement) →
  Hopf.axisMap (Orbit.rightPhase g u) ≡ Hopf.axisMap g
hopfAxisInvariantUnderPhase = Hopf.canonicalAxisPhaseInvariant

-- No invented 360-degree theorem: reuse the strict finite Q8 owner.
spinorialCentralSignIsNontrivial :
  Spin.spinAt360 ≡ Spin.spinAtZero → ⊥
spinorialCentralSignIsNontrivial = Spin.spinAt360IsNotSpinIdentity

spinorialDoubleTurnReturns :
  Spin.spinAt720 ≡ Spin.spinAtZero
spinorialDoubleTurnReturns = Spin.spinAt720ReturnsToIdentity

-- Existing highest-weight theorem separates spin-half SU2 from SO3.
spinHalfCannotDescendToSO3 :
  Irrep.EvenHighestWeight 1 → ⊥
spinHalfCannotDescendToSO3 = Irrep.spinorHighestWeightOneDoesNotDescend

-- This record carries both *proved* observations together but makes no
-- unsupported logical identification between their underlying carriers.
record HopfSpinProvenBoundary : Set where
  field
    axisPhaseLaw :
      (g : Orbit.Total) (u : U1.U1TorusElement) →
      Hopf.axisMap (Orbit.rightPhase g u) ≡ Hopf.axisMap g
    finite360Distinct : Spin.spinAt360 ≡ Spin.spinAtZero → ⊥
    finite720Return : Spin.spinAt720 ≡ Spin.spinAtZero
    halfRepresentationNotSO3 : Irrep.EvenHighestWeight 1 → ⊥

canonicalHopfSpinProvenBoundary : HopfSpinProvenBoundary
canonicalHopfSpinProvenBoundary = record
  { axisPhaseLaw = hopfAxisInvariantUnderPhase
  ; finite360Distinct = spinorialCentralSignIsNontrivial
  ; finite720Return = spinorialDoubleTurnReturns
  ; halfRepresentationNotSO3 = spinHalfCannotDescendToSO3
  }

-- Open gates: actual continuous SO3 path lifting; topology of the physical
-- soliton configuration space; Finkelstein-Rubinstein exchange constraint;
-- Hilbert representation and original 5D Einstein/matter dynamics.
