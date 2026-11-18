module DASHI.Mathematics.Topology.KKHopfSpinSelectionCounterexampleExact where

------------------------------------------------------------------------
-- CLASSICAL ATTRIBUTION / MATHEMATICAL ORIGIN
-- H. Hopf (1931), Math. Ann. 104, 637-665, DOI:10.1007/BF01457962.
-- D. Finkelstein and J. Rubinstein (1968), "Connection between Spin,
-- Statistics, and Kinks", J. Math. Phys. 9, 1762-1779,
-- DOI:10.1063/1.1664510.
-- Spin(3) = SU(2) -> SO(3) and the central sign are standard.
--
-- EXISTING DASHI OWNERS (REUSED, NOT CLAIMED AS NEW):
-- HopfQuaternionAxisProjectionExact.canonicalAxisPhaseInvariant;
-- FiniteQuaternionDoubleCover.rho, plusOne, minusOne, plusMinusDistinct;
-- SU2SO3IrrepDimensionExact.spinorHighestWeightOneDoesNotDescend;
-- SpinStatisticsConnectionReceipt (finite prime lanes remain bosonic).
--
-- NEW DASHI CONTRIBUTION, THIS ROUND:
-- An actual two-witness counterexample: the SAME spatially trivial
-- transformation is compatible with both central signs. The first and
-- second lifts are different. Consequently Hopf fibre invariance plus a
-- spatially trivial rotation CANNOT, by themselves, choose a spinorial
-- sign. This is a strict finite theorem, not a continuous FR soliton
-- classification or physical KK action.
--
-- USER RESEARCH MOTIVATION: test whether KK/Hopf dipolar winding derives
-- particle spin, rather than inserting spin-1/2 as a separate axiom.
-- ChatGPT-assisted implementation. Credit retained with classical sources
-- and existing prior repo modules; no claim of source-authored DASHI code.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Algebra.FiniteQuaternionDoubleCover as Cover
import DASHI.Mathematics.Topology.HopfQuaternionAxisProjectionExact as Hopf
import DASHI.Mathematics.Topology.HopfU1CosetOrbitExact as Orbit
import DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact as Circle

-- Both signs lift the same identity rotation in the finite Q8 model.
positiveSpatialIdentity :
  Cover.rho Cover.plusOne ≡ Cover.identityRotation
positiveSpatialIdentity = refl

negativeSpatialIdentity :
  Cover.rho Cover.minusOne ≡ Cover.identityRotation
negativeSpatialIdentity = refl

twoLiftsSameSpatialRotation :
  Cover.rho Cover.plusOne ≡ Cover.rho Cover.minusOne
twoLiftsSameSpatialRotation = refl

-- But they are not the same lift. Thus projection forgets the sign.
twoLiftsGenuinelyDifferent : Cover.plusOne ≡ Cover.minusOne → ⊥
twoLiftsGenuinelyDifferent = Cover.plusMinusDistinct

-- Existing Hopf phase invariance is orthogonal to this sign choice.
hopfBaseUnchangedByFibrePhase :
  (g : Orbit.Total) (u : Circle.U1TorusElement) →
  Hopf.axisMap (Orbit.rightPhase g u) ≡ Hopf.axisMap g
hopfBaseUnchangedByFibrePhase = Hopf.canonicalAxisPhaseInvariant

-- Counterexample: specifying *only* the identity spatial rotation does
-- not uniquely determine the lifted spin transformation.
noUniqueSpinLiftFromSpatialProjection :
  ((q : Cover.Q8) →
    Cover.rho q ≡ Cover.identityRotation →
    q ≡ Cover.plusOne) → ⊥
noUniqueSpinLiftFromSpatialProjection unique =
  Cover.plusMinusDistinct (sym (unique Cover.minusOne refl))

-- This is deliberately not the assertion that a given soliton has no
-- spin-1/2 quantization. It demonstrates that topological or spatial
-- projection data alone fail to select it. The selected configuration
-- space, rotation path, quantum representation, and exchange path must
-- still be constructed from the physical parent theory.
