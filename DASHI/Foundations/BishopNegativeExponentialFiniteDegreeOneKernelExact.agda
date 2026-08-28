module DASHI.Foundations.BishopNegativeExponentialFiniteDegreeOneKernelExact where

------------------------------------------------------------------------
-- DIRECT FINITE DEGREE-ONE ERDOS KERNEL
--
-- For 0 < x <= 1 and every finite cutoff N,
--
--     sum_{v=1}^N v exp(-vx) < 1/x^2.
--
-- Here the left side is represented as W_N(q), q = exp(-x), using the exact
-- finite degree-one geometric owner.  No global exp-additivity theorem is
-- required for this finite q-power kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as Identity
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Geometric
import DASHI.Foundations.BishopNegativeExponentialReciprocalSquareExact as Cross
import DASHI.Foundations.BishopNegativeExponentialReciprocalSquareDivisionExact as Division
import DASHI.Foundations.BishopNegativeExponentialUnitIntervalExact as Unit
open import DASHI.Physics.YangMills.CompactLieProofLevel

ratioInputs :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  Geometric.BishopUnitIntervalRatio (Cross.q x)
ratioInputs = Unit.negativeExpUnitRatio

geometricInverseAgreesWithDivisionInverse :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  BishopReal._≃_
    (Geometric.oneMinusInverse (ratioInputs inputs))
    (Division.inverse
      (Cross.gap (Cross.q x))
      (Division.qGapNonzero inputs))
geometricInverseAgreesWithDivisionInverse {x} inputs =
  BishopInverse.⁻¹-cong
    (Geometric.oneMinusNonzero (ratioInputs inputs))
    (Division.qGapNonzero inputs)
    BishopP.≃-refl

geometricReciprocalSquareAgrees :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  BishopReal._≃_
    (BishopReal._*_
      (Cross.q x)
      (BishopReal._*_
        (Geometric.oneMinusInverse (ratioInputs inputs))
        (Geometric.oneMinusInverse (ratioInputs inputs))))
    (BishopReal._*_
      (Cross.q x)
      (Division.inverseSquare
        (Cross.gap (Cross.q x))
        (Division.qGapNonzero inputs)))
geometricReciprocalSquareAgrees inputs =
  BishopP.*-congˡ
    (BishopP.*-cong
      (geometricInverseAgreesWithDivisionInverse inputs)
      (geometricInverseAgreesWithDivisionInverse inputs))

finiteNegativeExponentialDegreeOneKernel :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  ∀ cutoff →
  BishopReal._<_
    (Identity.weightedPartial (Cross.q x) cutoff)
    (Division.inverseSquare x (Division.xNonzero inputs))
finiteNegativeExponentialDegreeOneKernel {x} inputs cutoff =
  let
    finiteBound =
      Geometric.finiteDegreeOneGeometricBound
        (ratioInputs inputs) cutoff
    reciprocalBound =
      Division.negativeExpReciprocalSquareBound inputs
    geometricRhsBelow =
      BishopP.<-respˡ-≃
        (BishopP.≃-symm
          (geometricReciprocalSquareAgrees inputs))
        reciprocalBound
  in
  BishopP.≤-<-trans finiteBound geometricRhsBelow

bishopNegativeExponentialFiniteDegreeOneKernelLevel : ProofLevel
bishopNegativeExponentialFiniteDegreeOneKernelLevel = machineChecked
