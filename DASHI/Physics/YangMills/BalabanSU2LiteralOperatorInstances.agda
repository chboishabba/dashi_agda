module DASHI.Physics.YangMills.BalabanSU2LiteralOperatorInstances where

------------------------------------------------------------------------
-- Concrete SU(2) instances of the literal block-average and penalty seam.
--
-- This module closes the carrier parameters in the finite lattice lane:
-- gauge links are unit quaternions, fluctuations are pure-imaginary
-- quaternions, scalar weights are real, and the quadratic form is the invariant
-- Euclidean adjoint inner product.
--
-- The remaining inputs are genuine physical/operator data: the background
-- field U, fluctuation A, block weight, and penalty coefficient a.  No estimate
-- or determinant theorem is added.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (NonZero)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4
  ; Axis4
  )
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  ( DirectedGaugeField4
  ; GaugeFunction4
  ; gaugeTransformBond
  )
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  ( DirectedAdjointBondField4
  ; transformAdjointBondField
  )
open import DASHI.Physics.YangMills.BalabanBlockedLinearAverageMainTerm using
  ( blockedLinearAverageMainTerm
  ; blockedLinearAverageMainTermGaugeCovariant
  )
open import DASHI.Physics.YangMills.BalabanPenaltyMismatchQuadraticForm using
  ( PenaltyQuadraticModule
  ; penaltyMismatchQuadraticForm
  ; penaltyMismatchGaugeInvariant
  )
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( SU2Quaternion
  ; _+R_
  ; _*R_
  ; -R_
  ; zeroR
  ; su2QuaternionGroup
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2AdjointLinearModule
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  ( su2Dot
  ; su2DotAdjointInvariant
  ; su2ScalarAdjointLinearModule
  )

su2ScalarSubtract : ℝ → ℝ → ℝ
su2ScalarSubtract x y = x +R (-R y)

su2PenaltyQuadraticModule :
  PenaltyQuadraticModule su2QuaternionGroup
su2PenaltyQuadraticModule = record
  { scalarLinear = su2ScalarAdjointLinearModule
  ; zeroScalar = zeroR
  ; addScalar = _+R_
  ; multiplyScalar = _*R_
  ; subtractScalar = su2ScalarSubtract
  ; inner = su2Dot
  ; innerActionInvariant = su2DotAdjointInvariant
  }

SU2DirectedGaugeField4 : Nat → Set
SU2DirectedGaugeField4 N =
  DirectedGaugeField4 N su2QuaternionGroup

SU2AdjointBondField4 : Nat → Set
SU2AdjointBondField4 N =
  DirectedAdjointBondField4 N
    su2QuaternionGroup su2AdjointLinearModule

SU2BlockedAdjointBondField4 : Nat → Nat → Set
SU2BlockedAdjointBondField4 M L =
  Cube4 M → Axis4 → SU2LieAlgebra

su2BlockedLinearAverageMainTerm :
  ∀ {M L : Nat} {{_ : NonZero (M * suc L)}} →
  ℝ →
  SU2DirectedGaugeField4 (M * suc L) →
  SU2AdjointBondField4 (M * suc L) →
  SU2BlockedAdjointBondField4 M L
su2BlockedLinearAverageMainTerm =
  blockedLinearAverageMainTerm
    su2QuaternionGroup su2ScalarAdjointLinearModule

su2BlockedLinearAverageGaugeCovariant :
  ∀ {M L : Nat} {{_ : NonZero (M * suc L)}} →
  (weight : ℝ) →
  (gauge : GaugeFunction4 (M * suc L) su2QuaternionGroup) →
  (U : SU2DirectedGaugeField4 (M * suc L)) →
  (A : SU2AdjointBondField4 (M * suc L)) →
  (coarse : Cube4 M) →
  (axis : Axis4) →
  su2BlockedLinearAverageMainTerm weight
    (gaugeTransformBond su2QuaternionGroup gauge U)
    (transformAdjointBondField
      su2QuaternionGroup su2AdjointLinearModule gauge A)
    coarse axis
  ≡
  DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.su2Adjoint
    (gauge
      (DASHI.Physics.YangMills.BalabanBlockedLinearAverageMainTerm.blockOrigin
        coarse))
    (su2BlockedLinearAverageMainTerm weight U A coarse axis)
su2BlockedLinearAverageGaugeCovariant
  weight gauge U A coarse axis =
  blockedLinearAverageMainTermGaugeCovariant
    su2QuaternionGroup su2ScalarAdjointLinearModule
    weight gauge U A coarse axis

su2PenaltyMismatch :
  ∀ (M L : Nat) {{_ : NonZero (M * suc L)}} →
  ℝ →
  ℝ →
  SU2DirectedGaugeField4 (M * suc L) →
  SU2AdjointBondField4 (M * suc L) →
  ℝ
su2PenaltyMismatch M L =
  penaltyMismatchQuadraticForm M L
    su2QuaternionGroup su2PenaltyQuadraticModule

su2PenaltyMismatchGaugeInvariant :
  ∀ (M L : Nat) {{_ : NonZero (M * suc L)}} →
  (a weight : ℝ) →
  (gauge : GaugeFunction4 (M * suc L) su2QuaternionGroup) →
  (U : SU2DirectedGaugeField4 (M * suc L)) →
  (A : SU2AdjointBondField4 (M * suc L)) →
  su2PenaltyMismatch M L a weight
    (gaugeTransformBond su2QuaternionGroup gauge U)
    (transformAdjointBondField
      su2QuaternionGroup su2AdjointLinearModule gauge A)
  ≡ su2PenaltyMismatch M L a weight U A
su2PenaltyMismatchGaugeInvariant
  M L a weight gauge U A =
  penaltyMismatchGaugeInvariant
    M L su2QuaternionGroup su2PenaltyQuadraticModule
    a weight gauge U A
