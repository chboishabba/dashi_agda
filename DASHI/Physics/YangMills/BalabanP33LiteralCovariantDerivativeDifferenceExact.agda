module DASHI.Physics.YangMills.BalabanP33LiteralCovariantDerivativeDifferenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- On the literal directed periodic bond carrier, prove the exact identity
--
--   (D_U phi)(b) - (D_1 phi)(b)
--     = (Ad(U(b))-I) phi(b+).
--
-- This removes the covariant-derivative difference from the primitive physical
-- assumptions.  A normed adjoint-action application theorem then turns any
-- proved bound on ||Ad(U(b))-I|| into the corresponding pointwise bound for
-- D_U-D_1.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Tactic.RingSolver as Solver

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using
  (DirectedBond4; source; target)
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  (DirectedGaugeField4)
import DASHI.Physics.YangMills.BalabanLatticeAdjointCovariantDerivative as Derivative
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (SU2Quaternion; su2Identity; su2QuaternionGroup; realSolverRing)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; su2Lie; su2LieExt; lieSubtract; su2Adjoint
  ; su2AdjointUnit; su2AdjointAdditiveModule)

unitDirectedGauge :
  ∀ {N : Nat} →
  DirectedGaugeField4 N su2QuaternionGroup
unitDirectedGauge _ = su2Identity

lieSubtractCommonRight :
  ∀ left middle right →
  lieSubtract (lieSubtract left right) (lieSubtract middle right)
  ≡ lieSubtract left middle
lieSubtractCommonRight
    (su2Lie leftX leftY leftZ)
    (su2Lie middleX middleY middleZ)
    (su2Lie rightX rightY rightZ) =
  su2LieExt
    (Solver.solve
      (leftX ∷ middleX ∷ rightX ∷ []) realSolverRing)
    (Solver.solve
      (leftY ∷ middleY ∷ rightY ∷ []) realSolverRing)
    (Solver.solve
      (leftZ ∷ middleZ ∷ rightZ ∷ []) realSolverRing)

adjointDefect : SU2Quaternion → SU2LieAlgebra → SU2LieAlgebra
adjointDefect groupElement vector =
  lieSubtract (su2Adjoint groupElement vector) vector

covariantDerivativeDifference :
  ∀ {N : Nat} {{_ : NonZero N}} →
  DirectedGaugeField4 N su2QuaternionGroup →
  Derivative.PointAdjointField4
    N su2QuaternionGroup su2AdjointAdditiveModule →
  DirectedBond4 N →
  SU2LieAlgebra
covariantDerivativeDifference gaugeField pointField bond =
  lieSubtract
    (Derivative.covariantDerivative
      su2QuaternionGroup su2AdjointAdditiveModule
      gaugeField pointField bond)
    (Derivative.covariantDerivative
      su2QuaternionGroup su2AdjointAdditiveModule
      unitDirectedGauge pointField bond)

covariantDerivativeDifferenceExact :
  ∀ {N : Nat} {{_ : NonZero N}}
    (gaugeField : DirectedGaugeField4 N su2QuaternionGroup)
    (pointField : Derivative.PointAdjointField4
      N su2QuaternionGroup su2AdjointAdditiveModule)
    (bond : DirectedBond4 N) →
  covariantDerivativeDifference gaugeField pointField bond
  ≡ adjointDefect (gaugeField bond) (pointField (target bond))
covariantDerivativeDifferenceExact gaugeField pointField bond
  rewrite su2AdjointUnit (pointField (target bond)) =
  lieSubtractCommonRight
    (su2Adjoint (gaugeField bond) (pointField (target bond)))
    (pointField (target bond))
    (pointField (source bond))

record NormedAdjointDefectApplication (Bound : Set) : Set₁ where
  field
    vectorNorm : SU2LieAlgebra → Bound
    defectOperatorNorm : SU2Quaternion → Bound
    multiplyBound : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    adjointDefectApplicationBound : ∀ groupElement vector →
      LessEqual
        (vectorNorm (adjointDefect groupElement vector))
        (multiplyBound
          (defectOperatorNorm groupElement)
          (vectorNorm vector))

open NormedAdjointDefectApplication public

covariantDerivativeDifferenceNormBound :
  ∀ {N : Nat} {{_ : NonZero N}} {Bound}
    (normed : NormedAdjointDefectApplication Bound)
    (gaugeField : DirectedGaugeField4 N su2QuaternionGroup)
    (pointField : Derivative.PointAdjointField4
      N su2QuaternionGroup su2AdjointAdditiveModule)
    (bond : DirectedBond4 N) →
  LessEqual normed
    (vectorNorm normed
      (covariantDerivativeDifference gaugeField pointField bond))
    (multiplyBound normed
      (defectOperatorNorm normed (gaugeField bond))
      (vectorNorm normed (pointField (target bond))))
covariantDerivativeDifferenceNormBound
    normed gaugeField pointField bond =
  subst
    (λ selected →
      LessEqual normed
        (vectorNorm normed selected)
        (multiplyBound normed
          (defectOperatorNorm normed (gaugeField bond))
          (vectorNorm normed (pointField (target bond)))))
    (sym (covariantDerivativeDifferenceExact gaugeField pointField bond))
    (adjointDefectApplicationBound normed
      (gaugeField bond) (pointField (target bond)))

literalCovariantDerivativeDifferenceLevel : ProofLevel
literalCovariantDerivativeDifferenceLevel = machineChecked

literalCovariantDerivativeAdjointDefectLevel : ProofLevel
literalCovariantDerivativeAdjointDefectLevel = machineChecked

covariantDerivativePointwiseNormReductionLevel : ProofLevel
covariantDerivativePointwiseNormReductionLevel = machineChecked
