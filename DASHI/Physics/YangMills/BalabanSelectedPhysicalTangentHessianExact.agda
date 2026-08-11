module DASHI.Physics.YangMills.BalabanSelectedPhysicalTangentHessianExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Close an important same-object seam in the finite coercivity endpoint.  The
-- existing selected 1/32 theorem is stated for the literal Wilson Hessian plus
-- the squared gauge/block-residual Hessians.  At an exact residual background,
-- a genuine physical tangent vector additionally satisfies
--
--       DF_A[h] = 0,   DQ_A[h] = 0.
--
-- Hence the two residual first-norm terms vanish for the same h, and the
-- literal total second variation is exactly the Wilson action second variation.
-- Therefore the existing 1/32 lower bound descends to the physical Wilson
-- Hessian itself on the linearized constraint kernel.
--
-- This theorem does not identify the nonlinear tangent space by itself.  That
-- remains the quantitative implicit-function/orbit theorem.  It proves the
-- exact algebraic implication needed once those physical tangent first-zero
-- witnesses are supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeResidualExact as GaugeResidual
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as WilsonGlobal
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanP33SelectedBackgroundFiniteCoercivityExact as Selected

record ResidualFirstZero {Index : Set}
    (residual : Jets.FiniteResidualSecondJet Index) : Set₁ where
  field
    firstZero : ∀ index →
      Jets.jetFirst (Jets.componentJet residual index) ≡ 0ℚ

open ResidualFirstZero public

residualFirstNormSquaredZero :
  ∀ {Index} (residual : Jets.FiniteResidualSecondJet Index) →
  ResidualFirstZero residual →
  Jets.residualFirstNormSquared residual ≡ 0ℚ
residualFirstNormSquaredZero residual tangent =
  Jets.sumRationalCong
    (λ index →
      Jets.jetFirst (Jets.componentJet residual index)
        * Jets.jetFirst (Jets.componentJet residual index))
    (λ _ → 0ℚ)
    (Jets.coordinates residual)
    (λ index →
      trans
        (cong₂ _*_
          (firstZero tangent index)
          (firstZero tangent index))
        (ℚRing.solve []))

record SelectedPhysicalConstraintTangent
    {Perturbation ConstraintIndex : Set}
    (model : Selected.SelectedBackgroundPerturbationModel
      Perturbation ConstraintIndex)
    (h : Perturbation) : Set₁ where
  field
    gaugeFirstZero :
      ResidualFirstZero
        (Jets.gaugeResidual (Selected.selectedLiteralSecondVariation model h))
    blockConstraintFirstZero :
      ResidualFirstZero
        (Jets.constraintResidual (Selected.selectedLiteralSecondVariation model h))

open SelectedPhysicalConstraintTangent public

selectedTangentTotalEqualsWilson :
  ∀ {Perturbation ConstraintIndex}
    (model : Selected.SelectedBackgroundPerturbationModel
      Perturbation ConstraintIndex)
    h →
  SelectedPhysicalConstraintTangent model h →
  Jets.literalTotalSecondVariation
      (Selected.selectedLiteralSecondVariation model h)
  ≡ Jets.wilsonSecondVariation
      (Selected.selectedLiteralSecondVariation model h)
selectedTangentTotalEqualsWilson model h tangent =
  let
    dataSet = Selected.selectedLiteralSecondVariation model h

    gaugeFirstNormZero :
      Jets.residualFirstNormSquared (Jets.gaugeResidual dataSet) ≡ 0ℚ
    gaugeFirstNormZero = residualFirstNormSquaredZero
      (Jets.gaugeResidual dataSet) (gaugeFirstZero tangent)

    blockFirstNormZero :
      Jets.residualFirstNormSquared (Jets.constraintResidual dataSet) ≡ 0ℚ
    blockFirstNormZero = residualFirstNormSquaredZero
      (Jets.constraintResidual dataSet) (blockConstraintFirstZero tangent)

    gaugeExact :
      Jets.ExactResidualBackground (Jets.gaugeResidual dataSet)
    gaugeExact = GaugeResidual.backgroundGaugeResidualExact
      (Selected.backgroundOf model h) (Selected.physicalFieldOf model h)

    exactCollapse = Jets.literalTotalSecondVariationAtExactBackground
      dataSet gaugeExact (Selected.constraintExact model h)
  in
  trans exactCollapse
    (trans
      (cong
        (λ residualTerms → Jets.wilsonSecondVariation dataSet + residualTerms)
        (trans
          (cong₂ _+_ gaugeFirstNormZero blockFirstNormZero)
          (ℚRing.solve [])))
      (ℚRing.solve-∀ (Jets.wilsonSecondVariation dataSet)))

selectedPhysicalWilsonHessianOneThirtySecond :
  ∀ {Perturbation ConstraintIndex}
    (model : Selected.SelectedBackgroundPerturbationModel
      Perturbation ConstraintIndex)
    h →
  Relaxed.RelaxedInverseLinkRadius (Selected.backgroundOf model h) →
  WilsonGlobal.PhysicalWilsonSignedLocal
    (Selected.backgroundOf model h) (Selected.physicalFieldOf model h) →
  SelectedPhysicalConstraintTangent model h →
  P33.p33PhysicalFloor
      * Coordinates.physicalSU2BondNormSq (Selected.physicalFieldOf model h)
  ≤ Jets.wilsonSecondVariation
      (Selected.selectedLiteralSecondVariation model h)
selectedPhysicalWilsonHessianOneThirtySecond model h radius local tangent =
  subst
    (λ upper →
      P33.p33PhysicalFloor
        * Coordinates.physicalSU2BondNormSq (Selected.physicalFieldOf model h)
      ≤ upper)
    (selectedTangentTotalEqualsWilson model h tangent)
    (Selected.selectedBackgroundLiteralHessianOneThirtySecond
      model h radius local)

selectedPhysicalTangentPenaltyCollapseLevel : ProofLevel
selectedPhysicalTangentPenaltyCollapseLevel = machineChecked

selectedPhysicalWilsonHessianOneThirtySecondLevel : ProofLevel
selectedPhysicalWilsonHessianOneThirtySecondLevel = machineChecked
