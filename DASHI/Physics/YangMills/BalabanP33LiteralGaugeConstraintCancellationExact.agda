module DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CORRECTION AND CONTRIBUTION
--
-- At an exact residual background the literal gauge-fixing and CMP109
-- constraint Hessians are the positive first-derivative squares
--
--   g(h) = ||D F_A[h]||^2,
--   q(h) = ||D Q_A[h]||^2.
--
-- The side-four reference difference energy is the full componentwise
-- gradient energy.  In the flat Hodge identity it is completed jointly by the
-- Wilson curl energy and the gauge divergence energy.  Therefore gauge energy
-- must NOT be added once more to the reference and then cancelled: doing so
-- would leave Wilson - fullGradient, which equals -divergenceEnergy already at
-- the flat background.
--
-- The correct matched reference is
--
--   H_ref(h) = H_diff(h) + q(h),
--
-- so only the independent CMP109 penalty cancels.  The exact signed remainder
-- is
--
--   [H_W(h) + g(h) + q(h)] - [H_diff(h) + q(h)]
--     = H_W(h) + g(h) - H_diff(h).
--
-- Thus the load-bearing estimate is a coupled Wilson-plus-gauge Hodge
-- comparison.  This module proves that exact cancellation, the coercivity
-- promotion, and an explicit scalar counter-audit of the former overmatched
-- reference.  No estimate or normalization convention is hidden in the
-- repair.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _*_; -_; _-_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33

------------------------------------------------------------------------
-- Literal positive residual energies.
------------------------------------------------------------------------

gaugeFirstEnergy :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  Jets.LiteralPhysicalSecondVariation
    Plaquette GaugeIndex ConstraintIndex → ℚ
gaugeFirstEnergy dataSet =
  Jets.residualFirstNormSquared (Jets.gaugeResidual dataSet)

constraintFirstEnergy :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  Jets.LiteralPhysicalSecondVariation
    Plaquette GaugeIndex ConstraintIndex → ℚ
constraintFirstEnergy dataSet =
  Jets.residualFirstNormSquared (Jets.constraintResidual dataSet)

residualFirstNormSquaredNonnegative :
  ∀ {Index} (residual : Jets.FiniteResidualSecondJet Index) →
  0ℚ ≤ Jets.residualFirstNormSquared residual
residualFirstNormSquaredNonnegative residual =
  sumSquaresNonnegative (Jets.coordinates residual)
  where
  sumSquaresNonnegative : ∀ indices →
    0ℚ ≤ Jets.sumRational
      (map
        (λ index →
          Jets.jetFirst (Jets.componentJet residual index)
          * Jets.jetFirst (Jets.componentJet residual index))
        indices)
  sumSquaresNonnegative [] = ℚP.≤-refl
  sumSquaresNonnegative (index ∷ indices) =
    let
      squareNonnegative :
        0ℚ ≤ Jets.jetFirst (Jets.componentJet residual index)
          * Jets.jetFirst (Jets.componentJet residual index)
      squareNonnegative =
        FiniteL2.squareNonnegative
          (Jets.jetFirst (Jets.componentJet residual index))

      tailNonnegative = sumSquaresNonnegative indices
    in
    subst
      (λ lower →
        lower ≤
          Jets.jetFirst (Jets.componentJet residual index)
            * Jets.jetFirst (Jets.componentJet residual index)
          + Jets.sumRational
              (map
                (λ later →
                  Jets.jetFirst (Jets.componentJet residual later)
                    * Jets.jetFirst (Jets.componentJet residual later))
                indices))
      (sym (ℚP.+-identityˡ 0ℚ))
      (ℚP.+-mono-≤ squareNonnegative tailNonnegative)

gaugeFirstEnergyNonnegative :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  0ℚ ≤ gaugeFirstEnergy dataSet
gaugeFirstEnergyNonnegative dataSet =
  residualFirstNormSquaredNonnegative (Jets.gaugeResidual dataSet)

constraintFirstEnergyNonnegative :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  0ℚ ≤ constraintFirstEnergy dataSet
constraintFirstEnergyNonnegative dataSet =
  residualFirstNormSquaredNonnegative (Jets.constraintResidual dataSet)

------------------------------------------------------------------------
-- Correct matched reference: the constraint square cancels, gauge does not.
------------------------------------------------------------------------

matchedReferenceEnergy :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  Hodge.RationalBondField4 →
  Jets.LiteralPhysicalSecondVariation
    Plaquette GaugeIndex ConstraintIndex → ℚ
matchedReferenceEnergy field dataSet =
  Hodge.referenceHodgeEnergy
    field 0ℚ (constraintFirstEnergy dataSet)

matchedExactHessian :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  Jets.LiteralPhysicalSecondVariation
    Plaquette GaugeIndex ConstraintIndex → ℚ
matchedExactHessian dataSet =
  Jets.wilsonSecondVariation dataSet
  + (gaugeFirstEnergy dataSet + constraintFirstEnergy dataSet)

matchedSignedRemainder :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  Hodge.RationalBondField4 →
  Jets.LiteralPhysicalSecondVariation
    Plaquette GaugeIndex ConstraintIndex → ℚ
matchedSignedRemainder field dataSet =
  matchedExactHessian dataSet - matchedReferenceEnergy field dataSet

constraintCancellationLeavesWilsonGaugeHodgeExact :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Hodge.RationalBondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  matchedSignedRemainder field dataSet
  ≡ Jets.wilsonSecondVariation dataSet
      + gaugeFirstEnergy dataSet
      - Hodge.bondReferenceDifferenceEnergy field
constraintCancellationLeavesWilsonGaugeHodgeExact field dataSet =
  ℚRing.solve-∀
    (Jets.wilsonSecondVariation dataSet)
    (Hodge.bondReferenceDifferenceEnergy field)
    (gaugeFirstEnergy dataSet)
    (constraintFirstEnergy dataSet)

matchedReferenceRecomposesExactHessian :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Hodge.RationalBondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  P33.physicalHessianEnergy
    (matchedReferenceEnergy field dataSet)
    (matchedSignedRemainder field dataSet)
  ≡ matchedExactHessian dataSet
matchedReferenceRecomposesExactHessian field dataSet =
  ℚRing.solve-∀
    (matchedReferenceEnergy field dataSet)
    (matchedExactHessian dataSet)

literalTotalEqualsMatchedExactHessian :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  Jets.ExactResidualBackground (Jets.gaugeResidual dataSet) →
  Jets.ExactResidualBackground (Jets.constraintResidual dataSet) →
  Jets.literalTotalSecondVariation dataSet ≡ matchedExactHessian dataSet
literalTotalEqualsMatchedExactHessian dataSet gaugeExact constraintExact =
  Jets.literalTotalSecondVariationAtExactBackground
    dataSet gaugeExact constraintExact

------------------------------------------------------------------------
-- Counter-audit of the former overmatched reference.
------------------------------------------------------------------------

oldOvermatchedReference : ℚ → ℚ → ℚ → ℚ
oldOvermatchedReference fullGradient gaugeEnergy constraintEnergy =
  fullGradient + (gaugeEnergy + constraintEnergy)

literalExactScalarHessian : ℚ → ℚ → ℚ → ℚ
literalExactScalarHessian wilsonEnergy gaugeEnergy constraintEnergy =
  wilsonEnergy + (gaugeEnergy + constraintEnergy)

oldOvermatchedRemainder : ℚ → ℚ → ℚ → ℚ → ℚ
oldOvermatchedRemainder wilsonEnergy fullGradient gaugeEnergy constraintEnergy =
  literalExactScalarHessian wilsonEnergy gaugeEnergy constraintEnergy
  - oldOvermatchedReference fullGradient gaugeEnergy constraintEnergy

oldOvermatchedRemainderCancelsGaugeAlgebraically :
  ∀ wilsonEnergy fullGradient gaugeEnergy constraintEnergy →
  oldOvermatchedRemainder
    wilsonEnergy fullGradient gaugeEnergy constraintEnergy
  ≡ wilsonEnergy - fullGradient
oldOvermatchedRemainderCancelsGaugeAlgebraically = ℚRing.solve-∀

flatHodgeOldRemainderIsNegativeGauge :
  ∀ curlEnergy gaugeEnergy constraintEnergy →
  oldOvermatchedRemainder
    curlEnergy (curlEnergy + gaugeEnergy) gaugeEnergy constraintEnergy
  ≡ - gaugeEnergy
flatHodgeOldRemainderIsNegativeGauge = ℚRing.solve-∀

oldShortcutUnitGaugeWitness :
  oldOvermatchedRemainder
    0ℚ (+ 1 / 1) (+ 1 / 1) 0ℚ
  ≡ - (+ 1 / 1)
oldShortcutUnitGaugeWitness = ℚRing.solve []

correctMatchedReference : ℚ → ℚ → ℚ
correctMatchedReference fullGradient constraintEnergy =
  fullGradient + constraintEnergy

correctMatchedRemainder : ℚ → ℚ → ℚ → ℚ → ℚ
correctMatchedRemainder wilsonEnergy fullGradient gaugeEnergy constraintEnergy =
  literalExactScalarHessian wilsonEnergy gaugeEnergy constraintEnergy
  - correctMatchedReference fullGradient constraintEnergy

flatHodgeCorrectRemainderIsZero :
  ∀ curlEnergy gaugeEnergy constraintEnergy →
  correctMatchedRemainder
    curlEnergy (curlEnergy + gaugeEnergy) gaugeEnergy constraintEnergy
  ≡ 0ℚ
flatHodgeCorrectRemainderIsZero = ℚRing.solve-∀

------------------------------------------------------------------------
-- Coercivity depends on the coupled Wilson-plus-gauge Hodge remainder.
------------------------------------------------------------------------

literalHessianCoerciveFromWilsonGaugeHodgeDifference :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Hodge.RationalBondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  Hodge.BondComponentMeanZero field →
  Jets.ExactResidualBackground (Jets.gaugeResidual dataSet) →
  Jets.ExactResidualBackground (Jets.constraintResidual dataSet) →
  - (P33.p33PhysicalFloor * Hodge.bondNormSq field)
    ≤ Jets.wilsonSecondVariation dataSet
        + gaugeFirstEnergy dataSet
        - Hodge.bondReferenceDifferenceEnergy field →
  P33.p33PhysicalFloor * Hodge.bondNormSq field
    ≤ Jets.literalTotalSecondVariation dataSet
literalHessianCoerciveFromWilsonGaugeHodgeDifference
    field dataSet meanZero gaugeExact constraintExact coupledLower =
  let
    matchedLower :
      - (P33.p33PhysicalFloor * Hodge.bondNormSq field)
      ≤ matchedSignedRemainder field dataSet
    matchedLower =
      subst
        (λ remainder →
          - (P33.p33PhysicalFloor * Hodge.bondNormSq field)
          ≤ remainder)
        (sym (constraintCancellationLeavesWilsonGaugeHodgeExact
          field dataSet))
        coupledLower

    referenceCoercive :
      P33.p33PhysicalFloor * Hodge.bondNormSq field
      ≤ P33.physicalHessianEnergy
          (matchedReferenceEnergy field dataSet)
          (matchedSignedRemainder field dataSet)
    referenceCoercive =
      P33.path4SignedRemainderCoercive
        field
        0ℚ
        (constraintFirstEnergy dataSet)
        (matchedSignedRemainder field dataSet)
        meanZero
        ℚP.≤-refl
        (constraintFirstEnergyNonnegative dataSet)
        matchedLower

    matchedCoercive :
      P33.p33PhysicalFloor * Hodge.bondNormSq field
      ≤ matchedExactHessian dataSet
    matchedCoercive =
      subst
        (λ upper →
          P33.p33PhysicalFloor * Hodge.bondNormSq field ≤ upper)
        (matchedReferenceRecomposesExactHessian field dataSet)
        referenceCoercive
  in
  subst
    (λ upper →
      P33.p33PhysicalFloor * Hodge.bondNormSq field ≤ upper)
    (sym (literalTotalEqualsMatchedExactHessian
      dataSet gaugeExact constraintExact))
    matchedCoercive

literalConstraintCancellationLevel : ProofLevel
literalConstraintCancellationLevel = machineChecked

literalGaugeMustRemainInHodgeRemainderLevel : ProofLevel
literalGaugeMustRemainInHodgeRemainderLevel = machineChecked

oldOvermatchedReferenceCounterAuditLevel : ProofLevel
oldOvermatchedReferenceCounterAuditLevel = machineChecked

literalWilsonGaugeHodgeCoercivityLevel : ProofLevel
literalWilsonGaugeHodgeCoercivityLevel = machineChecked
