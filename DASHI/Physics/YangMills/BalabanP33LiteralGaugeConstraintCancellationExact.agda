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
-- The physical reference difference energy is the sum of the open side-four
-- difference energies of all three su(2) components.  Gauge energy is part of
-- the flat curl-plus-divergence completion of that full gradient energy and
-- must remain in the signed Hodge remainder.  Only the independent constraint
-- square is matched into the reference and cancelled:
--
--   [H_W(h)+g(h)+q(h)] - [H_diff^SU2(h)+q(h)]
--     = H_W(h)+g(h)-H_diff^SU2(h).
--
-- The previous scalar-field version also paired a total Wilson scalar with one
-- scalar bond component.  This module now uses the actual three-component
-- physical perturbation and its exact 3072-coordinate norm.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _-_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2HodgeCoercivityExact as PhysicalHodge
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate as LDL

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
-- Correct physical matched reference: only the constraint square cancels.
------------------------------------------------------------------------

matchedReferenceEnergy :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  Physical.PhysicalSU2BondField4 →
  Jets.LiteralPhysicalSecondVariation
    Plaquette GaugeIndex ConstraintIndex → ℚ
matchedReferenceEnergy field dataSet =
  PhysicalHodge.physicalReferenceHodgeEnergy
    field (constraintFirstEnergy dataSet)

matchedExactHessian :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  Jets.LiteralPhysicalSecondVariation
    Plaquette GaugeIndex ConstraintIndex → ℚ
matchedExactHessian dataSet =
  Jets.wilsonSecondVariation dataSet
  + (gaugeFirstEnergy dataSet + constraintFirstEnergy dataSet)

matchedSignedRemainder :
  ∀ {Plaquette GaugeIndex ConstraintIndex} →
  Physical.PhysicalSU2BondField4 →
  Jets.LiteralPhysicalSecondVariation
    Plaquette GaugeIndex ConstraintIndex → ℚ
matchedSignedRemainder field dataSet =
  matchedExactHessian dataSet - matchedReferenceEnergy field dataSet

constraintCancellationLeavesWilsonGaugeHodgeExact :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Physical.PhysicalSU2BondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  matchedSignedRemainder field dataSet
  ≡ Jets.wilsonSecondVariation dataSet
      + gaugeFirstEnergy dataSet
      - PhysicalHodge.physicalReferenceDifferenceEnergy field
constraintCancellationLeavesWilsonGaugeHodgeExact field dataSet =
  ℚRing.solve-∀
    (Jets.wilsonSecondVariation dataSet)
    (PhysicalHodge.physicalReferenceDifferenceEnergy field)
    (gaugeFirstEnergy dataSet)
    (constraintFirstEnergy dataSet)

matchedReferenceRecomposesExactHessian :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Physical.PhysicalSU2BondField4)
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
-- Counter-audit of the former overmatched scalar reference.
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
-- Physical coercivity from the coupled Wilson-plus-gauge Hodge remainder.
------------------------------------------------------------------------

physicalHalfFloorCancellationIdentity : ∀ normSq →
  P33.p33PhysicalFloor * normSq
  ≡ LDL.oneSixteenth * normSq
    + - (P33.p33PhysicalFloor * normSq)
physicalHalfFloorCancellationIdentity = ℚRing.solve-∀

literalHessianCoerciveFromWilsonGaugeHodgeDifference :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Physical.PhysicalSU2BondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  PhysicalHodge.PhysicalBondComponentMeanZero field →
  Jets.ExactResidualBackground (Jets.gaugeResidual dataSet) →
  Jets.ExactResidualBackground (Jets.constraintResidual dataSet) →
  - (P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq field)
    ≤ Jets.wilsonSecondVariation dataSet
        + gaugeFirstEnergy dataSet
        - PhysicalHodge.physicalReferenceDifferenceEnergy field →
  P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq field
    ≤ Jets.literalTotalSecondVariation dataSet
literalHessianCoerciveFromWilsonGaugeHodgeDifference
    field dataSet meanZero gaugeExact constraintExact coupledLower =
  let
    matchedLower :
      - (P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq field)
      ≤ matchedSignedRemainder field dataSet
    matchedLower =
      subst
        (λ remainder →
          - (P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq field)
          ≤ remainder)
        (sym (constraintCancellationLeavesWilsonGaugeHodgeExact
          field dataSet))
        coupledLower

    referenceLower :
      LDL.oneSixteenth * Physical.physicalSU2BondNormSq field
      ≤ matchedReferenceEnergy field dataSet
    referenceLower =
      PhysicalHodge.physicalReferenceHodgeCoercivity
        field (constraintFirstEnergy dataSet)
        meanZero (constraintFirstEnergyNonnegative dataSet)

    assembledLower :
      P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq field
      ≤ P33.physicalHessianEnergy
          (matchedReferenceEnergy field dataSet)
          (matchedSignedRemainder field dataSet)
    assembledLower =
      subst
        (λ lower →
          lower
          ≤ P33.physicalHessianEnergy
              (matchedReferenceEnergy field dataSet)
              (matchedSignedRemainder field dataSet))
        (sym
          (physicalHalfFloorCancellationIdentity
            (Physical.physicalSU2BondNormSq field)))
        (ℚP.+-mono-≤ referenceLower matchedLower)

    exactLower :
      P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq field
      ≤ matchedExactHessian dataSet
    exactLower =
      subst
        (λ upper →
          P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq field
          ≤ upper)
        (matchedReferenceRecomposesExactHessian field dataSet)
        assembledLower
  in
  subst
    (λ upper →
      P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq field
      ≤ upper)
    (sym (literalTotalEqualsMatchedExactHessian
      dataSet gaugeExact constraintExact))
    exactLower

literalConstraintCancellationLevel : ProofLevel
literalConstraintCancellationLevel = machineChecked

literalGaugeMustRemainInHodgeRemainderLevel : ProofLevel
literalGaugeMustRemainInHodgeRemainderLevel = machineChecked

oldOvermatchedReferenceCounterAuditLevel : ProofLevel
oldOvermatchedReferenceCounterAuditLevel = machineChecked

literalPhysicalWilsonGaugeHodgeCoercivityLevel : ProofLevel
literalPhysicalWilsonGaugeHodgeCoercivityLevel = machineChecked
