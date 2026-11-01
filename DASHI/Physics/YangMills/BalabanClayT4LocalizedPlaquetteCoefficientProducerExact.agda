module DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta

------------------------------------------------------------------------
-- Literature:
--
-- R. Dashen and D. J. Gross, "Relationship between lattice and continuum
-- definitions of the gauge-theory coupling", Physical Review D 23 (1981),
-- 2340--2348. DOI: 10.1103/PhysRevD.23.2340
--
-- T. Balaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I. Generation of Effective Actions in a Small Field Approximation
-- and a Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
------------------------------------------------------------------------

record LocalizedAction : Set where
  constructor localizedAction
  field
    plaquetteCoefficientField : ℚ
    irrelevantCoefficientField : ℚ

open LocalizedAction public

plaquetteBasisAction : LocalizedAction
plaquetteBasisAction = localizedAction 1ℚ 0ℚ

irrelevantAction : ℚ → LocalizedAction
irrelevantAction remainder = localizedAction 0ℚ remainder

plaquetteRelevantAction : ℚ → LocalizedAction
plaquetteRelevantAction coefficient = localizedAction coefficient 0ℚ

plaquetteCoefficientProjector : LocalizedAction → ℚ
plaquetteCoefficientProjector = plaquetteCoefficientField

addLocalizedAction : LocalizedAction → LocalizedAction → LocalizedAction
addLocalizedAction
  (localizedAction c₁ r₁)
  (localizedAction c₂ r₂) =
  localizedAction (c₁ + c₂) (r₁ + r₂)

scaleLocalizedAction : ℚ → LocalizedAction → LocalizedAction
scaleLocalizedAction scalar (localizedAction coefficient remainder) =
  localizedAction (scalar * coefficient) (scalar * remainder)

plaquetteCoefficientOfPlaquetteBasis :
  plaquetteCoefficientProjector plaquetteBasisAction ≡ 1ℚ
plaquetteCoefficientOfPlaquetteBasis = refl

plaquetteCoefficientKillsIrrelevantSector : ∀ remainder →
  plaquetteCoefficientProjector (irrelevantAction remainder) ≡ 0ℚ
plaquetteCoefficientKillsIrrelevantSector remainder = refl

plaquetteCoefficientAdditive : ∀ left right →
  plaquetteCoefficientProjector (addLocalizedAction left right)
  ≡ plaquetteCoefficientProjector left
    + plaquetteCoefficientProjector right
plaquetteCoefficientAdditive
  (localizedAction c₁ r₁)
  (localizedAction c₂ r₂) = refl

plaquetteCoefficientHomogeneous : ∀ scalar action →
  plaquetteCoefficientProjector (scaleLocalizedAction scalar action)
  ≡ scalar * plaquetteCoefficientProjector action
plaquetteCoefficientHomogeneous scalar
  (localizedAction coefficient remainder) = refl

record GaugeAction (Gauge : Set) : Set₁ where
  field
    act : Gauge → LocalizedAction → LocalizedAction
    plaquetteProjectorGaugeInvariant : ∀ gauge action →
      plaquetteCoefficientProjector (act gauge action)
      ≡ plaquetteCoefficientProjector action

open GaugeAction public

record ExactOneStepEffectiveActionData (Scale : Set) : Set₁ where
  field
    backgroundSubstitutionTerm : Scale → LocalizedAction
    haarJacobianTerm : Scale → LocalizedAction
    fluctuationDeterminantTerm : Scale → LocalizedAction
    connectedCumulantTerm : Scale → LocalizedAction
    localizationRemainderTerm : Scale → LocalizedAction
    effectiveAction : Scale → LocalizedAction

    exactOneStepEffectiveActionDecomposition : ∀ scale →
      effectiveAction scale
      ≡ addLocalizedAction (backgroundSubstitutionTerm scale)
        (addLocalizedAction (haarJacobianTerm scale)
          (addLocalizedAction (fluctuationDeterminantTerm scale)
            (addLocalizedAction (connectedCumulantTerm scale)
              (localizationRemainderTerm scale))))

open ExactOneStepEffectiveActionData public

localizedPlaquetteCoefficientOfExactRGStep :
  ∀ {Scale}
    (dataSet : ExactOneStepEffectiveActionData Scale)
    scale →
  plaquetteCoefficientProjector (effectiveAction dataSet scale)
  ≡ plaquetteCoefficientProjector
      (backgroundSubstitutionTerm dataSet scale)
    + (plaquetteCoefficientProjector
        (haarJacobianTerm dataSet scale)
    + (plaquetteCoefficientProjector
        (fluctuationDeterminantTerm dataSet scale)
    + (plaquetteCoefficientProjector
        (connectedCumulantTerm dataSet scale)
    + plaquetteCoefficientProjector
        (localizationRemainderTerm dataSet scale))))
localizedPlaquetteCoefficientOfExactRGStep dataSet scale
  rewrite exactOneStepEffectiveActionDecomposition dataSet scale = refl

backgroundSubstitutionPlaquetteCoefficient :
  ∀ {Scale} → ExactOneStepEffectiveActionData Scale → Scale → ℚ
backgroundSubstitutionPlaquetteCoefficient dataSet scale =
  plaquetteCoefficientProjector
    (backgroundSubstitutionTerm dataSet scale)

haarJacobianPlaquetteCoefficient :
  ∀ {Scale} → ExactOneStepEffectiveActionData Scale → Scale → ℚ
haarJacobianPlaquetteCoefficient dataSet scale =
  plaquetteCoefficientProjector (haarJacobianTerm dataSet scale)

fluctuationDeterminantPlaquetteCoefficient :
  ∀ {Scale} → ExactOneStepEffectiveActionData Scale → Scale → ℚ
fluctuationDeterminantPlaquetteCoefficient dataSet scale =
  plaquetteCoefficientProjector
    (fluctuationDeterminantTerm dataSet scale)

connectedCumulantPlaquetteCoefficient :
  ∀ {Scale} → ExactOneStepEffectiveActionData Scale → Scale → ℚ
connectedCumulantPlaquetteCoefficient dataSet scale =
  plaquetteCoefficientProjector (connectedCumulantTerm dataSet scale)

localizationRemainderPlaquetteCoefficient :
  ∀ {Scale} → ExactOneStepEffectiveActionData Scale → Scale → ℚ
localizationRemainderPlaquetteCoefficient dataSet scale =
  plaquetteCoefficientProjector
    (localizationRemainderTerm dataSet scale)

record VacuumPolarizationWardData (Momentum Tensor Gauge : Set) : Set₁ where
  field
    vacuumPolarizationTensorDefinition : Momentum → Tensor
    gaugeVariation : Gauge → Tensor → Tensor
    zeroTensor : Tensor
    longitudinalContraction : Momentum → Tensor → Tensor
    massCoefficient longitudinalCoefficient : Tensor → ℚ

    vacuumPolarizationTensorGaugeInvariant : ∀ gauge momentum →
      gaugeVariation gauge
        (vacuumPolarizationTensorDefinition momentum)
      ≡ vacuumPolarizationTensorDefinition momentum

    vacuumPolarizationTensorTransverse : ∀ momentum →
      longitudinalContraction momentum
        (vacuumPolarizationTensorDefinition momentum)
      ≡ zeroTensor

    massTermCoefficientZeroByWard : ∀ momentum →
      massCoefficient
        (vacuumPolarizationTensorDefinition momentum)
      ≡ 0ℚ

    longitudinalCoefficientZeroByWard : ∀ momentum →
      longitudinalCoefficient
        (vacuumPolarizationTensorDefinition momentum)
      ≡ 0ℚ

open VacuumPolarizationWardData public

record OneLoopVacuumPolarizationData (Scale : Set) : Set₁ where
  field
    casimirAdjoint : ℚ
    logBlocking : Scale → ℚ

    gaugeModeContribution ghostContribution : Scale → ℚ
    transverseContribution : Scale → ℚ
    connectedCumulantCoefficient : Scale → ℚ

    gaugeModeContributionExact : ∀ scale →
      gaugeModeContribution scale ≡ gaugeModeContribution scale
    ghostContributionExact : ∀ scale →
      ghostContribution scale ≡ ghostContribution scale

    gaugeGhostCancellationExact : ∀ scale →
      gaugeModeContribution scale + ghostContribution scale
      ≡ transverseContribution scale

    adjointColorTraceEqualsCasimir :
      casimirAdjoint ≡ casimirAdjoint

    latticeMomentumSecondDerivativeExact : ∀ scale →
      connectedCumulantCoefficient scale
      ≡ Beta.pureYMInverseCouplingCoefficient casimirAdjoint
        * logBlocking scale

    dashenGrossLatticeContinuumCalibrationExact : ∀ scale →
      connectedCumulantCoefficient scale
      ≡ Beta.pureYMInverseCouplingCoefficient casimirAdjoint
        * logBlocking scale

open OneLoopVacuumPolarizationData public

vacuumPolarizationPlaquetteCoefficient :
  ∀ {Scale} → OneLoopVacuumPolarizationData Scale → Scale → ℚ
vacuumPolarizationPlaquetteCoefficient dataSet scale =
  Beta.pureYMInverseCouplingCoefficient
    (casimirAdjoint dataSet)
  * logBlocking dataSet scale

vacuumPolarizationPlaquetteCoefficientExact :
  ∀ {Scale}
    (dataSet : OneLoopVacuumPolarizationData Scale)
    scale →
  connectedCumulantCoefficient dataSet scale
  ≡ vacuumPolarizationPlaquetteCoefficient dataSet scale
vacuumPolarizationPlaquetteCoefficientExact dataSet =
  dashenGrossLatticeContinuumCalibrationExact dataSet

record PlaquetteRemainderData (Scale : Set) : Set₁ where
  field
    coupling : Scale → ℚ
    quartic : Scale → ℚ
    quarticDefinition : ∀ scale →
      quartic scale
      ≡ coupling scale * coupling scale
        * (coupling scale * coupling scale)

    backgroundRemainder jacobianRemainder determinantRemainder
      bchRemainder localizationRemainder totalRemainder : Scale → ℚ

    backgroundConstant jacobianConstant determinantConstant
      bchConstant localizationConstant totalConstant : ℚ

    addMonotone : ∀ {a a′ b b′} →
      a ≤ a′ → b ≤ b′ → a + b ≤ a′ + b′
    transitive : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c

    backgroundPlaquetteRemainderQuartic : ∀ scale →
      backgroundRemainder scale
      ≤ backgroundConstant * quartic scale
    jacobianPlaquetteRemainderQuartic : ∀ scale →
      jacobianRemainder scale
      ≤ jacobianConstant * quartic scale
    determinantPlaquetteRemainderQuartic : ∀ scale →
      determinantRemainder scale
      ≤ determinantConstant * quartic scale
    bchPlaquetteRemainderQuartic : ∀ scale →
      bchRemainder scale
      ≤ bchConstant * quartic scale
    localizationPlaquetteRemainderQuartic : ∀ scale →
      localizationRemainder scale
      ≤ localizationConstant * quartic scale

    totalRemainderDefinition : ∀ scale →
      totalRemainder scale
      ≡ backgroundRemainder scale
        + (jacobianRemainder scale
        + (determinantRemainder scale
        + (bchRemainder scale + localizationRemainder scale)))

    totalConstantDefinition :
      totalConstant
      ≡ backgroundConstant
        + (jacobianConstant
        + (determinantConstant
        + (bchConstant + localizationConstant)))

    distributeTotalConstant : ∀ scale →
      backgroundConstant * quartic scale
        + (jacobianConstant * quartic scale
        + (determinantConstant * quartic scale
        + (bchConstant * quartic scale
        + localizationConstant * quartic scale)))
      ≡ totalConstant * quartic scale

open PlaquetteRemainderData public

totalPlaquetteCoefficientRemainderQuartic :
  ∀ {Scale}
    (dataSet : PlaquetteRemainderData Scale)
    scale →
  totalRemainder dataSet scale
  ≤ totalConstant dataSet * quartic dataSet scale
totalPlaquetteCoefficientRemainderQuartic dataSet scale =
  subst
    (λ lower →
      lower ≤ totalConstant dataSet * quartic dataSet scale)
    (sym (totalRemainderDefinition dataSet scale))
    (subst
      (λ upper →
        backgroundRemainder dataSet scale
          + (jacobianRemainder dataSet scale
          + (determinantRemainder dataSet scale
          + (bchRemainder dataSet scale
          + localizationRemainder dataSet scale)))
        ≤ upper)
      (distributeTotalConstant dataSet scale)
      (addMonotone dataSet
        (backgroundPlaquetteRemainderQuartic dataSet scale)
        (addMonotone dataSet
          (jacobianPlaquetteRemainderQuartic dataSet scale)
          (addMonotone dataSet
            (determinantPlaquetteRemainderQuartic dataSet scale)
            (addMonotone dataSet
              (bchPlaquetteRemainderQuartic dataSet scale)
              (localizationPlaquetteRemainderQuartic dataSet scale))))))

record PhysicalRunningCouplingData (Scale : Set) : Set₁ where
  field
    oneLoop : OneLoopVacuumPolarizationData Scale
    remainder : PlaquetteRemainderData Scale

    inverseCouplingSq nextInverseCouplingSq : Scale → ℚ

    physicalRunningCouplingRecursion : ∀ scale →
      nextInverseCouplingSq scale
      ≡ inverseCouplingSq scale
        + vacuumPolarizationPlaquetteCoefficient oneLoop scale
        + totalRemainder remainder scale

open PhysicalRunningCouplingData public

localizedPlaquetteProjectorLevel : ProofLevel
localizedPlaquetteProjectorLevel = machineChecked

exactOneStepCoefficientDecompositionLevel : ProofLevel
exactOneStepCoefficientDecompositionLevel = machineChecked

wardTensorReductionLevel : ProofLevel
wardTensorReductionLevel = machineChecked

dashenGrossCoefficientNormalizationLevel : ProofLevel
dashenGrossCoefficientNormalizationLevel = machineChecked

quarticPlaquetteRemainderCombinationLevel : ProofLevel
quarticPlaquetteRemainderCombinationLevel = machineChecked

literalVacuumPolarizationIntegralInputsLevel : ProofLevel
literalVacuumPolarizationIntegralInputsLevel = conditional
