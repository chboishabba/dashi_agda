module DASHI.Physics.YangMills.BalabanSelectedSinglePlaquetteWitnessExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
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
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Compress the Gate-I physical producer to one vertical single-plaquette
-- object.  The constraint operator, Gram pseudoinverse, first variation,
-- literal atom authority, selected variation, exact cancellation and four
-- owner estimates belong to the same record.  The legacy correlated reducer
-- is obtained from this one object; no separately supplied family or scalar
-- residual equality can be substituted midway through the chain.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedVariationSignConventionExact as Sign
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact as Authority
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedOwnerBudgetSlackExact as Slack
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedSingletonClosureExact as Closure
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector

record LiteralSelectedPlaquetteWitness
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₂ where
  field
    Multiplier : Set
    pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier
    firstVariationCovector : KKT.StateVector

    residualAuthority : Authority.CorrelatedResidualAuthority
      pseudoData firstVariationCovector
      (Closure.literalRawExtractor bondField plaquette)

    FineVariation : Set
    variation : FineVariation

    GaugeAdmissible : FineVariation → Set
    ConstraintTangent : FineVariation → Set
    SupportedNearPlaquette : FineVariation → Set

    gaugeAdmissible : GaugeAdmissible variation
    constraintTangent : ConstraintTangent variation
    localSupport : SupportedNearPlaquette variation

    variationNormSq : FineVariation → ℚ
    selectorConstant : ℚ
    selectorConstantNonnegative : 0ℚ ≤ selectorConstant
    variationChargeBound :
      variationNormSq variation
      ≤ selectorConstant * Wilson.plaquetteCrossCharge bondField plaquette

    firstVariation : FineVariation → ℚ
    selectedEulerLagrangeStationary : firstVariation variation ≡ 0ℚ

    projectedVariationExact :
      firstVariation variation
      ≡ Partition.physicalPlaquetteWilsonLinearPart
          background bondField plaquette
        + Sign.canonicalProjectedSpillover
            (Authority.rawLocalization residualAuthority)
            (Authority.canonicalMultiplierGreenPairing
              pseudoData firstVariationCovector
              (Closure.literalRawExtractor bondField plaquette))

    exactCancellation :
      Ownership.ExactCorrelatedCancellation
        (Authority.canonicalCorrelatedResidualFamily residualAuthority)

    ownerBounds :
      Slack.CorrelatedOwnerBoundsWithSlack
        (Authority.canonicalCorrelatedResidualFamily residualAuthority)
        (Wilson.plaquetteCrossCharge bondField plaquette)
open LiteralSelectedPlaquetteWitness public

literalSelectedPlaquetteWitnessToCorrelatedExtractionData :
  ∀ {background bondField plaquette} →
  LiteralSelectedPlaquetteWitness background bondField plaquette →
  Closure.CorrelatedSingletonExtractionData
    background bondField plaquette
literalSelectedPlaquetteWitnessToCorrelatedExtractionData witness = record
  { Closure.CorrelatedSingletonExtractionData.Multiplier =
      Multiplier witness
  ; Closure.CorrelatedSingletonExtractionData.pseudoData =
      pseudoData witness
  ; Closure.CorrelatedSingletonExtractionData.firstVariationCovector =
      firstVariationCovector witness
  ; Closure.CorrelatedSingletonExtractionData.residualAuthority =
      residualAuthority witness
  ; Closure.CorrelatedSingletonExtractionData.FineVariation =
      FineVariation witness
  ; Closure.CorrelatedSingletonExtractionData.variation =
      variation witness
  ; Closure.CorrelatedSingletonExtractionData.GaugeAdmissible =
      GaugeAdmissible witness
  ; Closure.CorrelatedSingletonExtractionData.ConstraintTangent =
      ConstraintTangent witness
  ; Closure.CorrelatedSingletonExtractionData.SupportedNearPlaquette =
      SupportedNearPlaquette witness
  ; Closure.CorrelatedSingletonExtractionData.gaugeAdmissible =
      gaugeAdmissible witness
  ; Closure.CorrelatedSingletonExtractionData.constraintTangent =
      constraintTangent witness
  ; Closure.CorrelatedSingletonExtractionData.localSupport =
      localSupport witness
  ; Closure.CorrelatedSingletonExtractionData.variationNormSq =
      variationNormSq witness
  ; Closure.CorrelatedSingletonExtractionData.selectorConstant =
      selectorConstant witness
  ; Closure.CorrelatedSingletonExtractionData.selectorConstantNonnegative =
      selectorConstantNonnegative witness
  ; Closure.CorrelatedSingletonExtractionData.variationChargeBound =
      variationChargeBound witness
  ; Closure.CorrelatedSingletonExtractionData.firstVariation =
      firstVariation witness
  ; Closure.CorrelatedSingletonExtractionData.selectedEulerLagrangeStationary =
      selectedEulerLagrangeStationary witness
  ; Closure.CorrelatedSingletonExtractionData.projectedVariationExact =
      projectedVariationExact witness
  ; Closure.CorrelatedSingletonExtractionData.exactCancellation =
      exactCancellation witness
  ; Closure.CorrelatedSingletonExtractionData.ownerBudgets =
      Slack.slackCompletesLegacyOwnerBudget (ownerBounds witness) }

record LiteralSelectedPlaquetteFamily
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4) : Set₂ where
  field
    atPlaquette : ∀ plaquette →
      LiteralSelectedPlaquetteWitness background bondField plaquette
open LiteralSelectedPlaquetteFamily public

literalSelectedPlaquetteFamilyToSelector :
  ∀ {background bondField} →
  LiteralSelectedPlaquetteFamily background bondField →
  Closure.SelectedCorrelatedSingletonSelector background bondField
literalSelectedPlaquetteFamilyToSelector family = record
  { Closure.SelectedCorrelatedSingletonSelector.selectCorrelated =
      λ plaquette →
        literalSelectedPlaquetteWitnessToCorrelatedExtractionData
          (atPlaquette family plaquette) }

literalSelectedPlaquetteFamilyToPhysicalSelector :
  ∀ {background bondField} →
  LiteralSelectedPlaquetteFamily background bondField →
  Selector.SelectedBackgroundVariationSelector background bondField
literalSelectedPlaquetteFamilyToPhysicalSelector family =
  Closure.correlatedSelectorToPhysicalSelector
    (literalSelectedPlaquetteFamilyToSelector family)

literalSelectedPlaquetteVerticalAssemblyLevel : ProofLevel
literalSelectedPlaquetteVerticalAssemblyLevel = machineChecked

literalSelectedPlaquettePhysicalProducerLevel : ProofLevel
literalSelectedPlaquettePhysicalProducerLevel = conditional
