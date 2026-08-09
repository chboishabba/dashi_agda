module DASHI.Physics.YangMills.BalabanSelectedCorrelatedSingletonClosureExact where

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
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Assemble the Round-40 algebra into the existing physical selector reducer.
-- The projected variation has the exact public form
--
--   dS(Pw) = Singleton + RawLocalization - <lambda,Lw>.
--
-- The final two terms are identified with the signed, owner-aggregated
-- correlated residual.  Exact cancellation is removed first; the four
-- surviving owner estimates close 55/18874368.  The resulting witness reuses
-- the already physical pair/deep channel to obtain the correlated Wilson lower
-- bound.  No alternative sign or arbitrary 27+28 split enters this path.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonCorrelatedDeepPartitionExact as Split
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Radius
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedVariationSignConventionExact as Sign
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership

record CorrelatedSingletonExtractionData
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₁ where
  field
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
    rawLocalization multiplierDefectPairing : ℚ

    selectedEulerLagrangeStationary :
      firstVariation variation ≡ 0ℚ

    projectedVariationExact :
      firstVariation variation
      ≡ Partition.physicalPlaquetteWilsonLinearPart
          background bondField plaquette
        + Sign.canonicalProjectedSpillover
            rawLocalization multiplierDefectPairing

    correlatedFamily : Ownership.CorrelatedResidualFamily
    correlatedResidualExact :
      Ownership.correlatedResidualTotal correlatedFamily
      ≡ Sign.canonicalProjectedSpillover
          rawLocalization multiplierDefectPairing

    exactCancellation :
      Ownership.ExactCorrelatedCancellation correlatedFamily

    ownerBudgets :
      Ownership.CorrelatedOwnerBudgets correlatedFamily
        (Wilson.plaquetteCrossCharge bondField plaquette)

open CorrelatedSingletonExtractionData public

selectedSingletonResidualBudgetExact :
  ∀ {background bondField plaquette} →
  (dataSet : CorrelatedSingletonExtractionData
    background bondField plaquette) →
  Sign.canonicalProjectedSpillover
    (rawLocalization dataSet)
    (multiplierDefectPairing dataSet)
  ≤ Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge bondField plaquette
selectedSingletonResidualBudgetExact
    {bondField = bondField} {plaquette = plaquette} dataSet =
  subst
    (λ lower →
      lower
      ≤ Selector.remainingSingletonCoefficient
          * Wilson.plaquetteCrossCharge bondField plaquette)
    (correlatedResidualExact dataSet)
    (Ownership.correlatedResidualClosesSingletonBudget
      (exactCancellation dataSet)
      (ownerBudgets dataSet))

correlatedSingletonExtractionWitness :
  ∀ {background bondField plaquette} →
  CorrelatedSingletonExtractionData background bondField plaquette →
  Selector.SingletonExtractionWitness background bondField plaquette
correlatedSingletonExtractionWitness dataSet = record
  { Selector.SingletonExtractionWitness.FineVariation =
      FineVariation dataSet
  ; Selector.SingletonExtractionWitness.variation = variation dataSet
  ; Selector.SingletonExtractionWitness.GaugeAdmissible =
      GaugeAdmissible dataSet
  ; Selector.SingletonExtractionWitness.ConstraintTangent =
      ConstraintTangent dataSet
  ; Selector.SingletonExtractionWitness.SupportedNearPlaquette =
      SupportedNearPlaquette dataSet
  ; Selector.SingletonExtractionWitness.gaugeAdmissible =
      gaugeAdmissible dataSet
  ; Selector.SingletonExtractionWitness.constraintTangent =
      constraintTangent dataSet
  ; Selector.SingletonExtractionWitness.localSupport =
      localSupport dataSet
  ; Selector.SingletonExtractionWitness.variationNormSq =
      variationNormSq dataSet
  ; Selector.SingletonExtractionWitness.selectorConstant =
      selectorConstant dataSet
  ; Selector.SingletonExtractionWitness.selectorConstantNonnegative =
      selectorConstantNonnegative dataSet
  ; Selector.SingletonExtractionWitness.variationChargeBound =
      variationChargeBound dataSet
  ; Selector.SingletonExtractionWitness.firstVariation =
      firstVariation dataSet
  ; Selector.SingletonExtractionWitness.extractionSpillover =
      Sign.canonicalProjectedSpillover
        (rawLocalization dataSet)
        (multiplierDefectPairing dataSet)
  ; Selector.SingletonExtractionWitness.selectedEulerLagrangeStationary =
      selectedEulerLagrangeStationary dataSet
  ; Selector.SingletonExtractionWitness.extractsLiteralSingleton =
      projectedVariationExact dataSet
  ; Selector.SingletonExtractionWitness.spilloverUpper =
      selectedSingletonResidualBudgetExact dataSet }

selectedBackgroundSingletonLowerFromCorrelatedResidual :
  ∀ {background bondField plaquette} →
  (dataSet : CorrelatedSingletonExtractionData
    background bondField plaquette) →
  - (Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge bondField plaquette)
  ≤ Partition.physicalPlaquetteWilsonLinearPart
      background bondField plaquette
selectedBackgroundSingletonLowerFromCorrelatedResidual dataSet =
  Selector.selectedBackgroundSingletonCurvatureLower
    (correlatedSingletonExtractionWitness dataSet)

selectedBackgroundCorrelatedWilsonLower :
  ∀ {background bondField plaquette} →
  Radius.RelaxedInverseLinkRadius background →
  CorrelatedSingletonExtractionData background bondField plaquette →
  - (Wilson.rhoOverThirtySix
      * Wilson.plaquetteCrossCharge bondField plaquette)
  ≤ Split.physicalPlaquetteCorrelatedWilsonPart
      background bondField plaquette
selectedBackgroundCorrelatedWilsonLower radius dataSet =
  Selector.selectedBackgroundCorrelatedWilsonLower
    radius (correlatedSingletonExtractionWitness dataSet)

record SelectedCorrelatedSingletonSelector
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4) : Set₁ where
  field
    selectCorrelated : ∀ plaquette →
      CorrelatedSingletonExtractionData background bondField plaquette
open SelectedCorrelatedSingletonSelector public

correlatedSelectorToPhysicalSelector :
  ∀ {background bondField} →
  SelectedCorrelatedSingletonSelector background bondField →
  Selector.SelectedBackgroundVariationSelector background bondField
correlatedSelectorToPhysicalSelector selected = record
  { Selector.SelectedBackgroundVariationSelector.select = λ plaquette →
      correlatedSingletonExtractionWitness
        (selectCorrelated selected plaquette) }

selectedSingletonResidualBudgetLevel : ProofLevel
selectedSingletonResidualBudgetLevel = machineChecked

selectedCorrelatedWilsonLowerLevel : ProofLevel
selectedCorrelatedWilsonLowerLevel = machineChecked

selectedPhysicalCorrelatedSingletonDataProducerLevel : ProofLevel
selectedPhysicalCorrelatedSingletonDataProducerLevel = conditional
