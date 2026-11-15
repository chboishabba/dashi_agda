module DASHI.Governance.SituatedCortisolAggregateNonIdentificationExact where

-- Aggregate-to-individual identifiability cut, DASHI-original mathematics.
-- Existing biological owners:
--   DASHI.Biology.EmbodiedOptionConeInteroceptionExact
--   DASHI.Biology.AllostaticBodyStateExact
--   DASHI.Biology.StressPhysiologyCascadeExact
--   DASHI.Biology.MultiscaleAllostaticBodyHyperformalismExact
-- Crenshaw supplies intersectional conceptual motivation, not this theorem.
-- Cortisol is a biomarker, not a complete stress/trauma state, and a
-- synthetic Nat response is NOT a measured hormone concentration.
open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Embodied
import DASHI.Biology.StressPhysiologyCascadeExact as Cascade
import DASHI.Biology.AllostaticBodyStateExact as Allostasis
import DASHI.Biology.MultiscaleAllostaticBodyHyperformalismExact as Multiscale

data Person : Set where
  participantA participantB : Person

data HypotheticalWorld : Set where
  distributionAB distributionBA : HypotheticalWorld

-- Same aggregate exposure and same TOTAL synthetic cortisol count.
-- Swapping person-specific synthetic responses changes neither aggregate.
aggregateEnvironmentalExposure : HypotheticalWorld → Nat
aggregateEnvironmentalExposure _ = 8

responseA : HypotheticalWorld → Nat
responseA distributionAB = 1
responseA distributionBA = 3

responseB : HypotheticalWorld → Nat
responseB distributionAB = 3
responseB distributionBA = 1

groupTotalResponse : HypotheticalWorld → Nat
groupTotalResponse w = responseA w + responseB w

sameAggregateEnvironmentalExposure :
  aggregateEnvironmentalExposure distributionAB
  ≡ aggregateEnvironmentalExposure distributionBA
sameAggregateEnvironmentalExposure = refl

sameAggregateResponseTotal :
  groupTotalResponse distributionAB ≡
  groupTotalResponse distributionBA
sameAggregateResponseTotal = refl

coarseEnvironmentAndAggregateTotal :
  HypotheticalWorld → Nat × Nat
coarseEnvironmentAndAggregateTotal w =
  aggregateEnvironmentalExposure w , groupTotalResponse w

individualResponse : Person → HypotheticalWorld → Nat
individualResponse participantA = responseA
individualResponse participantB = responseB

sameAggregateDifferentIndividualCortisol :
  NF.NonFactorabilityWitness
    coarseEnvironmentAndAggregateTotal
    (individualResponse participantA)
sameAggregateDifferentIndividualCortisol =
  NF.nonFactorabilityWitness distributionAB distributionBA refl (λ ())

aggregateEnvironmentalExposureCannotDeterminePerson :
  NF.FactorsThrough
    coarseEnvironmentAndAggregateTotal
    (individualResponse participantA) → ⊥
aggregateEnvironmentalExposureCannotDeterminePerson =
  NF.witnessRulesOutEveryFlatFactorisation
    sameAggregateDifferentIndividualCortisol

anyAggregateRechartStillLosesPersonalResponse :
  ∀ {R : Set}
    (rechart : Nat × Nat → R) →
  NF.FactorsThrough
    (λ w → rechart (coarseEnvironmentAndAggregateTotal w))
    (individualResponse participantA) → ⊥
anyAggregateRechartStillLosesPersonalResponse rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart sameAggregateDifferentIndividualCortisol

-- Constructive repair: retaining an individual-specific response coordinate
-- recovers it exactly. This is a mathematical observation-adequacy proof,
-- not a claim that the coordinate has been obtained for any real person.
individualAugmentedObservation : HypotheticalWorld → Nat × Nat
individualAugmentedObservation w =
  aggregateEnvironmentalExposure w , individualResponse participantA w

individualResponseFactorsThroughAugmentedObserver :
  NF.FactorsThrough individualAugmentedObservation
    (individualResponse participantA)
individualResponseFactorsThroughAugmentedObserver =
  NF.factorsThrough proj₂ (λ w → refl)

-- Bridge to existing cortisol component and HPA timescale owner, without
-- identifying an ordinal body activation with an assay concentration.
existingCortisolProjection :
  Embodied.BodyState → Embodied.Activation
existingCortisolProjection = Embodied.cortisol

existingSlowerHPAClass :
  Cascade.mediatorTimescale Cascade.cortisol
  ≡ Cascade.slowerEndocrineRoute
existingSlowerHPAClass = refl

existingCortisolDoesNotDetermineWholeBody :
  Embodied.regulatedBody ≡ Embodied.mobilisedBody → ⊥
existingCortisolDoesNotDetermineWholeBody =
  Embodied.cortisolDoesNotDetermineBodyState

existingCoreDoesNotDetermineAllostaticImmune :
  NF.FactorsThrough
    Allostasis.coreProjection Allostasis.immuneProjection → ⊥
existingCoreDoesNotDetermineAllostaticImmune =
  Allostasis.coreBodyDoesNotDetermineFullAllostaticState

existingHpaDoesNotRecoverFullSupervoxel :
  Multiscale.regulatedStack ≡ Multiscale.acuteMobilisedStack → ⊥
existingHpaDoesNotRecoverFullSupervoxel =
  Multiscale.hpaCoordinateDoesNotRecoverWholeBody
