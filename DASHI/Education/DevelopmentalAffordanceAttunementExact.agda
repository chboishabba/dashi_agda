module DASHI.Education.DevelopmentalAffordanceAttunementExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.EcologyOfDataHyperfabricBridge as Ecology
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Education.EarlyLearningComparativeArchitectureExact as Comparative
import DASHI.Education.RoseContextLearningSourceBoundary as Rose
import DASHI.Reasoning.DevelopmentalAttunementPNFBridge as Attunement
import DASHI.Reasoning.RelationalFormalismSourceAtlas as RelationalSources

------------------------------------------------------------------------
-- DEVELOPMENTAL AFFORDANCE / ATTUNEMENT HYPERFABRIC
--
-- "Smell the roses" is interpreted as a carrier correction, not an enrichment
-- slogan.  Sensory/context exposure is one typed coordinate.  What matters is
-- whether available affordances fit the child, developmental phase, temporal
-- organisation and relational loop.  More exposure, more attention, more
-- structure or more autonomy are therefore not promoted to monotone goods.
------------------------------------------------------------------------

data DevelopmentalPhase : Set where
  earlyExploration emergingSymbolic consolidatedPractice : DevelopmentalPhase

data AffordanceKind : Set where
  relationalAffordance sensoryAffordance olfactoryAffordance : AffordanceKind
  spatialAffordance motorAffordance socialAffordance : AffordanceKind
  languageAffordance restRecoveryAffordance : AffordanceKind

data AffordanceFit : Set where
  mismatchedAffordanceFit attunedAffordanceFit : AffordanceFit

data TemporalOrganisation : Set where
  fragmentedTiming contingentPredictableTiming : TemporalOrganisation

data ChildPreferenceVisibility : Set where
  preferenceOccluded preferenceContestableVisible : ChildPreferenceVisibility

record DevelopmentalAffordanceCell : Set where
  constructor developmentalAffordanceCell
  field
    phase : DevelopmentalPhase
    availableAffordances : List AffordanceKind
    fit : AffordanceFit
    timing : TemporalOrganisation
    childPreference : ChildPreferenceVisibility
    relationalReviewPresent : Bool
    overloadRegulationPresent : Bool
    localLifeworldRetained : Bool
    commonEntitlementRetained : Bool
    cellLabel : String

open DevelopmentalAffordanceCell public

canonicalAffordanceInventory : List AffordanceKind
canonicalAffordanceInventory =
  relationalAffordance
  ∷ sensoryAffordance
  ∷ olfactoryAffordance
  ∷ spatialAffordance
  ∷ motorAffordance
  ∷ socialAffordance
  ∷ languageAffordance
  ∷ restRecoveryAffordance
  ∷ []

mismatchedAffordanceCell : DevelopmentalAffordanceCell
mismatchedAffordanceCell =
  developmentalAffordanceCell
    earlyExploration canonicalAffordanceInventory mismatchedAffordanceFit
    fragmentedTiming preferenceOccluded
    false false true true
    "same nominal affordance inventory, but fragmented timing, occluded child preference and no relational review"

attunedAffordanceCell : DevelopmentalAffordanceCell
attunedAffordanceCell =
  developmentalAffordanceCell
    earlyExploration canonicalAffordanceInventory attunedAffordanceFit
    contingentPredictableTiming preferenceContestableVisible
    true true true true
    "same nominal affordance inventory, with contingent timing, visible child preference, overload regulation and relational review"

------------------------------------------------------------------------
-- Equal resource/affordance inventory cannot determine developmental fit.
-- This is the ecological analogue of the existing family-choice and delivery-
-- site non-factorability theorems.
------------------------------------------------------------------------

data SameAffordanceInventoryLabel : Set where
  sameAffordanceInventory : SameAffordanceInventoryLabel

affordanceInventoryProjection : DevelopmentalAffordanceCell → SameAffordanceInventoryLabel
affordanceInventoryProjection cell = sameAffordanceInventory

situatedAffordanceFitWitness : DevelopmentalAffordanceCell → Bool
situatedAffordanceFitWitness mismatchedAffordanceCell = false
situatedAffordanceFitWitness attunedAffordanceCell = true
situatedAffordanceFitWitness cell = false

sameInventoryDifferentFit :
  situatedAffordanceFitWitness mismatchedAffordanceCell ≡
  situatedAffordanceFitWitness attunedAffordanceCell → ⊥
sameInventoryDifferentFit ()

affordanceInventoryNonFactorability :
  Intersection.NonFactorabilityWitness
    affordanceInventoryProjection situatedAffordanceFitWitness
affordanceInventoryNonFactorability =
  Intersection.nonFactorabilityWitness
    mismatchedAffordanceCell attunedAffordanceCell refl sameInventoryDifferentFit

affordanceInventoryCannotDetermineDevelopmentalFit :
  Intersection.FactorsThrough
    affordanceInventoryProjection situatedAffordanceFitWitness → ⊥
affordanceInventoryCannotDetermineDevelopmentalFit =
  Intersection.witnessRulesOutEveryFlatFactorisation
    affordanceInventoryNonFactorability

------------------------------------------------------------------------
-- Existing developmental-attunement result upgraded to a generic
-- non-factorability statement: the same amount of attended interaction does
-- not determine sequence-dependent burden when temporal ordering differs.
------------------------------------------------------------------------

attentionQuantityProjection : List Attunement.ResponseSignal → Nat
attentionQuantityProjection = Attunement.attentionMass

sequenceBurden : List Attunement.ResponseSignal → Nat
sequenceBurden = Attunement.traceTotalBurden

sameAttentionQuantity :
  attentionQuantityProjection Attunement.stableTrace ≡
  attentionQuantityProjection Attunement.fragmentedTrace
sameAttentionQuantity = refl

sameAttentionDifferentBurden :
  sequenceBurden Attunement.stableTrace ≡
  sequenceBurden Attunement.fragmentedTrace → ⊥
sameAttentionDifferentBurden ()

attentionQuantityNonFactorability :
  Intersection.NonFactorabilityWitness attentionQuantityProjection sequenceBurden
attentionQuantityNonFactorability =
  Intersection.nonFactorabilityWitness
    Attunement.stableTrace Attunement.fragmentedTrace
    sameAttentionQuantity sameAttentionDifferentBurden

attentionQuantityCannotDetermineAttunementBurden :
  Intersection.FactorsThrough attentionQuantityProjection sequenceBurden → ⊥
attentionQuantityCannotDetermineAttunementBurden =
  Intersection.witnessRulesOutEveryFlatFactorisation
    attentionQuantityNonFactorability

------------------------------------------------------------------------
-- Existing ecological and rose sources are reused exactly.  The Finn/Brown
-- ecology keeps person, place, affordance, activity, value-flow and time as
-- co-constituted surfaces.  The rose source licenses olfactory exposure as a
-- context coordinate while explicitly denying universal-benefit promotion.
------------------------------------------------------------------------

canonicalEcology = Ecology.canonicalEcologyOfDataHyperfabricBridge
canonicalRoseBoundary = Rose.canonicalRoseContextEvidenceBoundary
canonicalRelationalSourceAtlas = RelationalSources.canonicalRelationalSourceAtlas

roseExposureStillDoesNotProveUniversalLearningBenefit :
  Rose.exposureAloneProvesUniversalLearningBenefit
    Rose.canonicalRoseContextEvidenceBoundary ≡ false
roseExposureStillDoesNotProveUniversalLearningBenefit =
  Rose.exposureAloneProvesUniversalLearningBenefitIsFalse
    Rose.canonicalRoseContextEvidenceBoundary

------------------------------------------------------------------------
-- No monotone-scalar promotion.  These empty permissions deliberately block
-- the tempting replacement of delivery-site ideology with a new scalar such
-- as "more stimulation", "more autonomy" or "more structure".
------------------------------------------------------------------------

data MoreAffordancesAlwaysBetterPermission : Set where
data MoreSensoryExposureAlwaysBetterPermission : Set where
data MoreAutonomyAlwaysBetterPermission : Set where
data MoreStructureAlwaysBetterPermission : Set where
data ProfessionalPresenceAlwaysAttunedPermission : Set where

moreAffordancesCannotAutoPromoteToBetter : MoreAffordancesAlwaysBetterPermission → ⊥
moreAffordancesCannotAutoPromoteToBetter ()

moreSensoryExposureCannotAutoPromoteToBetter : MoreSensoryExposureAlwaysBetterPermission → ⊥
moreSensoryExposureCannotAutoPromoteToBetter ()

moreAutonomyCannotAutoPromoteToBetter : MoreAutonomyAlwaysBetterPermission → ⊥
moreAutonomyCannotAutoPromoteToBetter ()

moreStructureCannotAutoPromoteToBetter : MoreStructureAlwaysBetterPermission → ⊥
moreStructureCannotAutoPromoteToBetter ()

professionalPresenceCannotAutoPromoteToAttunement :
  ProfessionalPresenceAlwaysAttunedPermission → ⊥
professionalPresenceCannotAutoPromoteToAttunement ()

------------------------------------------------------------------------
-- Comparative architecture remains upstream but is no longer the last word:
-- quality/structure/autonomy/context must themselves be unpacked into the
-- person-place-affordance-timing relation when developmental fit is consumed.
------------------------------------------------------------------------

professionalFloorStillCannotDetermineOutcome =
  Comparative.professionalFloorCannotDetermineOutcome

homeDeliveryStillCannotDetermineAcademicOutcome =
  Comparative.homeDeliveryCannotDetermineAcademicOutcome

developmentalAffordanceReading : String
developmentalAffordanceReading =
  "Developmental opportunity does not factor through delivery site, professional presence, resource count, attention quantity, sensory exposure, autonomy or structure alone. Person and place co-constitute a field of affordances whose developmental fit depends on phase, temporal contingency, child preference, overload regulation, local lifeworld and relational review. Preserve entitlements, but evaluate the topology and timing of what the child can actually do, perceive, contest and integrate."
