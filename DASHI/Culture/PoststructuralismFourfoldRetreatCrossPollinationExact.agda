module DASHI.Culture.PoststructuralismFourfoldRetreatCrossPollinationExact where

------------------------------------------------------------------------
-- POSTSTRUCTURALISM x FOURFOLD-RETREAT CROSS-POLLINATION
--
-- Reuses merged repository machinery rather than turning a school label into
-- a one-bit verdict.  The application claim is deliberately weaker:
--
--   critique of universal/foundational reason
-- + discourse treated as constitutive
-- does NOT by itself entail
--   abandonment of materialism and rational explanation.
--
-- Likewise, a tradition label does not determine a four-coordinate retreat
-- profile.  These are DASHI formal boundaries, not historical propositions
-- attributed to Foster, Rockhill, Foucault, Derrida, or any other thinker.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.PhilosophyClaimProvenanceHistoryBidiExact as Philosophy
import DASHI.Culture.HistoricalTotalityCriticalTheoryCrossPollinationExact as Critical
import DASHI.Culture.RockhillFosterFourfoldRetreatSourceBoundaryExact as Source

------------------------------------------------------------------------
-- 1. Four independent coordinates, not one school-level Boolean.
------------------------------------------------------------------------

record RetreatProfile : Set where
  constructor retreat-profile
  field
    classAxis : Bool
    imperialismAxis : Bool
    materialismScienceAxis : Bool
    reasonAxis : Bool

open RetreatProfile public

mixedPoststructuralProfile : RetreatProfile
mixedPoststructuralProfile = retreat-profile true true false false

fourAxisHighProfile : RetreatProfile
fourAxisHighProfile = retreat-profile true true true true

materialismCoordinateSeparatesProfiles :
  mixedPoststructuralProfile ≡ fourAxisHighProfile → ⊥
materialismCoordinateSeparatesProfiles same =
  falseIsNotTrue
    (cong materialismScienceAxis same)
  where
    falseIsNotTrue : false ≡ true → ⊥
    falseIsNotTrue ()

------------------------------------------------------------------------
-- 2. Same broad school label cannot recover the full retreat profile.
------------------------------------------------------------------------

data SituatedReading : Set where
  discourseMaterialistReading
  discourseIdealistReading
  : SituatedReading

data BroadSchoolLabel : Set where poststructuralistLabel : BroadSchoolLabel

schoolLabel : SituatedReading → BroadSchoolLabel
schoolLabel _ = poststructuralistLabel

retreatProfile : SituatedReading → RetreatProfile
retreatProfile discourseMaterialistReading = mixedPoststructuralProfile
retreatProfile discourseIdealistReading = fourAxisHighProfile

sameLabelDifferentProfile :
  retreatProfile discourseMaterialistReading ≡
  retreatProfile discourseIdealistReading → ⊥
sameLabelDifferentProfile = materialismCoordinateSeparatesProfiles

poststructuralistLabelNonFactorability :
  INF.NonFactorabilityWitness schoolLabel retreatProfile
poststructuralistLabelNonFactorability =
  INF.nonFactorabilityWitness
    discourseMaterialistReading
    discourseIdealistReading
    refl
    sameLabelDifferentProfile

poststructuralistLabelCannotDetermineRetreatProfile :
  INF.FactorsThrough schoolLabel retreatProfile → ⊥
poststructuralistLabelCannotDetermineRetreatProfile =
  INF.witnessRulesOutEveryFlatFactorisation
    poststructuralistLabelNonFactorability

------------------------------------------------------------------------
-- 3. Separate propositions A, B, C.
--
-- A: critiques foundational/universal reason.
-- B: treats discourse/knowledge categories as constitutive rather than merely
--    reflective.
-- C: abandons materialism and rational explanation.
--
-- Repository policy: A+B never auto-promotes to C.
------------------------------------------------------------------------

data TheoreticalMove : Set where
  critiquesFoundationalReason
  discourseConstitutive
  abandonsMaterialismAndRationalExplanation
  : TheoreticalMove

record ABReceipt : Set where
  constructor ab-receipt
  field
    reasonCritiquePresent : Bool
    discourseConstitutivePresent : Bool

canonicalABReceipt : ABReceipt
canonicalABReceipt = ab-receipt true true

data ABPromotesC : Set where

abDoesNotAutoPromoteToC : ABPromotesC → ⊥
abDoesNotAutoPromoteToC ()

------------------------------------------------------------------------
-- 4. Material/discursive reciprocity is a distinct model, not a retreat proof.
------------------------------------------------------------------------

data CausalArchitecture : Set where
  materialOneWayDetermination
  discursiveOneWayDetermination
  reciprocalMaterialDiscursiveConstitution
  : CausalArchitecture

reciprocalNotDiscursiveOneWay :
  reciprocalMaterialDiscursiveConstitution ≡ discursiveOneWayDetermination → ⊥
reciprocalNotDiscursiveOneWay ()

------------------------------------------------------------------------
-- 5. Political-strategy residual: the stronger criticism can remain open.
--
-- The meaningful question is not whether discourse exists, but whether the
-- framework supplies adequate causal and strategic carriers for production,
-- class, accumulation, states, imperial systems, collective agents and
-- transformation targets.
------------------------------------------------------------------------

data StrategicCoordinate : Set where
  productionRelation
  classStructure
  capitalAccumulation
  statePower
  imperialSystem
  collectiveAgent
  transformationTarget
  : StrategicCoordinate

data StrategicAdequacy : Set where
  strategicallySpecified
  strategicallyOpen
  : StrategicAdequacy

record StrategicResidual : Set where
  constructor strategic-residual
  field
    coordinate : StrategicCoordinate
    adequacy : StrategicAdequacy

------------------------------------------------------------------------
-- 6. Direct x-pollination with merged provenance/critical-theory boundaries.
------------------------------------------------------------------------

record FourfoldRetreatCrossPollinationWeld : Set where
  constructor fourfold-retreat-cross-pollination-weld
  field
    sourceBoundary : Source.FourfoldRetreatSourceBoundary
    philosophyBoundary : Philosophy.PhilosophyClaimProvenanceHistoryBoundary
    criticalTheoryBoundary : Critical.HistoricalTotalityCriticalTheoryBoundary
    schoolLabelDoesNotDetermineProfile : Bool
    critiqueOfReasonDoesNotEqualIrrationalism : Bool
    discourseConstitutiveDoesNotEqualImmaterialism : Bool
    socialConstructionDoesNotEqualCausalInertness : Bool
    oneRetreatAxisDoesNotDetermineOtherAxes : Bool
    fourAxisProfileDoesNotFollowFromTraditionName : Bool
    strategicAdequacyRequiresIndependentReceipts : Bool
    sourceArgumentRemainsSourceBound : Bool

canonicalFourfoldRetreatCrossPollinationWeld :
  FourfoldRetreatCrossPollinationWeld
canonicalFourfoldRetreatCrossPollinationWeld =
  fourfold-retreat-cross-pollination-weld
    Source.canonicalFourfoldRetreatSourceBoundary
    Philosophy.canonicalPhilosophyClaimProvenanceHistoryBoundary
    Critical.canonicalHistoricalTotalityCriticalTheoryBoundary
    true true true true true true true true

------------------------------------------------------------------------
-- 7. Explicit no-promotion gates.
------------------------------------------------------------------------

data CritiqueOfReasonMeansIrrationalism : Set where
data DiscourseConstitutiveMeansImmaterialism : Set where
data SocialConstructionMeansCausalInertness : Set where
data OneRetreatAxisDeterminesAllFour : Set where
data PoststructuralistMeansFourfoldRetreat : Set where
data FourfoldRetreatCritiqueProvesHistoricalCausation : Set where

critiqueOfReasonDoesNotMeanIrrationalism :
  CritiqueOfReasonMeansIrrationalism → ⊥
critiqueOfReasonDoesNotMeanIrrationalism ()

discourseConstitutiveDoesNotMeanImmaterialism :
  DiscourseConstitutiveMeansImmaterialism → ⊥
discourseConstitutiveDoesNotMeanImmaterialism ()

socialConstructionDoesNotMeanCausalInertness :
  SocialConstructionMeansCausalInertness → ⊥
socialConstructionDoesNotMeanCausalInertness ()

oneRetreatAxisDoesNotDetermineAllFour :
  OneRetreatAxisDeterminesAllFour → ⊥
oneRetreatAxisDoesNotDetermineAllFour ()

poststructuralistDoesNotMeanFourfoldRetreat :
  PoststructuralistMeansFourfoldRetreat → ⊥
poststructuralistDoesNotMeanFourfoldRetreat ()

fourfoldRetreatCritiqueDoesNotProveHistoricalCausation :
  FourfoldRetreatCritiqueProvesHistoricalCausation → ⊥
fourfoldRetreatCritiqueDoesNotProveHistoricalCausation ()
