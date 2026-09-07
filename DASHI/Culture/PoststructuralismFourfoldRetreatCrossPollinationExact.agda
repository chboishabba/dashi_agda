module DASHI.Culture.PoststructuralismFourfoldRetreatCrossPollinationExact where

------------------------------------------------------------------------
-- POSTSTRUCTURALISM x FOURFOLD-RETREAT CROSS-POLLINATION
--
-- Source-attribution policy is explicit:
--
--   Foster/Rockhill source proposition
--   != DASHI bounded interpretation
--   != DASHI formal construction
--   != empirical claim about a thinker/tradition.
--
-- In particular, the finite countermodels below are repository constructions.
-- They are not historical claims about Foucault, Derrida, poststructuralism or
-- postmodernism as a whole.
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

-- These profiles are finite DASHI witnesses only.  They have no external
-- thinker/tradition attribution.
constructedMixedProfile : RetreatProfile
constructedMixedProfile = retreat-profile true true false false

constructedFourAxisHighProfile : RetreatProfile
constructedFourAxisHighProfile = retreat-profile true true true true

materialismCoordinateSeparatesConstructedProfiles :
  constructedMixedProfile ≡ constructedFourAxisHighProfile → ⊥
materialismCoordinateSeparatesConstructedProfiles same =
  falseIsNotTrue
    (cong materialismScienceAxis same)
  where
    falseIsNotTrue : false ≡ true → ⊥
    falseIsNotTrue ()

------------------------------------------------------------------------
-- 2. Same broad school label cannot recover the full retreat profile.
--
-- `SituatedReading` is a toy carrier witnessing non-factorability.  Its two
-- constructors are not asserted to be actual historical schools or authors.
------------------------------------------------------------------------

data SituatedReading : Set where
  constructedDiscourseMaterialistReading : SituatedReading
  constructedDiscourseIdealistReading : SituatedReading


data BroadSchoolLabel : Set where poststructuralistLabel : BroadSchoolLabel

schoolLabel : SituatedReading → BroadSchoolLabel
schoolLabel _ = poststructuralistLabel

retreatProfile : SituatedReading → RetreatProfile
retreatProfile constructedDiscourseMaterialistReading = constructedMixedProfile
retreatProfile constructedDiscourseIdealistReading = constructedFourAxisHighProfile

sameLabelDifferentProfile :
  retreatProfile constructedDiscourseMaterialistReading ≡
  retreatProfile constructedDiscourseIdealistReading → ⊥
sameLabelDifferentProfile = materialismCoordinateSeparatesConstructedProfiles

poststructuralistLabelNonFactorability :
  INF.NonFactorabilityWitness schoolLabel retreatProfile
poststructuralistLabelNonFactorability =
  INF.nonFactorabilityWitness
    constructedDiscourseMaterialistReading
    constructedDiscourseIdealistReading
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
-- The implication A+B -> C is NOT attributed to Foster/Rockhill as a theorem;
-- its rejection here is a DASHI no-promotion boundary.
------------------------------------------------------------------------

data TheoreticalMove : Set where
  critiquesFoundationalReason : TheoreticalMove
  discourseConstitutive : TheoreticalMove
  abandonsMaterialismAndRationalExplanation : TheoreticalMove


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
  materialOneWayDetermination : CausalArchitecture
  discursiveOneWayDetermination : CausalArchitecture
  reciprocalMaterialDiscursiveConstitution : CausalArchitecture


reciprocalNotDiscursiveOneWay :
  reciprocalMaterialDiscursiveConstitution ≡ discursiveOneWayDetermination → ⊥
reciprocalNotDiscursiveOneWay ()

------------------------------------------------------------------------
-- 5. Political-strategy residual: the stronger criticism can remain open.
------------------------------------------------------------------------

data StrategicCoordinate : Set where
  productionRelation : StrategicCoordinate
  classStructure : StrategicCoordinate
  capitalAccumulation : StrategicCoordinate
  statePower : StrategicCoordinate
  imperialSystem : StrategicCoordinate
  collectiveAgent : StrategicCoordinate
  transformationTarget : StrategicCoordinate


data StrategicAdequacy : Set where
  strategicallySpecified : StrategicAdequacy
  strategicallyOpen : StrategicAdequacy


record StrategicResidual : Set where
  constructor strategic-residual
  field
    coordinate : StrategicCoordinate
    adequacy : StrategicAdequacy

------------------------------------------------------------------------
-- 6. Attribution-aware source consumption.
--
-- Every imported external proposition remains attached to the exact speaker
-- receipt that owns it.  The repository may then build bounded interpretations
-- or formal countermodels, but those later layers do not flow backward into
-- source authorship.
------------------------------------------------------------------------

data CrossPollinationClaimLayer : Set where
  externalSourceProposition : CrossPollinationClaimLayer
  dashIBoundedInterpretation : CrossPollinationClaimLayer
  dashIFormalCountermodel : CrossPollinationClaimLayer
  empiricalNamedThinkerClaim : CrossPollinationClaimLayer


record SourceUseReceipt : Set where
  constructor source-use-receipt
  field
    sourceReceipt : Source.SourceReceipt
    sourceLayer : CrossPollinationClaimLayer
    downstreamLayer : CrossPollinationClaimLayer
    preservesSpeakerOwnership : Bool
    preservesExactSourceLocation : Bool
    createsEmpiricalAuthority : Bool
    attributesDASHIConstructionToSource : Bool
    independentPromotionReceiptRequired : Bool

fourfoldSummarySourceUse : SourceUseReceipt
fourfoldSummarySourceUse =
  source-use-receipt
    Source.fourfoldRetreatReceipt
    externalSourceProposition
    dashIBoundedInterpretation
    true true false false true

nonMechanicalQualificationSourceUse : SourceUseReceipt
nonMechanicalQualificationSourceUse =
  source-use-receipt
    Source.nonMechanicalFieldReceipt
    externalSourceProposition
    dashIBoundedInterpretation
    true true false false true

fosterDiscursiveTurnSourceUse : SourceUseReceipt
fosterDiscursiveTurnSourceUse =
  source-use-receipt
    Source.fosterDiscursiveTurnAssociationReceipt
    externalSourceProposition
    dashIBoundedInterpretation
    true true false false true

rockhillMaterialWithdrawalSourceUse : SourceUseReceipt
rockhillMaterialWithdrawalSourceUse =
  source-use-receipt
    Source.rockhillMaterialRealityWithdrawalReceipt
    externalSourceProposition
    dashIBoundedInterpretation
    true true false false true

------------------------------------------------------------------------
-- 7. Direct x-pollination with merged provenance/critical-theory boundaries.
------------------------------------------------------------------------

record FourfoldRetreatCrossPollinationWeld : Set where
  constructor fourfold-retreat-cross-pollination-weld
  field
    sourceBoundary : Source.FourfoldRetreatSourceBoundary
    philosophyBoundary : Philosophy.PhilosophyClaimProvenanceHistoryBoundary
    criticalTheoryBoundary : Critical.HistoricalTotalityCriticalTheoryBoundary
    exactSpeakerReceiptsPreserved : Bool
    sourceLocationReceiptsPreserved : Bool
    accessCarrierNotPromotedToAuthorship : Bool
    schoolLabelDoesNotDetermineProfile : Bool
    critiqueOfReasonDoesNotEqualIrrationalism : Bool
    discourseConstitutiveDoesNotEqualImmaterialism : Bool
    socialConstructionDoesNotEqualCausalInertness : Bool
    oneRetreatAxisDoesNotDetermineOtherAxes : Bool
    fourAxisProfileDoesNotFollowFromTraditionName : Bool
    strategicAdequacyRequiresIndependentReceipts : Bool
    sourceArgumentRemainsSourceBound : Bool
    finiteCountermodelOwnedByDASHI : Bool
    namedThinkerClassificationStillRequiresEvidence : Bool

canonicalFourfoldRetreatCrossPollinationWeld :
  FourfoldRetreatCrossPollinationWeld
canonicalFourfoldRetreatCrossPollinationWeld =
  fourfold-retreat-cross-pollination-weld
    Source.canonicalFourfoldRetreatSourceBoundary
    Philosophy.canonicalPhilosophyClaimProvenanceHistoryBoundary
    Critical.canonicalHistoricalTotalityCriticalTheoryBoundary
    true true true true true true true true true true true true true

------------------------------------------------------------------------
-- 8. Explicit no-promotion gates.
------------------------------------------------------------------------

data CritiqueOfReasonMeansIrrationalism : Set where
data DiscourseConstitutiveMeansImmaterialism : Set where
data SocialConstructionMeansCausalInertness : Set where
data OneRetreatAxisDeterminesAllFour : Set where
data PoststructuralistMeansFourfoldRetreat : Set where
data FourfoldRetreatCritiqueProvesHistoricalCausation : Set where
data AccessLocationCreatesSourceAuthorship : Set where
data DASHICountermodelBecomesSourceAuthorsTheorem : Set where
data SourceCriticismClassifiesNamedThinkerWithoutReceipt : Set where

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

accessLocationDoesNotCreateSourceAuthorship :
  AccessLocationCreatesSourceAuthorship → ⊥
accessLocationDoesNotCreateSourceAuthorship ()

dashICountermodelDoesNotBecomeSourceAuthorsTheorem :
  DASHICountermodelBecomesSourceAuthorsTheorem → ⊥
dashICountermodelDoesNotBecomeSourceAuthorsTheorem ()

sourceCriticismDoesNotClassifyNamedThinkerWithoutReceipt :
  SourceCriticismClassifiesNamedThinkerWithoutReceipt → ⊥
sourceCriticismDoesNotClassifyNamedThinkerWithoutReceipt ()
