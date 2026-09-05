module DASHI.Culture.MissingDeceasedExternalisationBoundarySelectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ExternalisationBoundaryEnrichmentBidiExact as W
import DASHI.Core.ReferencePopulationRosterEnrichmentExact as R
import DASHI.Culture.MissingDeceasedTechnicalExternalisationExact as X
import DASHI.Culture.AmyEskridgeKnowledgeBoundaryTransitionExact as AmyB
import DASHI.Culture.RezaPatentBoundaryTransitionExact as RezaB

------------------------------------------------------------------------
-- CURRENT PERSON-LEVEL WITNESSES
------------------------------------------------------------------------

loureiroViriatoDeepWitness : W.DeepFeatureWitness
loureiroViriatoDeepWitness = W.deep-feature-witness
  X.loureiroViriatoExternalisation
  X.loureiroViriatoDeepExternalisation
  "Viriato publicly exposes model, numerical method/architecture and validation/benchmark structure. This is E-depth, not B-boundary transfer."

------------------------------------------------------------------------
-- PRE-REGISTERED MATCHED CONTROL DESIGNS
------------------------------------------------------------------------

deepExternalisationControlDesign : R.MatchedReferenceDesign
deepExternalisationControlDesign = R.matched-reference-design
  "declared technical roster members scored for model+method+validation externalisation"
  "matched technical peers from the same institutional/domain/seniority strata who are not roster members"
  ( "institution"
  ∷ "technical domain"
  ∷ "career seniority"
  ∷ "publication opportunity"
  ∷ "public-facing role opportunity"
  ∷ "programme sensitivity"
  ∷ "time/geography"
  ∷ [] )
  true refl
  "score the fixed externalisation stages for roster and controls before comparing outcomes"
  "do not exclude controls because they externalise as deeply as roster members"

restrictedBoundaryControlDesign : R.MatchedReferenceDesign
restrictedBoundaryControlDesign = R.matched-reference-design
  "declared technical roster members with a closed same-object private-to-public transfer, stratified by boundary kind"
  "matched peers with comparable boundary mechanism, access, release opportunity, institution, programme sensitivity and time window"
  ( "boundary kind"
  ∷ "institution"
  ∷ "technical domain"
  ∷ "role/access level"
  ∷ "programme sensitivity"
  ∷ "public-release opportunity"
  ∷ "time/geography"
  ∷ [] )
  true refl
  "count completed B only after prior private/restricted state, public release, same-object provenance and boundary kind are all present"
  "do not pool ordinary patent confidentiality with contractual proprietary, controlled-government, export-controlled, classified/declassification or discretionary-disclosure transitions"

------------------------------------------------------------------------
-- BIDI FRONTIER
------------------------------------------------------------------------

deepExternalisationNeedsMatchedControls : W.ExternalisationSelectionFrontier
deepExternalisationNeedsMatchedControls = W.externalisation-selection-frontier
  W.deepTechnicalExternalisation
  W.missingMatchedControlPopulation
  "complete pre-registered peers and score problem/model/method/implementation/validation/failure/artifact/interpretation stages with the same rubric"
  "whether deep technical externalisation is enriched beyond ordinary peer practice"
  "selection, targeting, actor identity, motive, harm, or restricted-to-public transfer"

nonRoutineRestrictedTransferNeedsClosedPersonEvidence : W.ExternalisationSelectionFrontier
nonRoutineRestrictedTransferNeedsClosedPersonEvidence = W.externalisation-selection-frontier
  W.restrictedToPublicTransfer
  W.missingPersonFeatureEvidence
  "Reza now closes a routine patent-confidentiality -> statutory-publication transition. For the stronger non-routine H_B, recover a completed same-object contractual proprietary, controlled-government, export-controlled, classified/declassification or discretionary-disclosure transition. Eskridge/POAMS remains the strongest candidate but Amy's exact object identity is still open."
  "a non-routine completed person-level B witness eligible for like-for-like boundary-kind controls"
  "sensitive disclosure merely from routine patent publication; enrichment, selection, actor identity, motive or harm"

deepExternalisationNeedsFeatureAwareSelector : W.ExternalisationSelectionFrontier
deepExternalisationNeedsFeatureAwareSelector = W.externalisation-selection-frontier
  W.deepTechnicalExternalisation
  W.missingFeatureAwareSelector
  "after enrichment is tested, identify a real observer/review system that can discriminate externalisation depth rather than merely see public scientists"
  "the visibility/discrimination half of an externalisation-selection hypothesis"
  "causal selection, targeting, actor identity or harm"

record CurrentExternalisationBoundaryAssessment : Set where
  constructor current-externalisation-boundary-assessment
  field
    loureiroDeepWitnessOwned : Bool
    loureiroDeepWitnessOwnedIsTrue : loureiroDeepWitnessOwned ≡ true

    amyAttemptedBoundaryTransitionCandidateLocated : Bool
    amyAttemptedBoundaryTransitionCandidateLocatedIsTrue :
      amyAttemptedBoundaryTransitionCandidateLocated ≡ true

    amyExactSameObjectWeldLocated : Bool
    amyExactSameObjectWeldLocatedIsFalse :
      amyExactSameObjectWeldLocated ≡ false

    anyClosedBoundaryWitnessLocated : Bool
    anyClosedBoundaryWitnessLocatedIsTrue :
      anyClosedBoundaryWitnessLocated ≡ true

    rezaRoutinePatentBoundaryClosed : Bool
    rezaRoutinePatentBoundaryClosedIsTrue :
      rezaRoutinePatentBoundaryClosed ≡ true

    anyClosedNonRoutineSensitiveBoundaryWitnessLocated : Bool
    anyClosedNonRoutineSensitiveBoundaryWitnessLocatedIsFalse :
      anyClosedNonRoutineSensitiveBoundaryWitnessLocated ≡ false

    deepRosterEnrichmentEstablished : Bool
    deepRosterEnrichmentEstablishedIsFalse :
      deepRosterEnrichmentEstablished ≡ false

    boundaryRosterEnrichmentEstablished : Bool
    boundaryRosterEnrichmentEstablishedIsFalse :
      boundaryRosterEnrichmentEstablished ≡ false

    featureAwareSelectorEstablished : Bool
    featureAwareSelectorEstablishedIsFalse :
      featureAwareSelectorEstablished ≡ false

canonicalCurrentExternalisationBoundaryAssessment :
  CurrentExternalisationBoundaryAssessment
canonicalCurrentExternalisationBoundaryAssessment =
  current-externalisation-boundary-assessment
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
