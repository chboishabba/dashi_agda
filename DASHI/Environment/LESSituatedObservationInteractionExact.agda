module DASHI.Environment.LESSituatedObservationInteractionExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.PredictionEnvelopeExact as Prediction
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as Kimmerer
import DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact as LES

------------------------------------------------------------------------
-- SITUATED OBSERVE-AND-INTERACT FOR LES
--
-- Source calibration / interpretation boundary:
-- The supplied permaculture material identifies "Observe and Interact" as a
-- canonical design principle and emphasizes place-specific, time-indexed,
-- iterative observation before stronger design commitments.  The same supplied
-- discussion also stresses that Indigenous/local knowledge is situated and
-- relational, so shared observations must not erase provenance, governance or
-- epistemic history.  The exact finite constructions below are DASHI
-- mathematics; they are not attributed to Holmgren, Kimmerer or any supplied
-- secondary source.
------------------------------------------------------------------------

data Site : Set where
  wetlandMargin uplandPlot : Site

data Season : Set where
  wetSeason drySeason : Season

data ObservationMethod : Set where
  directFieldObservation instrumentSurvey : ObservationMethod

data EcologicalReading : Set where
  sameVisibleCondition changedVisibleCondition : EcologicalReading

data SmallInteraction : Set where
  noIntervention reversibleProbe : SmallInteraction

data ResponseReading : Set where
  unchangedAfterProbe changedAfterProbe : ResponseReading

record SituatedObservation : Set where
  constructor situatedObservation
  field
    site : Site
    season : Season
    method : ObservationMethod
    knowledgeHistory : Kimmerer.KnowledgeHistory
    reading : EcologicalReading

open SituatedObservation public

-- A deliberately lossy public surface: it keeps only the reading.
anonymousReading : SituatedObservation → EcologicalReading
anonymousReading = reading

ObservationContext : Set
ObservationContext =
  Site × (Season × (ObservationMethod × Kimmerer.Provenance))

observationContext : SituatedObservation → ObservationContext
observationContext observation =
  site observation ,
    (season observation ,
      (method observation , Kimmerer.provenance (knowledgeHistory observation)))

SituatedObservationSignature : Set
SituatedObservationSignature = EcologicalReading × ObservationContext

situatedObservationSignature :
  SituatedObservation → SituatedObservationSignature
situatedObservationSignature observation =
  anonymousReading observation , observationContext observation

indigenousWetSeasonObservation : SituatedObservation
indigenousWetSeasonObservation =
  situatedObservation
    wetlandMargin
    wetSeason
    directFieldObservation
    Kimmerer.indigenousHistory
    sameVisibleCondition

scientificWetSeasonObservation : SituatedObservation
scientificWetSeasonObservation =
  situatedObservation
    wetlandMargin
    wetSeason
    directFieldObservation
    Kimmerer.scientificHistory
    sameVisibleCondition

indigenousDrySeasonObservation : SituatedObservation
indigenousDrySeasonObservation =
  situatedObservation
    wetlandMargin
    drySeason
    directFieldObservation
    Kimmerer.indigenousHistory
    sameVisibleCondition

uplandWetSeasonObservation : SituatedObservation
uplandWetSeasonObservation =
  situatedObservation
    uplandPlot
    wetSeason
    directFieldObservation
    Kimmerer.indigenousHistory
    sameVisibleCondition

------------------------------------------------------------------------
-- Positive situated-observation theorem shape:
-- same ecological reading does not imply same observation context.
------------------------------------------------------------------------

anonymousReadingCannotRecoverSituatedSignature :
  INF.FactorsThrough anonymousReading situatedObservationSignature → ⊥
anonymousReadingCannotRecoverSituatedSignature =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      indigenousWetSeasonObservation
      scientificWetSeasonObservation
      refl
      (λ ()))

anonymousReadingCannotRecoverSeason :
  INF.FactorsThrough anonymousReading season → ⊥
anonymousReadingCannotRecoverSeason =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      indigenousWetSeasonObservation
      indigenousDrySeasonObservation
      refl
      (λ ()))

anonymousReadingCannotRecoverSite :
  INF.FactorsThrough anonymousReading site → ⊥
anonymousReadingCannotRecoverSite =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      indigenousWetSeasonObservation
      uplandWetSeasonObservation
      refl
      (λ ()))

anonymousReadingCannotRecoverProvenance :
  INF.FactorsThrough
    anonymousReading
    (λ observation → Kimmerer.provenance (knowledgeHistory observation)) →
  ⊥
anonymousReadingCannotRecoverProvenance =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      indigenousWetSeasonObservation
      scientificWetSeasonObservation
      refl
      (λ ()))

-- Re-labelling an anonymous reading still cannot reconstruct what was erased.
rechartingAnonymousReadingCannotRecoverSituatedSignature :
  ∀ {Recharted : Set} →
  (rechart : EcologicalReading → Recharted) →
  INF.FactorsThrough
    (λ observation → rechart (anonymousReading observation))
    situatedObservationSignature →
  ⊥
rechartingAnonymousReadingCannotRecoverSituatedSignature rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart
    (INF.nonFactorabilityWitness
      indigenousWetSeasonObservation
      scientificWetSeasonObservation
      refl
      (λ ()))

------------------------------------------------------------------------
-- Stage-6 evidence geometry.
--
-- A situated observation is not "more true" merely because it carries more
-- coordinates.  It is a strictly richer evidence carrier for consumers that
-- require those coordinates.  Full situated evidence point-identifies the
-- matching signature; anonymous reading does not.
------------------------------------------------------------------------

situatedCompatible :
  Prediction.Compatible SituatedObservationSignature SituatedObservation
situatedCompatible evidence observation =
  situatedObservationSignature observation ≡ evidence

situatedEvidencePointIdentifiesSignature :
  (evidence : SituatedObservationSignature) →
  Prediction.PointIdentifiable
    situatedCompatible situatedObservationSignature evidence
situatedEvidencePointIdentifiesSignature evidence left right leftOK rightOK =
  trans leftOK (sym rightOK)

situatedEvidenceHasUniqueSignatureEnvelope :
  (evidence : SituatedObservationSignature) →
  Prediction.EnvelopeUnique
    situatedCompatible situatedObservationSignature evidence
situatedEvidenceHasUniqueSignatureEnvelope evidence =
  Prediction.pointIdentifiableImpliesEnvelopeUnique
    (situatedEvidencePointIdentifiesSignature evidence)

anonymousCompatible :
  Prediction.Compatible EcologicalReading SituatedObservation
anonymousCompatible evidence observation = anonymousReading observation ≡ evidence

anonymousEvidenceDoesNotPointIdentifySignature :
  Prediction.PointIdentifiable
    anonymousCompatible
    situatedObservationSignature
    sameVisibleCondition →
  ⊥
anonymousEvidenceDoesNotPointIdentifySignature identifiable =
  (λ ())
    (identifiable
      indigenousWetSeasonObservation
      scientificWetSeasonObservation
      refl
      refl)

------------------------------------------------------------------------
-- Observe -> interact -> observe again.
--
-- "Interact" is represented as a small, typed probe whose response becomes
-- additional evidence.  This is epistemically useful without implying that an
-- observation or probe creates authority to intervene.
------------------------------------------------------------------------

record ObserveInteractCycle : Set where
  constructor observeInteractCycle
  field
    before : SituatedObservation
    interaction : SmallInteraction
    response : ResponseReading
    after : SituatedObservation

open ObserveInteractCycle public

record ContextPreservingCycle (cycle : ObserveInteractCycle) : Set where
  constructor contextPreservingCycle
  field
    sameSite : site (before cycle) ≡ site (after cycle)
    sameKnowledgeHistory :
      knowledgeHistory (before cycle) ≡ knowledgeHistory (after cycle)

open ContextPreservingCycle public

canonicalReversibleObservationCycle : ObserveInteractCycle
canonicalReversibleObservationCycle =
  observeInteractCycle
    indigenousWetSeasonObservation
    reversibleProbe
    changedAfterProbe
    (situatedObservation
      wetlandMargin
      wetSeason
      directFieldObservation
      Kimmerer.indigenousHistory
      changedVisibleCondition)

canonicalCyclePreservesDeclaredContext :
  ContextPreservingCycle canonicalReversibleObservationCycle
canonicalCyclePreservesDeclaredContext =
  contextPreservingCycle refl refl

CycleEvidence : Set
CycleEvidence = SituatedObservationSignature × ResponseReading

cycleEvidence : ObserveInteractCycle → CycleEvidence
cycleEvidence cycle =
  situatedObservationSignature (after cycle) , response cycle

-- A response adds an explicit evidence coordinate rather than overwriting the
-- pre-existing situated observation.
cycleEvidenceRetainsAfterObservation :
  (cycle : ObserveInteractCycle) →
  proj₁ (cycleEvidence cycle) ≡ situatedObservationSignature (after cycle)
cycleEvidenceRetainsAfterObservation cycle = refl

------------------------------------------------------------------------
-- Cross-pollination with the full LES planning carrier.
--
-- The observation principle supplies richer evidence; it does not replace the
-- history/relation/provenance/justice signature already retained by LES #637.
------------------------------------------------------------------------

record SituatedObservationForLESPlanning : Set where
  constructor situatedObservationForLESPlanning
  field
    environmentalObservation : SituatedObservation
    planningState : LES.FullLESSituatedState

open SituatedObservationForLESPlanning public

LESObservationPlanningSignature : Set
LESObservationPlanningSignature =
  SituatedObservationSignature × LES.FullPlanningSignature

lesObservationPlanningSignature :
  SituatedObservationForLESPlanning → LESObservationPlanningSignature
lesObservationPlanningSignature state =
  situatedObservationSignature (environmentalObservation state) ,
    LES.fullPlanningSignature (planningState state)

-- The observation layer and planning layer remain jointly retained.  Neither
-- is definitionally substituted for the other.

record ObserveInteractPlanningBoundary : Set where
  constructor observeInteractPlanningBoundary
  field
    anonymousReadingIsSituatedObservation : Bool
    anonymousReadingIsSituatedObservationIsFalse :
      anonymousReadingIsSituatedObservation ≡ false

    sameReadingImpliesSameSite : Bool
    sameReadingImpliesSameSiteIsFalse : sameReadingImpliesSameSite ≡ false

    sameReadingImpliesSameSeason : Bool
    sameReadingImpliesSameSeasonIsFalse : sameReadingImpliesSameSeason ≡ false

    sameReadingImpliesSameKnowledgeProvenance : Bool
    sameReadingImpliesSameKnowledgeProvenanceIsFalse :
      sameReadingImpliesSameKnowledgeProvenance ≡ false

    interactionIsAutomaticallyAuthorizedIntervention : Bool
    interactionIsAutomaticallyAuthorizedInterventionIsFalse :
      interactionIsAutomaticallyAuthorizedIntervention ≡ false

    permaculturePrincipleProvesEmpiricalEnvironmentalDynamics : Bool
    permaculturePrincipleProvesEmpiricalEnvironmentalDynamicsIsFalse :
      permaculturePrincipleProvesEmpiricalEnvironmentalDynamics ≡ false

canonicalObserveInteractPlanningBoundary : ObserveInteractPlanningBoundary
canonicalObserveInteractPlanningBoundary =
  observeInteractPlanningBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
