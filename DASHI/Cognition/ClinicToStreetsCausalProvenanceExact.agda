module DASHI.Cognition.ClinicToStreetsCausalProvenanceExact where

------------------------------------------------------------------------
-- FROM THE CLINIC TO THE STREETS: CAUSAL-PROVENANCE FORMALISATION
--
-- Source boundary:
--   This owner formalises the causal / interpretive structure represented in
--   the supplied reel transcript about Lara Sheehi's 2026 book.  The reel is
--   treated as an attributed source, not as automatic theorem authority for
--   historical, clinical, political, or causal claims.
--
-- Core idea:
--   structural -> intimate/familial -> intrapsychic
--
-- is kept distinct from the lossy atomising projection
--
--   intimate/familial -> intrapsychic.
--
-- The reusable primitive is causal-provenance erasure.  Psychic intrusion,
-- depoliticisation, pathologisation and counterinsurgent effect are represented
-- as typed interpretation/effect surfaces.  Deliberate intent remains a
-- separate coordinate and is never inferred merely from effect.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.CognitiveWarfarePlatoTraumaDetectorWeldExact as Detector

------------------------------------------------------------------------
-- 1. Typed causal levels and mechanisms.
------------------------------------------------------------------------

data CausalLevel : Set where
  structural institutional communal familial interpersonal intrapsychic : CausalLevel

data Mechanism : Set where
  extraction occupation violence alienation normalisation individualisation
  pathologisation activation internalisation psychicIntrusion affectModulation
  depoliticisation : Mechanism

data Affect : Set where
  fear confusion despair exhaustion anger grief agency : Affect

data Direction : Set where
  decreases unchanged increases : Direction

data IntentStatus : Set where
  intentUnknown intentAttributed intentEstablished : IntentStatus

------------------------------------------------------------------------
-- 2. Source-claim typing.
------------------------------------------------------------------------

data ClaimKind : Set where
  observation interpretation causalClaim historicalClaim attribution
  normativeClaim autobiographicalReport recommendation : ClaimKind

data EpistemicStatus : Set where
  attributed reported sourceChecked independentlyEstablished : EpistemicStatus

record SourceClaim : Set where
  constructor source-claim
  field
    startSecond : Nat
    endSecond : Nat
    propositionLabel : String
    speakerLabel : String
    attributedSourceLabel : String
    kind : ClaimKind
    status : EpistemicStatus

familyActivationClaim : SourceClaim
familyActivationClaim =
  source-claim
    135 145
    "family as intimate site where structural inequalities are activated, internalised, and made to seem normal"
    "reel narrator"
    "attributed to Lara Sheehi"
    causalClaim
    attributed

therapyCounterinsurgencyClaim : SourceClaim
therapyCounterinsurgencyClaim =
  source-claim
    29 38
    "therapy can function as counterinsurgency"
    "reel narrator"
    "attributed to Lara Sheehi / Fanon lineage"
    interpretation
    attributed

------------------------------------------------------------------------
-- 3. Causal traces preserve level provenance.
------------------------------------------------------------------------

record CausalTrace : Set where
  constructor causal-trace
  field
    upstream : CausalLevel
    intimateSite : CausalLevel
    downstream : CausalLevel
    upstreamToSite : Mechanism
    siteToDownstream : Mechanism

canonicalStructuralFamilyPsychicTrace : CausalTrace
canonicalStructuralFamilyPsychicTrace =
  causal-trace structural familial intrapsychic activation internalisation

------------------------------------------------------------------------
-- 4. Visibility state and causal-provenance erasure.
------------------------------------------------------------------------

record ProvenanceVisibility : Set where
  constructor provenance-visibility
  field
    structuralVisible : Bool
    intimateVisible : Bool
    intrapsychicVisible : Bool

fullContext : ProvenanceVisibility
fullContext = provenance-visibility true true true

atomisedContext : ProvenanceVisibility
atomisedContext = provenance-visibility false true true

record CausalProvenanceErasure
  (before after : ProvenanceVisibility) : Set where
  constructor causal-provenance-erasure
  field
    beforeStructuralVisible : ProvenanceVisibility.structuralVisible before ≡ true
    afterStructuralHidden : ProvenanceVisibility.structuralVisible after ≡ false
    intimateRetained : ProvenanceVisibility.intimateVisible after ≡ true
    intrapsychicRetained : ProvenanceVisibility.intrapsychicVisible after ≡ true

canonicalAtomisingErasure :
  CausalProvenanceErasure fullContext atomisedContext
canonicalAtomisingErasure =
  causal-provenance-erasure refl refl refl refl

------------------------------------------------------------------------
-- 5. Contextualisation is additive rather than substitutive.
------------------------------------------------------------------------

record ContextPreservingInterpretation : Set where
  constructor context-preserving-interpretation
  field
    structuralCauseAdmissible : Bool
    intimateCauseAdmissible : Bool
    intrapsychicCauseAdmissible : Bool
    downstreamCauseErasedByUpstream : Bool

canonicalContextPreservingInterpretation : ContextPreservingInterpretation
canonicalContextPreservingInterpretation =
  context-preserving-interpretation true true true false

------------------------------------------------------------------------
-- 6. Psychic intrusion as an effect transformation with separate intent.
------------------------------------------------------------------------

record PsychicState : Set where
  constructor psychic-state
  field
    fearPresent : Bool
    confusionPresent : Bool
    despairPresent : Bool
    causalAttributionDistorted : Bool
    actionSpaceContracted : Bool

record PsychicIntrusionTransform : Set where
  constructor psychic-intrusion-transform
  field
    before : PsychicState
    after : PsychicState
    attributionChanged : Bool
    actionSpaceChanged : Bool
    intent : IntentStatus

canonicalPsychicIntrusionEffect : PsychicIntrusionTransform
canonicalPsychicIntrusionEffect =
  psychic-intrusion-transform
    (psychic-state false false false false false)
    (psychic-state true true true true true)
    true true intentUnknown

-- Effect does not manufacture deliberate intent.
data PsychicEffectImpliesEstablishedIntent : Set where

psychicEffectDoesNotEstablishIntent :
  PsychicEffectImpliesEstablishedIntent → ⊥
psychicEffectDoesNotEstablishIntent ()

------------------------------------------------------------------------
-- 7. Counterinsurgent effect is effect-typed, not profession-typed.
------------------------------------------------------------------------

record CounterinsurgentEffect : Set where
  constructor counterinsurgent-effect
  field
    structuralSalience : Direction
    individualBlame : Direction
    collectiveAgency : Direction
    effectObserved : Bool
    deliberateIntent : IntentStatus

canonicalCounterinsurgentEffectSignature : CounterinsurgentEffect
canonicalCounterinsurgentEffectSignature =
  counterinsurgent-effect decreases increases decreases true intentUnknown

-- Having this effect signature does not establish that therapy as a whole is
-- counterinsurgency, nor that a therapist intended the political effect.
data EffectSignatureImpliesTherapyEssence : Set where

effectSignatureDoesNotEstablishTherapyEssence :
  EffectSignatureImpliesTherapyEssence → ⊥
effectSignatureDoesNotEstablishTherapyEssence ()

------------------------------------------------------------------------
-- 8. Reskilling / provenance restoration.
------------------------------------------------------------------------

record ReskillingTransform : Set where
  constructor reskilling-transform
  field
    structuralProvenanceRestored : Bool
    levelDifferentiationPreserved : Bool
    causalResolution : Direction
    confusion : Direction
    actionSpace : Direction

canonicalReskillingTransform : ReskillingTransform
canonicalReskillingTransform =
  reskilling-transform true true increases decreases increases

------------------------------------------------------------------------
-- 9. Cross-pollination with the existing cognitive-warfare / Plato / trauma
-- detector.  The existing exact owner already proves content, cone deformation
-- and provenance are independent coordinates.  We retain that boundary here.
------------------------------------------------------------------------

inheritedDetectorBoundary : Detector.CognitiveDetectorWeldBoundary
inheritedDetectorBoundary = Detector.canonicalCognitiveDetectorWeldBoundary

coneDeformationStillDoesNotEstablishInfluence :
  Detector.ConeDeformationImpliesInfluence → ⊥
coneDeformationStillDoesNotEstablishInfluence =
  Detector.coneDeformationDoesNotEstablishInfluence

provenanceStillDoesNotEstablishTruth :
  Detector.ProvenanceImpliesTruth → ⊥
provenanceStillDoesNotEstablishTruth =
  Detector.provenanceDoesNotEstablishTruth

------------------------------------------------------------------------
-- 10. Promotion boundary.
------------------------------------------------------------------------

record ClinicToStreetsBoundary : Set where
  constructor clinic-to-streets-boundary
  field
    reelClaimsAreAttributed : Bool
    structuralContextCanCoexistWithIntrapsychicCause : Bool
    atomisationCanEraseUpstreamProvenance : Bool
    psychicEffectImpliesIntent : Bool
    counterinsurgentEffectImpliesTherapyEssence : Bool
    provenanceImpliesTruth : Bool
    coneDeformationImpliesHostileInfluence : Bool
    reskillingRestoresProvenanceCoordinate : Bool

canonicalClinicToStreetsBoundary : ClinicToStreetsBoundary
canonicalClinicToStreetsBoundary =
  clinic-to-streets-boundary
    true true true false false false false true
