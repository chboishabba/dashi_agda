module DASHI.Cognition.HardtDeltaSteelmanMaxCutExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- HARDT / BIOCYBERNAUT DELTA CLAIM: CLAIM-TYPED STEELMAN
-- Stacked on psychotronics PR #1242; does not create new field ontology.
-- No experimental, military or paranormal efficacy claim is admitted.
------------------------------------------------------------------------

hardtOriginalPost : Source.AttributedSource
hardtOriginalPost = Source.mkNoDOISource
  "BioCybernaut Institute (publisher); James V. Hardt (attributed speaker)"
  "Instagram delta-training and alleged assassination testimony reel"
  "Creator's post DchjvH2B98C, visible in user-supplied screenshot; post date unverified"
  "date of post not authenticated; screenshot acquired 2026-10-24"
  "https://www.instagram.com/reel/DchjvH2B98C/"
  Source.practitionerSource
  "First-party publication of a claim; neither the asserted unit nor outcome rate nor field mechanism is independently demonstrated"
  Source.publicAttribution

hardtPublic2017 : Source.AttributedSource
hardtPublic2017 = Source.mkNoDOISource
  "James V. Hardt / BioCybernaut Institute"
  "Your Wealth and Your Brain Waves"
  "First-party article, claimed waking delta influence and unpublished author manuscript"
  "online by 2017 (exact source-body publication timestamp unverified)"
  "https://biocybernaut.com/blog/your-wealth-and-brain-waves/"
  Source.practitionerSource
  "Claimed influence and ethics prerequisite, not independently reproduced intervention evidence"
  Source.publicAttribution

loudermilk2020 : Source.AttributedSource
loudermilk2020 = Source.mkNoDOISource
  "Derek Loudermilk (host); James V. Hardt (interviewee)"
  "Dr. James Hardt | Brainwaves, The Force, Creativity, Kundalini, ESP and more"
  "Host's own episode page dated 24 December 2020"
  "2020-12-24"
  "https://derekloudermilk.com/james-hardt/"
  Source.practitionerSource
  "Original host page advertises alleged remote assassination discussion, not independent corroboration of deaths"
  Source.publicAttribution

data Hypothesis : Set where
  sharedCueOrBias : Hypothesis
  measurableMaxwell : Hypothesis
  extraLocalMediator : Hypothesis
  operationalNonlocal : Hypothesis

data EvidenceClass : Set where
  firstPartyAssertion : EvidenceClass
  literatureMeasuredField : EvidenceClass
  exactFiniteCalculation : EvidenceClass
  untestedPhysicalHypothesis : EvidenceClass

data TypedLink : Set where
  eegToSourceCurrent : TypedLink
  currentToMagneticField : TypedLink
  magneticFieldToSensorReadout : TypedLink
  receiverInterventionToOutcome : TypedLink

-- Only a direct, source-matched measurement can discharge the last link.
-- No constructor: pending independent admissible real-world receipt.
data IndependentBlindedCausalTrial : Set where

record NonlocalCausalPromotion : Set where
  field
    trial : IndependentBlindedCausalTrial
    mechanism : Hypothesis

------------------------------------------------------------------------
-- Real FINITE result: 8/10 exposed outcomes DO NOT identify causal effect.
-- These are synthetic potential-outcome worlds, not assassination records.
------------------------------------------------------------------------

record TenCaseWorld : Set where
  constructor ten-case-world
  field
    observedWithIntervention : Nat
    counterfactualWithoutIntervention : Nat
open TenCaseWorld

nullEffectWorld : TenCaseWorld
nullEffectWorld = ten-case-world 8 8

maximalEffectWorld : TenCaseWorld
maximalEffectWorld = ten-case-world 8 0

sameObservedTreatedCount :
  observedWithIntervention nullEffectWorld ≡
  observedWithIntervention maximalEffectWorld
sameObservedTreatedCount = refl

-- Refutes an asserted universal decoder from treated-count equality
-- to the unobserved baseline. This is an IDENTIFIABILITY obstruction,
-- not a negative result about an actual biofeedback intervention.
noUniversalControlDecoder :
  ((u v : TenCaseWorld) →
   observedWithIntervention u ≡ observedWithIntervention v →
   counterfactualWithoutIntervention u ≡
   counterfactualWithoutIntervention v) → ⊥
noUniversalControlDecoder claimed with
  claimed nullEffectWorld maximalEffectWorld refl
... | ()

-- Count of participants cannot be substituted for count of attempted
-- interventions: denominators are distinct provenance-typed fields.
record ClaimedRate : Set where
  constructor claimed-rate
  field
    numberOfParticipants : Nat
    numberOfAttempts : Nat
    numberOfSourceDefinedSuccesses : Nat

-- Real measurements, the exact target/source action, calibrated transfer,
-- consent, blinded allocation and independent replication are absent here.
-- An empty evidence type is an unfilled local receipt, NOT a theorem
-- that all possible physical phenomena are impossible.
