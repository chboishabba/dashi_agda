module DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact as Transcript
import DASHI.Policy.ABC730PrimarySourceSpeakerResolutionExact as Speakers
import DASHI.Policy.ABC730RationaleSalienceDecisionFunctionExact as Rationale
import DASHI.Policy.AustraliaIsraelGaslightingPoliticalEconomyBridgeExact as Gaslighting

------------------------------------------------------------------------
-- Consumer downstream of transcript/discourse repair.
--
-- The transcript establishes that Australia invoked implementation concerns and
-- unspecified "unintended consequences" for named affected classes.  This
-- owner asks what additional evidence is required before any of those classes
-- can pay a concrete policy-effect proposition, and separately what would be
-- required before Shoebridge's evaluative "gaslighting" characterisation can
-- be promoted beyond attributed rhetoric.
------------------------------------------------------------------------

data EvidenceObligationKind : Set where
  affectedClassIdentity : EvidenceObligationKind
  consequenceSign : EvidenceObligationKind
  causalMechanism : EvidenceObligationKind
  magnitudeOrMateriality : EvidenceObligationKind
  probabilityOrFrequency : EvidenceObligationKind
  temporalHorizon : EvidenceObligationKind
  policyCounterfactual : EvidenceObligationKind
  distributionalIncidence : EvidenceObligationKind
  alternativeInstrumentComparison : EvidenceObligationKind
  decisionChainWeight : EvidenceObligationKind

record PolicyEffectObligation : Set where
  constructor policyEffectObligation
  field
    obligationId : String
    targetReference : String
    kind : EvidenceObligationKind
    sourceReference : String
    paid : Bool
    residual : String

open PolicyEffectObligation public

businessMechanism : PolicyEffectObligation
businessMechanism = policyEffectObligation
  "ABC730-UC-business-mechanism"
  "Australian businesses"
  causalMechanism
  "ABC730 C029"
  false
  "the primary transcript names Australian businesses but does not specify a causal pathway from a settlement import ban to the claimed unintended consequence"

palestinianMechanism : PolicyEffectObligation
palestinianMechanism = policyEffectObligation
  "ABC730-UC-palestinian-mechanism"
  "Palestinians"
  causalMechanism
  "ABC730 C029"
  false
  "the primary transcript names Palestinians but does not specify who would bear what harm/benefit, by what mechanism, with what sign or magnitude"

israeliMechanism : PolicyEffectObligation
israeliMechanism = policyEffectObligation
  "ABC730-UC-israeli-mechanism"
  "Israelis"
  causalMechanism
  "ABC730 C029"
  false
  "the primary transcript names Israelis but does not specify the consequence mechanism, incidence, sign, probability or materiality"

counterfactualComparison : PolicyEffectObligation
counterfactualComparison = policyEffectObligation
  "ABC730-UC-policy-counterfactual"
  "UK-style settlement import ban versus Australia's targeted-measures approach"
  policyCounterfactual
  "ABC730 C017 C028 C029 C035 C040"
  false
  "requires a same-object comparison of expected consequences under the broader ban and the targeted-measures alternative"

alternativeInstrument : PolicyEffectObligation
alternativeInstrument = policyEffectObligation
  "ABC730-UC-alternative-instrument"
  "targeted sanctions versus settlement-linked import/services restrictions"
  alternativeInstrumentComparison
  "ABC730 C017 C035 C040 C045-C047"
  false
  "requires evidence about scope, enforcement, substitution and expected settlement-support reduction for each instrument rather than rhetoric about bluntness alone"

allUnintendedConsequenceObligations : List PolicyEffectObligation
allUnintendedConsequenceObligations =
  businessMechanism ∷ palestinianMechanism ∷ israeliMechanism ∷
  counterfactualComparison ∷ alternativeInstrument ∷ []

------------------------------------------------------------------------
-- Typed evaluative consumer for the Shoebridge characterisation.
------------------------------------------------------------------------

data GaslightingAptnessCoordinate : Set where
  policyObjectiveAcknowledged : GaslightingAptnessCoordinate
  criticisedPolicyMechanismRelevant : GaslightingAptnessCoordinate
  statedProtectiveRationaleSpecified : GaslightingAptnessCoordinate
  statedProtectiveRationaleEvidenceBacked : GaslightingAptnessCoordinate
  contradictionOrInversionDemonstrated : GaslightingAptnessCoordinate
  materialOmissionOrMisrepresentationDemonstrated : GaslightingAptnessCoordinate
  speakerAttributionPaid : GaslightingAptnessCoordinate

record GaslightingAptnessObligation : Set where
  constructor gaslightingAptnessObligation
  field
    coordinate : GaslightingAptnessCoordinate
    sourceReference : String
    paid : Bool
    boundedInterpretation : String

open GaslightingAptnessObligation public

objectivePaid : GaslightingAptnessObligation
objectivePaid = gaslightingAptnessObligation policyObjectiveAcknowledged
  "ABC730 C040-C042"
  true
  "Australia states a two-state solution as its objective while describing settlement expansion/E1/settler violence as extinguishing that possibility"

speakerPaid : GaslightingAptnessObligation
speakerPaid = gaslightingAptnessObligation speakerAttributionPaid
  "DASHI.Policy.ABC730PrimarySourceSpeakerResolutionExact.c032Speaker"
  true
  "the ABC primary transcript pays David Shoebridge as speaker of C032"

mechanismRelevantOpen : GaslightingAptnessObligation
mechanismRelevantOpen = gaslightingAptnessObligation criticisedPolicyMechanismRelevant
  "ABC730 C017 C045-C047 plus external policy-effect evidence required"
  false
  "the source describes the UK measure and settlement-support pathways, but effectiveness against the Australian decision objective still requires evidence"

protectiveRationaleSpecifiedOpen : GaslightingAptnessObligation
protectiveRationaleSpecifiedOpen = gaslightingAptnessObligation statedProtectiveRationaleSpecified
  "ABC730 C029"
  false
  "affected classes are named, but the alleged protective/unintended-consequence mechanism is not specified in the transcript"

protectiveRationaleEvidenceOpen : GaslightingAptnessObligation
protectiveRationaleEvidenceOpen = gaslightingAptnessObligation statedProtectiveRationaleEvidenceBacked
  "same-object impact analysis / modelling / advice not yet attached"
  false
  "requires documentary or empirical evidence that the claimed unintended consequences were expected and materially policy-relevant"

inversionOpen : GaslightingAptnessObligation
inversionOpen = gaslightingAptnessObligation contradictionOrInversionDemonstrated
  "ABC730 C029-C032 plus consequence/mechanism evidence"
  false
  "the critic alleges inversion, but source-level juxtaposition alone does not prove that the stated rationale is internally contradictory or opposite in effect"

misrepresentationOpen : GaslightingAptnessObligation
misrepresentationOpen = gaslightingAptnessObligation materialOmissionOrMisrepresentationDemonstrated
  "decision-chain and public-rationale evidence required"
  false
  "under-specification or non-exhaustiveness alone does not establish deception, concealment or manipulative misrepresentation"

allGaslightingAptnessObligations : List GaslightingAptnessObligation
allGaslightingAptnessObligations =
  objectivePaid ∷ speakerPaid ∷ mechanismRelevantOpen ∷
  protectiveRationaleSpecifiedOpen ∷ protectiveRationaleEvidenceOpen ∷
  inversionOpen ∷ misrepresentationOpen ∷ []

------------------------------------------------------------------------
-- Roadmap status and non-collapse boundaries.
------------------------------------------------------------------------

record PolicyEvaluationRoadmap : Set where
  constructor policyEvaluationRoadmap
  field
    transcriptAttributionPaid : Bool
    policyDifferenceTranscriptPaid : Bool
    consequenceTargetsNamed : Bool
    consequenceMechanismsPaid : Bool
    alternativeInstrumentEffectsPaid : Bool
    decisionChainWeightsPaid : Bool
    evaluativeAptnessPaid : Bool

canonicalPolicyEvaluationRoadmap : PolicyEvaluationRoadmap
canonicalPolicyEvaluationRoadmap =
  policyEvaluationRoadmap true true true false false false false

data NamedAffectedClassProvesConsequence : Set where
namedAffectedClassDoesNotProveConsequence : NamedAffectedClassProvesConsequence → ⊥
namedAffectedClassDoesNotProveConsequence ()

data UnderSpecifiedRationaleProvesGaslighting : Set where
underSpecifiedRationaleDoesNotProveGaslighting : UnderSpecifiedRationaleProvesGaslighting → ⊥
underSpecifiedRationaleDoesNotProveGaslighting ()

data CounterRationaleProvesOppositeEffect : Set where
counterRationaleDoesNotProveOppositeEffect : CounterRationaleProvesOppositeEffect → ⊥
counterRationaleDoesNotProveOppositeEffect ()

data CorrectSpeakerProvesEvaluation : Set where
correctSpeakerDoesNotProveEvaluation : CorrectSpeakerProvesEvaluation → ⊥
correctSpeakerDoesNotProveEvaluation ()

canonicalTranscriptRationale : Transcript.TranscriptClaim
canonicalTranscriptRationale = Transcript.abcAustraliaUnintendedConsequencesRationale

speakerResolutionAnchor : Speakers.PrimarySourceSpeakerResolutionBoundary
speakerResolutionAnchor = Speakers.canonicalPrimarySourceSpeakerResolutionBoundary

rationaleBoundaryAnchor : Rationale.RationaleSalienceBoundary
rationaleBoundaryAnchor = Rationale.canonicalRationaleSalienceBoundary

politicalEconomyBoundaryAnchor : Gaslighting.PoliticalEconomyBoundary
politicalEconomyBoundaryAnchor = Gaslighting.canonicalPoliticalEconomyBoundary
