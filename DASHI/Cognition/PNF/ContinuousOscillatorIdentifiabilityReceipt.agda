module DASHI.Cognition.PNF.ContinuousOscillatorIdentifiabilityReceipt where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Cognition.PNF.ContinuousOscillatorMemoryRefinementExact as Parent
import DASHI.Cognition.PNF.ContinuousOscillatorSyntheticReceipt as Synthetic

------------------------------------------------------------------------
-- Query-indexed identifiability adapter.
--
-- Identifiability is not one intrinsic Boolean of an observation.  Reuse the
-- repository's existing query-indexed factorisation calculus: a waveform may
-- be adequate for a reconstruction query while the same projection is
-- inadequate for frequency, phase, or complete hidden-state recovery.
-- Numerical near-collisions emitted by the Python producer are diagnostics;
-- they do not construct an exact QueryAdequacyDefect by themselves.
------------------------------------------------------------------------

data OscillatorIdentifiabilityQuery : Set where
  waveformQuery frequencyQuery amplitudeQuery phaseQuery hiddenStateQuery :
    OscillatorIdentifiabilityQuery

queryIndexedAdequacySurface :
  ∀ {State Observation Answer} →
  (State → Observation) →
  Query.QuerySemantics State OscillatorIdentifiabilityQuery Answer →
  OscillatorIdentifiabilityQuery → Set₁
queryIndexedAdequacySurface = Query.AdequateFor

queryIndexedDefectSurface :
  ∀ {State Observation Answer} →
  (State → Observation) →
  Query.QuerySemantics State OscillatorIdentifiabilityQuery Answer →
  OscillatorIdentifiabilityQuery → Set₁
queryIndexedDefectSurface = Query.QueryAdequacyDefect

------------------------------------------------------------------------
-- Parent-following provenance.
------------------------------------------------------------------------

record OscillatorIdentifiabilityParentChain : Set where
  constructor oscillator-identifiability-parent-chain
  field
    structuralParentReference : String
    numericalParentReference : String
    structuralParentCarrierRetained : Bool
    numericalParentExperimentRetained : Bool
    parentImplementationCreatesScientificAuthority : Bool
open OscillatorIdentifiabilityParentChain public

canonicalOscillatorIdentifiabilityParentChain : OscillatorIdentifiabilityParentChain
canonicalOscillatorIdentifiabilityParentChain =
  oscillator-identifiability-parent-chain
    "merged PR #896: ContinuousOscillatorMemoryRefinementExact + RecursiveScaleTransitionExact"
    "PR #909: fixed-frequency synthetic 3/6/9 producer and ContinuousOscillatorSyntheticReceipt"
    true true false

parentOscillatorSchema : Set₁
parentOscillatorSchema = Parent.OscillatorSchema

parentSyntheticReceipt : Synthetic.ContinuousOscillatorSyntheticReceipt
parentSyntheticReceipt = Synthetic.canonicalContinuousOscillatorSyntheticReceipt

------------------------------------------------------------------------
-- Attribution / snowball boundary.
--
-- Blackwell is precedent for comparison of information in experiments, not
-- authorship of this DASHI oscillator construction.  The actual factorisation
-- theorem shape is inherited from QueryIndexedProjectionAdequacyExact, whose
-- own source boundary already records that distinction.
------------------------------------------------------------------------

blackwellSource : Attribution.AttributedSource
blackwellSource = Attribution.mkDOISource
  "David Blackwell"
  "Equivalent Comparisons of Experiments"
  "Annals of Mathematical Statistics 24(2), 265-272"
  "1953"
  "10.1214/aoms/1177729032"
  "https://doi.org/10.1214/aoms/1177729032"
  Attribution.academicArticleSource
  "information-comparison precedent for query-relative observation adequacy; does not author DASHI oscillator dynamics or prove numerical identifiability"
  Attribution.publicAttribution

blackwellSnowball : Snowball.SourceRoleSnowballReceipt blackwellSource
blackwellSnowball = Snowball.canonicalSourceRoleSnowballReceipt blackwellSource

record OscillatorIdentifiabilitySourceBoundary : Set where
  constructor oscillator-identifiability-source-boundary
  field
    attributedSourceCoreRetained : Bool
    snowballRoleInvariantRetained : Bool
    doiRetainedWhenAvailable : Bool
    sourceFormalisationRoleRetained : Bool
    citationImportsProof : Bool
    citationCreatesAuthority : Bool
    shared369DigitsCreateCrossDomainIdentity : Bool
    syntheticExperimentHasInventedOEISIdentity : Bool
    syntheticExperimentHasInventedWikidataIdentity : Bool
open OscillatorIdentifiabilitySourceBoundary public

canonicalOscillatorIdentifiabilitySourceBoundary :
  OscillatorIdentifiabilitySourceBoundary
canonicalOscillatorIdentifiabilitySourceBoundary =
  oscillator-identifiability-source-boundary
    true true true true false false false false false

------------------------------------------------------------------------
-- Numerical/formal and semantic promotion firewalls.
------------------------------------------------------------------------

record OscillatorIdentifiabilityPromotionBoundary : Set where
  constructor oscillator-identifiability-promotion-boundary
  field
    numericalNearCollisionCreatesExactNonfactorabilityProof : Bool
    waveformAdequacyCreatesHiddenStateAdequacy : Bool
    optimizerFailureCreatesMathematicalNonidentifiability : Bool
    learnableFrequencyCreatesNeuroscienceMechanism : Bool
    learnableFrequencyCreatesHebbianIdentity : Bool
    learnableFrequencyCreatesOjaIdentity : Bool
    learnableFrequencyCreatesKuramotoIdentity : Bool
    phaseMismatchCreatesCognitiveDissonanceIdentity : Bool
    threeSixNineCreatesIntrinsicSuperiority : Bool
    continuousPhaseCreatesQuantumInterpretation : Bool
    globalIdentifiabilityPromoted : Bool
open OscillatorIdentifiabilityPromotionBoundary public

canonicalOscillatorIdentifiabilityPromotionBoundary :
  OscillatorIdentifiabilityPromotionBoundary
canonicalOscillatorIdentifiabilityPromotionBoundary =
  oscillator-identifiability-promotion-boundary
    false false false false false false false false false false false
