module DASHI.Physics.Semiconductor.Device.LitavisSPADMultimodalObservationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- LITAVIS SPAD MULTIMODAL OBSERVATION
--
-- Thin instance over existing DASHI machinery.  The source material motivates
-- the coordinates; it does not create a new factorisation calculus or promote
-- vendor performance claims into independently established measurements.
------------------------------------------------------------------------

singularPhotonicsLitavisRelease : Source.AttributedSource
singularPhotonicsLitavisRelease =
  Source.mkNoDOISource
    "Singular Photonics"
    "Singular Photonics launches world-first SPAD-based image sensor"
    "Singular Photonics"
    "2026"
    "https://singularphotonics.com/singular-photonics-launches-world-first-spad-image-sensor/"
    Source.institutionalSource
    "primary company release for the source-attested Litavis architecture and claimed operating modes; does not independently validate novelty, latency, power, application performance, or market claims"
    Source.publicAttribution

interestingEngineeringLitavisArticle : Source.AttributedSource
interestingEngineeringLitavisArticle =
  Source.mkNoDOISource
    "Kaif Shaikh"
    "World’s first SPAD image sensor with on-chip photon processing debuts"
    "Interesting Engineering"
    "2026"
    "https://interestingengineering.com/innovation/singular-photonics-litavis-spad-image-sensor"
    Source.newsSource
    "secondary report used as discovery/corroborating context; technical propositions are bounded back to the company release where available"
    Source.publicAttribution

litavisArchitectureDiligence : Diligence.SourceDiligence
litavisArchitectureDiligence =
  Diligence.source-diligence
    "Litavis source-attested multimodal SPAD architecture"
    singularPhotonicsLitavisRelease
    Diligence.primaryProposition
    true
    refl
    "followed the Interesting Engineering source link to the Singular Photonics launch release and compared the architecture claims"
    Diligence.primaryLocated
    "Singular Photonics launch release, Technical details and operating-mode sections"
    "release dated 2026-09-10; atlas read 2026-09-14"
    "Litavis product named by both the company release and the secondary article"
    "launch-state product architecture as publicly described in September 2026"
    "covers reported array sizes, concurrent photon-counting/timestamping surfaces, in-pixel histogramming, multi-event timing, and software-configurable modes"
    "secondary report checked against the company release; no independent benchmark or novelty survey admitted by this owner"
    "architecture fields below are source-attested propositions, not independent physical measurements by DASHI"
    "does not establish world-first priority, achieved system latency, achieved power efficiency, medical suitability, quantum advantage, or application-level performance"

litavisArchitectureAdmission : Diligence.EmpiricalFactAdmission
litavisArchitectureAdmission =
  Diligence.empirical-fact-admission
    litavisArchitectureDiligence
    "the September 2026 company release describes continuous 256 x 256 photon-counting imaging together with timestamped photon events on a 64 x 64 macropixel grid, plus multi-event timing and in-pixel histogramming"
    "bounded to what the named primary company release explicitly describes"
    "source identity and role remain attached to this architecture fixture"
    "no independent benchmark, die inspection, datasheet audit, priority search, or laboratory replication is imported"
    "the admission creates neither scientific authority nor downstream application authority"
    false refl
    false refl
    false refl

record SourceAttestedArchitecture : Set where
  constructor source-attested-architecture
  field
    photonCountingRows : Nat
    photonCountingColumns : Nat
    timestampMacropixelRows : Nat
    timestampMacropixelColumns : Nat
    concurrentPhotonCountingAndTimestamping : Bool
    inPixelHistogramming : Bool
    multiEventTiming : Bool
    softwareConfigurableModes : Bool
    timingScaleReference : String
    sourceBound : Bool
    sourceBoundIsTrue : sourceBound ≡ true

open SourceAttestedArchitecture public

litavisSourceAttestedArchitecture : SourceAttestedArchitecture
litavisSourceAttestedArchitecture =
  source-attested-architecture
    256
    256
    64
    64
    true
    true
    true
    true
    "company release states picosecond-resolution photon timing; no finer numerical timing specification is introduced here"
    true
    refl

------------------------------------------------------------------------
-- Query-indexed information boundary.
--
-- Intensity-only observations can pay an intensity consumer while failing
-- timing and histogram consumers.  A richer multimodal observation can pay
-- those queries in this finite fixture.  This is an information statement,
-- not a claim that every Litavis operating mode exposes every coordinate at
-- every instant or at identical spatial/temporal resolution.
------------------------------------------------------------------------

data SensorState : Set where
  stateA stateB : SensorState

data IntensityObservation : Set where
  sameIntensity : IntensityObservation

data MultimodalObservation : Set where
  multimodalA multimodalB : MultimodalObservation

data LitavisQuery : Set where
  intensityQuery timingQuery histogramQuery : LitavisQuery

data LitavisAnswer : Set where
  intensityAnswer : LitavisAnswer
  timingEarly timingLate : LitavisAnswer
  histogramNarrow histogramBroad : LitavisAnswer

intensityProject : SensorState → IntensityObservation
intensityProject stateA = sameIntensity
intensityProject stateB = sameIntensity

multimodalProject : SensorState → MultimodalObservation
multimodalProject stateA = multimodalA
multimodalProject stateB = multimodalB

litavisAnswer : LitavisQuery → SensorState → LitavisAnswer
litavisAnswer intensityQuery stateA = intensityAnswer
litavisAnswer intensityQuery stateB = intensityAnswer
litavisAnswer timingQuery stateA = timingEarly
litavisAnswer timingQuery stateB = timingLate
litavisAnswer histogramQuery stateA = histogramNarrow
litavisAnswer histogramQuery stateB = histogramBroad

litavisSemantics : Query.QuerySemantics SensorState LitavisQuery LitavisAnswer
litavisSemantics = Query.querySemantics litavisAnswer

IntensityAdequacy : Set₁
IntensityAdequacy =
  Query.AdequateFor intensityProject litavisSemantics intensityQuery

TimingDefect : Set₁
TimingDefect =
  Query.QueryAdequacyDefect intensityProject litavisSemantics timingQuery

HistogramDefect : Set₁
HistogramDefect =
  Query.QueryAdequacyDefect intensityProject litavisSemantics histogramQuery

MultimodalTimingAdequacy : Set₁
MultimodalTimingAdequacy =
  Query.AdequateFor multimodalProject litavisSemantics timingQuery

MultimodalHistogramAdequacy : Set₁
MultimodalHistogramAdequacy =
  Query.AdequateFor multimodalProject litavisSemantics histogramQuery

intensityQueryAdequate : IntensityAdequacy
intensityQueryAdequate =
  Query.factorsForQuery
    (λ observation → intensityAnswer)
    (λ state → refl)

timingQueryDefect : TimingDefect
timingQueryDefect =
  Query.queryAdequacyDefect
    stateA
    stateB
    refl
    (λ ())

histogramQueryDefect : HistogramDefect
histogramQueryDefect =
  Query.queryAdequacyDefect
    stateA
    stateB
    refl
    (λ ())

multimodalTimingAnswer : MultimodalObservation → LitavisAnswer
multimodalTimingAnswer multimodalA = timingEarly
multimodalTimingAnswer multimodalB = timingLate

multimodalHistogramAnswer : MultimodalObservation → LitavisAnswer
multimodalHistogramAnswer multimodalA = histogramNarrow
multimodalHistogramAnswer multimodalB = histogramBroad

multimodalTimingQueryAdequate : MultimodalTimingAdequacy
multimodalTimingQueryAdequate =
  Query.factorsForQuery
    multimodalTimingAnswer
    factor
  where
    factor : (state : SensorState) →
      litavisAnswer timingQuery state ≡
      multimodalTimingAnswer (multimodalProject state)
    factor stateA = refl
    factor stateB = refl

multimodalHistogramQueryAdequate : MultimodalHistogramAdequacy
multimodalHistogramQueryAdequate =
  Query.factorsForQuery
    multimodalHistogramAnswer
    factor
  where
    factor : (state : SensorState) →
      litavisAnswer histogramQuery state ≡
      multimodalHistogramAnswer (multimodalProject state)
    factor stateA = refl
    factor stateB = refl

timingQueryNotAdequate :
  Query.AdequateFor intensityProject litavisSemantics timingQuery → ⊥
timingQueryNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation timingQueryDefect

histogramQueryNotAdequate :
  Query.AdequateFor intensityProject litavisSemantics histogramQuery → ⊥
histogramQueryNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation histogramQueryDefect

------------------------------------------------------------------------
-- Claim firewall.
------------------------------------------------------------------------

record SourceClaimBoundary : Set where
  constructor source-claim-boundary
  field
    primaryCompanyReleaseRetained : Bool
    primaryCompanyReleaseRetainedIsTrue : primaryCompanyReleaseRetained ≡ true
    secondaryArticleRetained : Bool
    secondaryArticleRetainedIsTrue : secondaryArticleRetained ≡ true
    worldFirstIsAttributedClaimNotPriorityProof : Bool
    worldFirstIsAttributedClaimNotPriorityProofIsTrue :
      worldFirstIsAttributedClaimNotPriorityProof ≡ true
    latencyAndPowerBenefitAreClaimsNotBenchmarks : Bool
    latencyAndPowerBenefitAreClaimsNotBenchmarksIsTrue :
      latencyAndPowerBenefitAreClaimsNotBenchmarks ≡ true
    applicationListCreatesValidatedSuitability : Bool
    applicationListCreatesValidatedSuitabilityIsFalse :
      applicationListCreatesValidatedSuitability ≡ false
    softwareConfigurabilityImpliesEqualInformationAcrossModes : Bool
    softwareConfigurabilityImpliesEqualInformationAcrossModesIsFalse :
      softwareConfigurabilityImpliesEqualInformationAcrossModes ≡ false
    citationCreatesScientificAuthority : Bool
    citationCreatesScientificAuthorityIsFalse :
      citationCreatesScientificAuthority ≡ false

canonicalSourceClaimBoundary : SourceClaimBoundary
canonicalSourceClaimBoundary =
  source-claim-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
