module DASHI.Biology.OEFMeasurementPolicyHyperformalism where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF
import DASHI.Core.PolicyRelativeProjectionSafety as Policy

------------------------------------------------------------------------
-- OEF SOURCE / REFERENCE BOUNDARIES
--
-- Petrea Redmond, Amanda Heffernan, Lindy Abawi, Alice Brown, Robyn Henderson,
-- "An Online Engagement Framework for Higher Education",
-- Online Learning 22(1), 183-204 (2018).
-- DOI: 10.24059/olj.v22i1.1175.
--
-- Melissa Fanshawe, Alice Brown, Petrea Redmond,
-- "Using an online engagement framework to redesign the learning environment
-- for higher education students: A design experiment approach",
-- Online Learning 29(2) (2025).
-- DOI: 10.24059/olj.v29i2.4447.
--
-- Alice Brown, Jill Lawrence, Marita Basson, Megan Axelsen, Petrea Redmond,
-- Joanna Turner, Suzanne Maloney, Linda Galligan,
-- "The creation of a nudging protocol to support online student engagement in
-- higher education", Active Learning in Higher Education 24(3), 257-271.
-- DOI: 10.1177/14697874211039077.
--
-- The source papers motivate the domain instances.  The residual, measurement
-- hyperfabric and policy-safety distinctions below are DASHI formal extensions.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The founding OEF describes its indicator list as illustrative/non-definitive.
-- That licenses an *open codomain / residual-admissibility* reading, not the
-- stronger empirical claim that omitted residuals have positive measured mass.
------------------------------------------------------------------------

data ExhaustivenessStatus : Set where
  exhaustiveClaimed : ExhaustivenessStatus
  residualAdmissible : ExhaustivenessStatus

record FrameworkCodomainBoundary : Set where
  constructor frameworkCodomainBoundary
  field
    exhaustivenessStatus : ExhaustivenessStatus
    indicatorSurfaceIsNotWorldCarrier : Bool
    indicatorSurfaceIsNotWorldCarrierIsTrue :
      indicatorSurfaceIsNotWorldCarrier ≡ true

open FrameworkCodomainBoundary public

canonicalOEFCodomainBoundary : FrameworkCodomainBoundary
canonicalOEFCodomainBoundary =
  frameworkCodomainBoundary residualAdmissible true refl

data ResidualAdmissibilityImpliesPositiveResidualMassPermission : Set where

residualAdmissibilityCannotManufacturePositiveMass :
  ResidualAdmissibilityImpliesPositiveResidualMassPermission → ⊥
residualAdmissibilityCannotManufacturePositiveMass ()

------------------------------------------------------------------------
-- Measurement hyperfabric.
-- LMS behaviour, survey self-report, qualitative expression and researcher/OEF
-- coding are distinct observer surfaces over a richer situated state.  No
-- instrument is canonical merely because it is measurable.
------------------------------------------------------------------------

data MeasurementInstrument : Set where
  lmsAnalytics : MeasurementInstrument
  surveySelfReport : MeasurementInstrument
  qualitativeExpression : MeasurementInstrument
  oefResearcherCode : MeasurementInstrument

record MeasurementHyperfabric (State : Set) : Set₁ where
  constructor measurementHyperfabric
  field
    Observation : MeasurementInstrument → Set
    observe :
      (instrument : MeasurementInstrument) →
      State → Observation instrument

open MeasurementHyperfabric public

data InstrumentCanonicalityPermission : Set where

data LMSAccessImpliesCognitiveConnectionPermission : Set where

data ForumPostImpliesSocialConnectionPermission : Set where

instrumentCannotAutomaticallyBecomeCanonical :
  InstrumentCanonicalityPermission → ⊥
instrumentCannotAutomaticallyBecomeCanonical ()

lmsAccessCannotAutomaticallyAssertCognitiveConnection :
  LMSAccessImpliesCognitiveConnectionPermission → ⊥
lmsAccessCannotAutomaticallyAssertCognitiveConnection ()

forumPostCannotAutomaticallyAssertSocialConnection :
  ForumPostImpliesSocialConnectionPermission → ⊥
forumPostCannotAutomaticallyAssertSocialConnection ()

------------------------------------------------------------------------
-- Observation-mass kind is itself part of the consumer/indexing choice.
-- Comment frequency, participation, retention and belonging are not silently
-- interchangeable measures of pedagogical importance.
------------------------------------------------------------------------

data EngagementMassKind : Set where
  qualitativeReferenceMass : EngagementMassKind
  lmsParticipationMass : EngagementMassKind
  retentionMass : EngagementMassKind
  belongingMass : EngagementMassKind
  pedagogicalValueMass : EngagementMassKind

data CommentMassImpliesPedagogicalValuePermission : Set where

commentFrequencyCannotAutomaticallyAssertPedagogicalValue :
  CommentMassImpliesPedagogicalValuePermission → ⊥
commentFrequencyCannotAutomaticallyAssertPedagogicalValue ()

------------------------------------------------------------------------
-- Source-bound 2025 redesign observation surface.
-- The published paper reports 24 course offerings and identifies cognitive,
-- behavioural and emotional elements as highly valued.  The exact 8%/5%
-- social qualitative-reference shares supplied in the accompanying analysis
-- are retained here only as source observations, not as evidence that social
-- engagement is dynamically irrelevant or pedagogically unimportant.
------------------------------------------------------------------------

record OEFDesignExperimentObservation : Set where
  constructor oefDesignExperimentObservation
  field
    courseOfferings : Nat
    y1SocialQualitativePercent : Nat
    y3SocialQualitativePercent : Nat
    interpretationBoundary : String

open OEFDesignExperimentObservation public

canonicalOEFDesignExperimentObservation : OEFDesignExperimentObservation
canonicalOEFDesignExperimentObservation =
  oefDesignExperimentObservation
    24
    8
    5
    "Qualitative-reference frequency is one observation surface only; it is not promoted to pedagogical-value mass, universal student importance, or dynamic irrelevance."

------------------------------------------------------------------------
-- Reuse the existing OEF situated feedback hypervoxel and the generic policy
-- layer.  This adapter records that a framework-guided redesign or nudge is a
-- quotient -> policy -> transition loop whose safety must be justified at the
-- relevant consumer/policy horizon.
------------------------------------------------------------------------

record OEFPolicyLoopAdapter : Set₁ where
  constructor oefPolicyLoopAdapter
  field
    situatedFeedbackState : OEF.FeedbackHypervoxel
    sourceCodomainBoundary : FrameworkCodomainBoundary
    policySafetyIsSeparateObligation : Bool
    policySafetyIsSeparateObligationIsTrue :
      policySafetyIsSeparateObligation ≡ true
    reading : String

open OEFPolicyLoopAdapter public

canonicalOEFPolicyLoopAdapter : OEFPolicyLoopAdapter
canonicalOEFPolicyLoopAdapter =
  oefPolicyLoopAdapter
    OEF.canonicalFeedbackHypervoxel
    canonicalOEFCodomainBoundary
    true refl
    "OEF supplies a useful coarse engagement chart and the redesign/nudge literature supplies intervention loops, but LMS, survey, qualitative and OEF-code observers remain distinct fibres. A low-frequency observation on one fibre cannot be promoted to low pedagogical value, and an intervention driven by a coarse surface requires its own PolicyRelativeSafety or stronger DynamicConsumerSafety witness."
