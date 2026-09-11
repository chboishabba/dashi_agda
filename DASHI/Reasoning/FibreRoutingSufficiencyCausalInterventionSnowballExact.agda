module DASHI.Reasoning.FibreRoutingSufficiencyCausalInterventionSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Reasoning.FibreRoutingRateDistortionInformationBottleneckSnowballExact as RateIB
import DASHI.Law.LegalFactualCausationButForExact as LegalButFor

------------------------------------------------------------------------
-- IBRAHIM FOLLOW:
-- rate-distortion -> sufficient statistic -> causal inference /
-- causal representation -> intervention -> mechanistic consumer.
--
-- Snowball attribution requires stable link/identifier coordinates when
-- available: QID, DOI/arXiv/official identifier, canonical URL, and explicit
-- source role.  These coordinates travel together but create no proof.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim sufficiency/causal-intervention snowball"
  "verified external concept identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "identity checked 2026-09-11; QID does not establish statistical sufficiency for a DASHI consumer, causal identification, intervention validity or mechanism")

sufficientStatisticQid : Identity.ExternalIdentityDemand
sufficientStatisticQid = mkQid "sufficient statistic" "Q1099110"

causalInferenceQid : Identity.ExternalIdentityDemand
causalInferenceQid = mkQid "causal inference" "Q5054566"

causalRepresentationLearningQid : Identity.ExternalIdentityDemand
causalRepresentationLearningQid = Identity.mkOptionalIdentityDemand
  "Ibrahim sufficiency/causal-intervention snowball"
  "exact concept identity"
  "causal representation learning"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact same-concept QID promoted in this pass; causal inference Q5054566 and generic representation identities do not substitute")

interventionConsumerQid : Identity.ExternalIdentityDemand
interventionConsumerQid = Identity.mkOptionalIdentityDemand
  "Ibrahim sufficiency/causal-intervention snowball"
  "repo-native intervention consumer"
  "intervention-predictive adequacy"
  Identity.wikidataQid
  (Identity.notApplicable
    "DASHI consumer-relative relation; external identity is not required")

------------------------------------------------------------------------
-- Dewey: only inspected coordinates are admitted.
------------------------------------------------------------------------

data CausalDeweyResolution : Set where
  deweyVerified : String → String → CausalDeweyResolution
  deweyUnresolved : String → CausalDeweyResolution

record CausalDeweyCoordinate : Set where
  constructor causal-dewey-coordinate
  field
    subjectLabel : String
    resolution : CausalDeweyResolution
    classificationCreatesConsumerAdequacy : Bool
open CausalDeweyCoordinate public

sufficientStatisticDewey : CausalDeweyCoordinate
sufficientStatisticDewey = causal-dewey-coordinate
  "sufficient statistic"
  (deweyUnresolved "no exact inspected DDC statement promoted for Q1099110")
  false

causalInferenceDewey : CausalDeweyCoordinate
causalInferenceDewey = causal-dewey-coordinate
  "causal inference"
  (deweyUnresolved "Wikidata Q5054566 exposes LCC in the inspected record, but no exact DDC coordinate is promoted here")
  false

causalRepresentationDewey : CausalDeweyCoordinate
causalRepresentationDewey = causal-dewey-coordinate
  "causal representation learning"
  (deweyVerified "600" "University of Tuebingen repository classifies Schölkopf et al. 2021 under DDC 600; this is publication-repository classification, not a unique concept Dewey identity")
  false

------------------------------------------------------------------------
-- Source roles and canonical links.
------------------------------------------------------------------------

pearlCausalitySource : Attribution.AttributedSource
pearlCausalitySource = Attribution.mkDOISource
  "Judea Pearl"
  "Causality: Models, Reasoning, and Inference, Second Edition"
  "Cambridge University Press"
  "2009/2013 online"
  "10.1017/CBO9780511803161"
  "https://doi.org/10.1017/CBO9780511803161"
  Attribution.academicBookSource
  "foundational theoretical monograph for graphical/counterfactual causal inference and interventions; primary theory/reference source for Pearl's framework, not a proof that every DASHI representation is causal"
  Attribution.publicAttribution

scholkopfCausalRepresentationSource : Attribution.AttributedSource
scholkopfCausalRepresentationSource = Attribution.mkDOISource
  "Bernhard Schölkopf; Francesco Locatello; Stefan Bauer; Nan Rosemary Ke; Nal Kalchbrenner; Anirudh Goyal; Yoshua Bengio"
  "Toward Causal Representation Learning"
  "Proceedings of the IEEE 109(5), 612-634"
  "2021"
  "10.1109/JPROC.2021.3058954"
  "https://doi.org/10.1109/JPROC.2021.3058954"
  Attribution.academicArticleSource
  "review/synthesis and research-agenda source connecting machine learning representations with causal variables, transfer and intervention; not a primary empirical validation of one universal causal representation learner"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Statistical sufficiency is consumer/index relative; it does not imply
-- intervention sufficiency.
------------------------------------------------------------------------

data SufficiencyCase : Set where
  sameStatisticObservationallySufficientInterventionSafe
  sameStatisticObservationallySufficientInterventionUnsafe : SufficiencyCase

data StatisticSurface : Set where sameSufficientStatisticSurface : StatisticSurface
data InterventionStatus : Set where interventionPredictionPreserved interventionPredictionLost : InterventionStatus

statisticSurface : SufficiencyCase → StatisticSurface
statisticSurface _ = sameSufficientStatisticSurface

interventionStatus : SufficiencyCase → InterventionStatus
interventionStatus sameStatisticObservationallySufficientInterventionSafe = interventionPredictionPreserved
interventionStatus sameStatisticObservationallySufficientInterventionUnsafe = interventionPredictionLost

statisticInterventionDefect : INF.NonFactorabilityWitness statisticSurface interventionStatus
statisticInterventionDefect = INF.nonFactorabilityWitness
  sameStatisticObservationallySufficientInterventionSafe
  sameStatisticObservationallySufficientInterventionUnsafe
  refl
  (λ ())

statisticalSufficiencyCannotFactorInterventionAdequacy :
  INF.FactorsThrough statisticSurface interventionStatus → ⊥
statisticalSufficiencyCannotFactorInterventionAdequacy =
  INF.witnessRulesOutEveryFlatFactorisation statisticInterventionDefect

------------------------------------------------------------------------
-- Predictive equivalence does not recover causal/mechanistic equivalence.
------------------------------------------------------------------------

data PredictionCase : Set where
  samePredictionDifferentInterventionA samePredictionDifferentInterventionB : PredictionCase

data PredictionSurface : Set where sameObservationalPrediction : PredictionSurface
data CausalRealization : Set where causalRealizationA causalRealizationB : CausalRealization

predictionSurface : PredictionCase → PredictionSurface
predictionSurface _ = sameObservationalPrediction

causalRealization : PredictionCase → CausalRealization
causalRealization samePredictionDifferentInterventionA = causalRealizationA
causalRealization samePredictionDifferentInterventionB = causalRealizationB

predictionCausalDefect : INF.NonFactorabilityWitness predictionSurface causalRealization
predictionCausalDefect = INF.nonFactorabilityWitness
  samePredictionDifferentInterventionA samePredictionDifferentInterventionB refl (λ ())

observationalPredictionCannotFactorCausalRealization :
  INF.FactorsThrough predictionSurface causalRealization → ⊥
observationalPredictionCannotFactorCausalRealization =
  INF.witnessRulesOutEveryFlatFactorisation predictionCausalDefect

------------------------------------------------------------------------
-- Existing boundaries are reused.
------------------------------------------------------------------------

rateDistortionBoundary : RateIB.FibreRateDistortionInformationBottleneckBoundary
rateDistortionBoundary = RateIB.canonicalFibreRateDistortionInformationBottleneckBoundary

legalButForBoundary : LegalButFor.LegalButForBoundary
legalButForBoundary = LegalButFor.canonicalLegalButForBoundary

------------------------------------------------------------------------
-- Reverse Ibrahim constraints.
------------------------------------------------------------------------

record CausalReverseConstraint : Set where
  constructor causal-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open CausalReverseConstraint public

statisticsConstraint : CausalReverseConstraint
statisticsConstraint = causal-reverse-constraint
  "Sufficient statistic / statistics"
  "parameter-relative statistical sufficiency, downstream prediction, intervention prediction and arbitrary DASHI consumer adequacy remain distinct"
  false

causalInferenceConstraint : CausalReverseConstraint
causalInferenceConstraint = causal-reverse-constraint
  "Causal inference / counterfactuals"
  "observational fit, graph assumptions, intervention semantics, counterfactual admissibility, identification and uncertainty remain distinct"
  false

representationConstraint : CausalReverseConstraint
representationConstraint = causal-reverse-constraint
  "Representation learning"
  "compact/predictive representation, causal variables, intervention stability and mechanistic realization remain separate"
  false

sensibLawConstraint : CausalReverseConstraint
sensibLawConstraint = causal-reverse-constraint
  "SensibLaw factual causation"
  "model intervention/counterfactual prediction, legally admissible counterfactual, factual causation and scope of liability remain separate"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data SufficientStatisticMeansEveryConsumerAdequate : Set where
data PredictionMeansCausalMechanism : Set where
data CausalRepresentationLabelMeansInterventionSafe : Set where
data CausalInferenceQidCreatesIdentification : Set where
data CanonicalLinkCreatesAuthority : Set where
data DOICreatesCausalValidity : Set where

aSufficientStatisticDoesNotMeanEveryConsumerAdequate : SufficientStatisticMeansEveryConsumerAdequate → ⊥
aSufficientStatisticDoesNotMeanEveryConsumerAdequate ()

predictionDoesNotCreateMechanism : PredictionMeansCausalMechanism → ⊥
predictionDoesNotCreateMechanism ()

causalRepresentationLabelDoesNotCreateInterventionSafety : CausalRepresentationLabelMeansInterventionSafe → ⊥
causalRepresentationLabelDoesNotCreateInterventionSafety ()

causalInferenceQidDoesNotCreateIdentification : CausalInferenceQidCreatesIdentification → ⊥
causalInferenceQidDoesNotCreateIdentification ()

canonicalLinkDoesNotCreateAuthority : CanonicalLinkCreatesAuthority → ⊥
canonicalLinkDoesNotCreateAuthority ()

doiDoesNotCreateCausalValidity : DOICreatesCausalValidity → ⊥
doiDoesNotCreateCausalValidity ()

record FibreSufficiencyCausalInterventionBoundary : Set where
  constructor fibre-sufficiency-causal-intervention-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    canonicalLinksRetained : Bool
    doiOrCanonicalIdentifierRetained : Bool
    sourceRolePrimarySecondaryOrSynthesisExplicit : Bool
    deweyAttachedOnlyWhenInspected : Bool
    statisticalSufficiencySeparatedFromDashiAdequacy : Bool
    observationalPredictionSeparatedFromCausalRealization : Bool
    causalRepresentationSeparatedFromInterventionProof : Bool
    sensibLawCounterfactualBoundaryReused : Bool
    metadataDoesNotCreateAuthority : Bool
    presentAxisVocabularyClaimedComplete : Bool
open FibreSufficiencyCausalInterventionBoundary public

canonicalFibreSufficiencyCausalInterventionBoundary : FibreSufficiencyCausalInterventionBoundary
canonicalFibreSufficiencyCausalInterventionBoundary =
  fibre-sufficiency-causal-intervention-boundary
    true true true true true true true true true true false
