module DASHI.Physics.GR.GravitationalPredictionAttributionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Physics.GR.GravitationalObservationSourceAtlasExact as Sources
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred
import DASHI.Physics.GR.GravitationalEpistemicLineageExact as Lineage

------------------------------------------------------------------------
-- ATTRIBUTED PREDICTION <-> OBSERVATION
--
-- Carrier identity is not enough.  The exact claim scope supported by the
-- authority must equal the exact prediction claim scope consumed downstream.
------------------------------------------------------------------------

data PredictionAuthority : Set where
  externalTheoryAuthority : Lineage.ExternalTheoryAttributedSource → PredictionAuthority
  internalTheoremAuthority : Lineage.InternalTheoremProofLineage → PredictionAuthority

predictionAuthorityCarrier : PredictionAuthority → String
predictionAuthorityCarrier (externalTheoryAuthority source) =
  Lineage.stableIdentifier source
predictionAuthorityCarrier (internalTheoremAuthority theorem) =
  Lineage.modulePath theorem

predictionAuthorityClaimScope : PredictionAuthority → String
predictionAuthorityClaimScope (externalTheoryAuthority source) =
  Lineage.exactSourceEntitledClaim source
predictionAuthorityClaimScope (internalTheoremAuthority theorem) =
  Lineage.proofStatementScope theorem

record AttributedGravitationalPrediction : Set where
  constructor attributed-gravitational-prediction
  field
    prediction : Pred.GravitationalPredictionReceipt
    authority : PredictionAuthority
    authorityCarrierMatchesPrediction :
      predictionAuthorityCarrier authority ≡ Pred.theoryCarrier prediction
    authorityScopeMatchesPredictionClaim :
      predictionAuthorityClaimScope authority ≡ Pred.predictionClaimScope prediction

open AttributedGravitationalPrediction public

------------------------------------------------------------------------
-- Derived-comparison lineage bindings.
--
-- A DASHI-derived comparison must identify the exact source and authority
-- carriers consumed by that comparison.  A generic lineage record is not
-- sufficient merely because it names plausible upstream sources.
------------------------------------------------------------------------

record SinglePredictionComparisonLineage
    (attributedPrediction : AttributedGravitationalPrediction)
    (observation : Obs.GravitationalObservationReceipt) : Set where
  constructor single-prediction-comparison-lineage
  field
    derivedLineage : Lineage.DASHIDerivedComparisonLineage
    consumedObservationSource : Sources.ObservationAttributedSource
    consumedObservationSourceMatches :
      consumedObservationSource ≡ Obs.attributedObservationSource observation
    consumedPredictionAuthority : PredictionAuthority
    consumedPredictionAuthorityMatches :
      consumedPredictionAuthority ≡ authority attributedPrediction

open SinglePredictionComparisonLineage public

record PairedPredictionComparisonLineage
    (leftPrediction rightPrediction : AttributedGravitationalPrediction)
    (observation : Obs.GravitationalObservationReceipt) : Set where
  constructor paired-prediction-comparison-lineage
  field
    derivedLineage : Lineage.DASHIDerivedComparisonLineage
    consumedObservationSource : Sources.ObservationAttributedSource
    consumedObservationSourceMatches :
      consumedObservationSource ≡ Obs.attributedObservationSource observation
    consumedLeftAuthority : PredictionAuthority
    consumedLeftAuthorityMatches :
      consumedLeftAuthority ≡ authority leftPrediction
    consumedRightAuthority : PredictionAuthority
    consumedRightAuthorityMatches :
      consumedRightAuthority ≡ authority rightPrediction

open PairedPredictionComparisonLineage public

record AttributedPredictionObservationComparison : Set where
  constructor attributed-prediction-observation-comparison
  field
    attributedPrediction : AttributedGravitationalPrediction
    observation : Obs.GravitationalObservationReceipt
    weld :
      Pred.PredictionObservationWeld
        (prediction attributedPrediction)
        observation
    comparisonLineage :
      SinglePredictionComparisonLineage attributedPrediction observation

open AttributedPredictionObservationComparison public

------------------------------------------------------------------------
-- Introspective collision: same authority carrier can support different scopes.
-- A carrier-only observer therefore cannot determine consumer admissibility.
------------------------------------------------------------------------

data ScopeFixture : Set where
  supportedScope unsupportedScope : ScopeFixture

data ScopeDecision : Set where
  scopeAdmitted scopeRejected : ScopeDecision

coarseAuthorityObserver : ScopeFixture → String
coarseAuthorityObserver _ = "same-authority-carrier"

consumerScopeDecision : ScopeFixture → ScopeDecision
consumerScopeDecision supportedScope = scopeAdmitted
consumerScopeDecision unsupportedScope = scopeRejected

coarseAuthorityCollision :
  coarseAuthorityObserver supportedScope ≡ coarseAuthorityObserver unsupportedScope
coarseAuthorityCollision = refl

carrierOnlyObservationDoesNotFixScopeDecision :
  consumerScopeDecision supportedScope ≡ consumerScopeDecision unsupportedScope → ⊥
carrierOnlyObservationDoesNotFixScopeDecision ()

------------------------------------------------------------------------
-- Promotion / attribution firewall.
------------------------------------------------------------------------

record PredictionAttributionBoundary : Set where
  constructor prediction-attribution-boundary
  field
    externalTheoryNeedsScientificAttribution : Bool
    internalTheoremNeedsProofLineageInsteadOfFakeBibliography : Bool
    authorityCarrierMatchAlonePaysClaimScope : Bool
    exactAuthorityScopeMustMatchPredictionClaim : Bool
    derivedComparisonMustBindExactConsumedInputs : Bool
    attributedPredictionAutomaticallyMatchesObservation : Bool
    predictionObservationWeldAutomaticallyMakesSourceClaim : Bool
    derivedComparisonMustRemainDASHIInference : Bool
    betterFitAutomaticallyPromotesTheory : Bool

canonicalPredictionAttributionBoundary : PredictionAttributionBoundary
canonicalPredictionAttributionBoundary =
  prediction-attribution-boundary
    true true false true true false false true false
