module DASHI.Physics.GR.GravitationalPredictionAttributionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred
import DASHI.Physics.GR.GravitationalEpistemicLineageExact as Lineage

------------------------------------------------------------------------
-- ATTRIBUTED PREDICTION <-> OBSERVATION
--
-- Prediction provenance is carrier-sensitive.  An externally imported theory
-- model carries scientific attribution; an internal formal theorem carries
-- repository proof lineage.  Neither is silently coerced into the other.
------------------------------------------------------------------------

data PredictionAuthority : Set where
  externalTheoryAuthority : Lineage.ExternalTheoryAttributedSource → PredictionAuthority
  internalTheoremAuthority : Lineage.InternalTheoremProofLineage → PredictionAuthority

predictionAuthorityCarrier : PredictionAuthority → String
predictionAuthorityCarrier (externalTheoryAuthority source) =
  Lineage.stableIdentifier source
predictionAuthorityCarrier (internalTheoremAuthority theorem) =
  Lineage.modulePath theorem

record AttributedGravitationalPrediction : Set where
  constructor attributed-gravitational-prediction
  field
    prediction : Pred.GravitationalPredictionReceipt
    authority : PredictionAuthority
    authorityCarrierMatchesPrediction :
      predictionAuthorityCarrier authority ≡ Pred.theoryCarrier prediction
    attributionScope : String

open AttributedGravitationalPrediction public

record AttributedPredictionObservationComparison : Set where
  constructor attributed-prediction-observation-comparison
  field
    attributedPrediction : AttributedGravitationalPrediction
    observation : Obs.GravitationalObservationReceipt
    weld :
      Pred.PredictionObservationWeld
        (prediction attributedPrediction)
        observation
    derivedComparisonLineage : Lineage.DASHIDerivedComparisonLineage

open AttributedPredictionObservationComparison public

------------------------------------------------------------------------
-- Promotion / attribution firewall.
------------------------------------------------------------------------

record PredictionAttributionBoundary : Set where
  constructor prediction-attribution-boundary
  field
    externalTheoryNeedsScientificAttribution : Bool
    internalTheoremNeedsProofLineageInsteadOfFakeBibliography : Bool
    attributedPredictionAutomaticallyMatchesObservation : Bool
    predictionObservationWeldAutomaticallyMakesSourceClaim : Bool
    derivedComparisonMustRemainDASHIInference : Bool
    betterFitAutomaticallyPromotesTheory : Bool

canonicalPredictionAttributionBoundary : PredictionAttributionBoundary
canonicalPredictionAttributionBoundary =
  prediction-attribution-boundary true true false false true false
