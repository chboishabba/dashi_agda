module DASHI.Biology.Cannabis.CannabisTerpeneFormalism where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Biology.Cannabis.TerpeneClusterPromotionBoundary
open import DASHI.Biology.Cannabis.TerpeneClusteringStudyReceipt
open import DASHI.Biology.Cannabis.TerpeneCommentInterpretation

-- DASHI reading:
--
-- hidden biological carrier
--   -> measured chemical projection
--   -> finite cluster observable
--   -> optional association relation
--
-- Each arrow narrows a fibre.  None recovers the hidden carrier or creates a
-- therapeutic effect without a separately witnessed bridge.
record TerpeneProjectionSystem
  (Carrier Sample Terpene Effect : Set) : Set₁ where
  field
    sampleFromCarrier : Carrier → Sample
    chemical          : ChemicalClusterReceipt Sample Terpene
    possibleEffect    : Sample → Effect → Set

-- Traditional labels and chemical clusters are two observables over samples,
-- not definitionally interchangeable coordinates.
record DualObservableSurface
  (Sample Terpene : Set) : Set₁ where
  field
    chemical : ChemicalClusterReceipt Sample Terpene
    labels   : LabelObservation Sample

-- A bridge is promoted only by carrying its own justification inhabitant.
record JustifiedBridge (A B : Set) : Set₁ where
  field
    bridge        : A → B
    bridgeLaw     : Set
    bridgeWitness : bridgeLaw

record FullTerpeneDASHIBundle
  (Carrier Source Cohort Sample Terpene Coordinate Preprocessing Method
   SelectionCriterion StabilityEvidence Effect Dose Route Context Comparator
   Outcome Protocol Exposure Study Population Endpoint Harm Uncertainty
   Recommendation : Set) : Set₁ where
  field
    studyReceipt : TerpeneClusteringStudyReceipt Source Cohort Sample Terpene
      Coordinate Preprocessing Method SelectionCriterion StabilityEvidence

    observationSurface : DualObservableSurface Sample Terpene

    stagedEvidence : ClusterEffectEvidence Sample Terpene Effect Dose Route
      Context Comparator Outcome Protocol Exposure Study Population Endpoint
      Harm Uncertainty Recommendation

    discussionBoundary : TerpeneDiscussionBoundary

-- Structural status is computed from the evidence constructor rather than a
-- free Boolean supplied by the caller.
bundleStatus :
  {Carrier Source Cohort Sample Terpene Coordinate Preprocessing Method
   SelectionCriterion StabilityEvidence Effect Dose Route Context Comparator
   Outcome Protocol Exposure Study Population Endpoint Harm Uncertainty
   Recommendation : Set} →
  FullTerpeneDASHIBundle Carrier Source Cohort Sample Terpene Coordinate
    Preprocessing Method SelectionCriterion StabilityEvidence Effect Dose Route
    Context Comparator Outcome Protocol Exposure Study Population Endpoint Harm
    Uncertainty Recommendation →
  PromotionStatus
bundleStatus bundle =
  status (FullTerpeneDASHIBundle.stagedEvidence bundle)

-- No theorem in this bundle identifies:
--   label = cluster
--   cluster = effect
--   association = cause
--   one causal study = replicated result
--   replicated result = clinical recommendation
-- Those transports require the corresponding JustifiedBridge or higher-stage
-- receipt and therefore remain fail-closed by construction.
