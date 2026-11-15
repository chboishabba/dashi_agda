module DASHI.Cognition.Teleodynamics.GeometricLearnerPriorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC GEOMETRIC LEARNER PRIOR
--
-- A geometric prior is deliberately decomposed into independent surfaces.
-- Supplying a codebook/root family does not supply a group action, equivariance,
-- a representation intertwiner, semantic realization, or physical ontology.
------------------------------------------------------------------------

record GeometricLearnerPrior : Set where
  constructor geometricLearnerPrior
  field
    priorLabel : String
    latentCarrierLabel : String
    projectionLabel : String
    codebookLabel : String
    comparisonGeometryLabel : String
    quantizerLabel : String
    attentionPerturbationLabel : String
    observerLabel : String
    provenanceLabel : String
    quantizerActive : Bool
    attentionPerturbationActive : Bool
    regularizerActive : Bool
    observerActive : Bool

open GeometricLearnerPrior public

record GeometricPriorBoundary : Set where
  constructor geometricPriorBoundary
  field
    finiteCodebookEstablished : Bool
    groupActionEstablished : Bool
    groupEquivarianceEstablished : Bool
    weylInvarianceEstablished : Bool
    representationIntertwinerEstablished : Bool
    semanticOntologySelected : Bool
    physicalMechanismEstablished : Bool

open GeometricPriorBoundary public

canonicalGeometricPriorBoundary : GeometricPriorBoundary
canonicalGeometricPriorBoundary =
  geometricPriorBoundary true false false false false false false

data PriorAblation : Set where
  disableAttentionBias : PriorAblation
  disableQuantizer : PriorAblation
  disableRegularizer : PriorAblation
  disableObserver : PriorAblation

-- This type is intentionally four-way: the inspected E8 head-scale ablation is
-- only `disableAttentionBias`, not a full removal of geometric structure.
record PriorAblationReceipt : Set where
  constructor priorAblationReceipt
  field
    ablation : PriorAblation
    otherPriorMechanismsRemainPossible : Bool

canonicalHeadScaleAblation : PriorAblationReceipt
canonicalHeadScaleAblation =
  priorAblationReceipt disableAttentionBias true
