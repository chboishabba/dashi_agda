module DASHI.Biology.TraumaPsychogeographicMetricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.PsychogeographicMemoryHyperfabricExact as MemoryFabric
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric

------------------------------------------------------------------------
-- Source calibration.
--
-- Chris R. Brewin, Tim Dalgleish and Stephen Joseph,
-- "A Dual Representation Theory of Posttraumatic Stress Disorder",
-- Psychological Review 103(4), 1996, DOI 10.1037/0033-295X.103.4.670.
-- Pierre Nora, "Between Memory and History: Les Lieux de Memoire",
-- Representations 26, 1989, DOI 10.2307/2928520.
--
-- Only a finite structural distinction among physical distance,
-- psychogeographic distance, retrieval, action and integration residuals is
-- imported.  No diagnosis, prevalence claim or clinical treatment theorem is
-- derived.
------------------------------------------------------------------------

data SiteRelation : Set where
  nearbyBlockedRelation : SiteRelation
  remotePastImmediateRelation : SiteRelation
  ordinaryAlignedRelation : SiteRelation

physicalDistance : SiteRelation → Nat
physicalDistance nearbyBlockedRelation = 1
physicalDistance remotePastImmediateRelation = 9
physicalDistance ordinaryAlignedRelation = 3

psychogeographicDistance : SiteRelation → Nat
psychogeographicDistance nearbyBlockedRelation = 9
psychogeographicDistance remotePastImmediateRelation = 0
psychogeographicDistance ordinaryAlignedRelation = 3

nearbyCanBePsychogeographicallyDistant :
  physicalDistance nearbyBlockedRelation ≡ 1
  × psychogeographicDistance nearbyBlockedRelation ≡ 9
nearbyCanBePsychogeographicallyDistant = refl , refl

remotePastCanBePsychogeographicallyImmediate :
  physicalDistance remotePastImmediateRelation ≡ 9
  × psychogeographicDistance remotePastImmediateRelation ≡ 0
remotePastCanBePsychogeographicallyImmediate = refl , refl

physicalAndPsychogeographicMetricsNeedNotAgree :
  ¬ (physicalDistance nearbyBlockedRelation
     ≡ psychogeographicDistance nearbyBlockedRelation)
physicalAndPsychogeographicMetricsNeedNotAgree ()

record TraumaResidualVector : Set where
  constructor traumaResidualVector
  field
    retrievalResidual : Nat
    valuationResidual : Nat
    actionResidual : Nat
    integrationResidual : Nat

open TraumaResidualVector public

record TraumaPathObstruction : Set where
  constructor traumaPathObstruction
  field
    spatialSupport : String
    temporalSupport : String
    relationalSupport : String
    residualVector : TraumaResidualVector
    provenance : List String
    obstructionReceipt : String

open TraumaPathObstruction public

canonicalTraumaPathObstruction : TraumaPathObstruction
canonicalTraumaPathObstruction =
  traumaPathObstruction
    "institutional threshold"
    "past event reactivated in present"
    "authority/body/place relation"
    (traumaResidualVector 7 5 8 6)
    ("event provenance retained" ∷ "route history retained" ∷ [])
    "finite path-conditioned obstruction witness"

canonicalResidualComponentsRemainDistinct :
  actionResidual (residualVector canonicalTraumaPathObstruction) ≡ 8
  × integrationResidual (residualVector canonicalTraumaPathObstruction) ≡ 6
canonicalResidualComponentsRemainDistinct = refl , refl

------------------------------------------------------------------------
-- The same residual vector is also embedded in the repository's generic
-- proof-bearing obstruction carrier.
------------------------------------------------------------------------

typedTraumaObstruction :
  Hyperfabric.HyperfabricObstruction
    {Residual = TraumaResidualVector}
    (MemoryFabric.psychogeographicHyperfabric ⊤)
typedTraumaObstruction = record
  { Hyperfabric.obstructedEdge = MemoryFabric.placeMemoryEdge
  ; Hyperfabric.residual = residualVector canonicalTraumaPathObstruction
  ; Hyperfabric.obstructionProvenance =
      "event provenance retained" ∷ "route history retained" ∷ []
  ; Hyperfabric.obstructionReceipt =
      "typed psychogeographic obstruction; no diagnostic promotion"
  }

typedObstructionUsesPlaceMemoryEdge :
  Hyperfabric.obstructedEdge typedTraumaObstruction
  ≡ MemoryFabric.placeMemoryEdge
typedObstructionUsesPlaceMemoryEdge = refl

record TraumaPsychogeographicBoundary : Set where
  constructor traumaPsychogeographicBoundary
  field
    highSalienceAloneDefinesTrauma : Bool
    highSalienceAloneDefinesTraumaIsFalse :
      highSalienceAloneDefinesTrauma ≡ false
    obstructionDiagnosesPerson : Bool
    obstructionDiagnosesPersonIsFalse : obstructionDiagnosesPerson ≡ false
    physicalDistanceDeterminesLivedAccessibility : Bool
    physicalDistanceDeterminesLivedAccessibilityIsFalse :
      physicalDistanceDeterminesLivedAccessibility ≡ false
    structuralResidualIsClinicalTreatmentAdvice : Bool
    structuralResidualIsClinicalTreatmentAdviceIsFalse :
      structuralResidualIsClinicalTreatmentAdvice ≡ false

canonicalTraumaPsychogeographicBoundary : TraumaPsychogeographicBoundary
canonicalTraumaPsychogeographicBoundary =
  traumaPsychogeographicBoundary false refl false refl false refl false refl
