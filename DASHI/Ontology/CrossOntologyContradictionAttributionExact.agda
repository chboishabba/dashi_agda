module DASHI.Ontology.CrossOntologyContradictionAttributionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Algebra.TetralemmaBridge as Tetralemma
import DASHI.Interop.WikidataDerivationFibreBridge as Fibre
import DASHI.Interop.WikidataDerivationSupportSquareExact as Square
import DASHI.Ontology.EpistemicTrit as Trit

------------------------------------------------------------------------
-- Cross-ontology contradiction attribution.
--
-- A surfaced structural problem is not assigned one untyped "origin" enum.
-- Instead, one ClaimBase carries provenance-bearing derivations from four
-- explicit layers.  Their support/refutation evidence remains separately
-- inspectable and may be pooled on the existing support-square carrier.
------------------------------------------------------------------------

data AttributionLayer : Set where
  sourceOntologyLayer : AttributionLayer
  transcriptionLayer : AttributionLayer
  alignmentLayer : AttributionLayer
  targetGraphLayer : AttributionLayer

layerLabel : AttributionLayer → String
layerLabel sourceOntologyLayer = "source ontology"
layerLabel transcriptionLayer = "source-to-concrete transcription"
layerLabel alignmentLayer = "cross-ontology alignment"
layerLabel targetGraphLayer = "target graph"

layerAxis : AttributionLayer → Fibre.OntologyAxis
layerAxis sourceOntologyLayer = Fibre.externalAxis "source-ontology"
layerAxis transcriptionLayer = Fibre.externalAxis "transcription"
layerAxis alignmentLayer = Fibre.externalAxis "alignment"
layerAxis targetGraphLayer = Fibre.externalAxis "target-graph"

record AttributedDerivation (claim : Fibre.ClaimBase) : Set where
  constructor attributedDerivation
  field
    layer : AttributionLayer
    derivation : Fibre.Derivation claim
    usesLayer : Fibre._∈_ (layerAxis layer) (Fibre.derivationAxes derivation)

open AttributedDerivation public

mkAttributedDerivation :
  (claim : Fibre.ClaimBase) →
  AttributionLayer →
  Fibre.DerivationPolarity →
  String →
  String →
  AttributedDerivation claim
mkAttributedDerivation claim layerValue polarity evidence provenance =
  attributedDerivation
    layerValue
    (Fibre.derivation
      (layerLabel layerValue)
      polarity
      (layerAxis layerValue ∷ [])
      evidence
      provenance
      [])
    Fibre.here

attributedSquare :
  ∀ {claim} → AttributedDerivation claim → Four.PolarAssessment
attributedSquare evidence =
  Square.squareFromPolarity (Fibre.derivationPolarity (derivation evidence))

record AttributedDerivationFibre (claim : Fibre.ClaimBase) : Set where
  constructor attributedDerivationFibre
  field
    sourceEvidence : AttributedDerivation claim
    transcriptionEvidence : AttributedDerivation claim
    alignmentEvidence : AttributedDerivation claim
    targetEvidence : AttributedDerivation claim

open AttributedDerivationFibre public

pooledAttributionSquare :
  ∀ {claim} → AttributedDerivationFibre claim → Four.PolarAssessment
pooledAttributionSquare fibre =
  Square.mergeSquare
    (attributedSquare (sourceEvidence fibre))
    (Square.mergeSquare
      (attributedSquare (transcriptionEvidence fibre))
      (Square.mergeSquare
        (attributedSquare (alignmentEvidence fibre))
        (attributedSquare (targetEvidence fibre))))

pooledAttributionTrit :
  ∀ {claim} → AttributedDerivationFibre claim → Trit.EpistemicTrit
pooledAttributionTrit fibre = Square.collapseSquare (pooledAttributionSquare fibre)

------------------------------------------------------------------------
-- Concrete layer-local countermodel.
--
-- Source, transcription and target each support the same scoped proposition,
-- while the alignment layer carries a refuting derivation.  Pooling therefore
-- yields the top/conflict corner rather than erasing which layer disagreed.
------------------------------------------------------------------------

alignmentStressClaim : Fibre.ClaimBase
alignmentStressClaim =
  Fibre.claimBase
    "cross-ontology:alignment-local-stress"
    "the mapped structural relation is preserved across the declared alignment"
    (Fibre.externalClaimKind "cross-ontology alignment")
    Fibre.candidateLinkRole
    "fixture:alignment-local-stress:v1"

alignmentLocalStressFibre : AttributedDerivationFibre alignmentStressClaim
alignmentLocalStressFibre =
  attributedDerivationFibre
    (mkAttributedDerivation alignmentStressClaim sourceOntologyLayer Fibre.supporting
      "source ontology supports the scoped relation"
      "source:fixture:v1")
    (mkAttributedDerivation alignmentStressClaim transcriptionLayer Fibre.supporting
      "concrete transcription preserves the scoped source facts"
      "transcription:fixture:v1")
    (mkAttributedDerivation alignmentStressClaim alignmentLayer Fibre.contradicting
      "the declared alignment fails the scoped transport obligation"
      "alignment:fixture:bad-link:v1")
    (mkAttributedDerivation alignmentStressClaim targetGraphLayer Fibre.supporting
      "target graph independently supports the target-side relation"
      "target:fixture:v1")

sourceLayerSupports :
  Square.squareOutcome
    (attributedSquare (sourceEvidence alignmentLocalStressFibre))
  ≡ Fibre.satisfied
sourceLayerSupports = refl

transcriptionLayerSupports :
  Square.squareOutcome
    (attributedSquare (transcriptionEvidence alignmentLocalStressFibre))
  ≡ Fibre.satisfied
transcriptionLayerSupports = refl

alignmentLayerRefutes :
  Square.squareOutcome
    (attributedSquare (alignmentEvidence alignmentLocalStressFibre))
  ≡ Fibre.violated
alignmentLayerRefutes = refl

targetLayerSupports :
  Square.squareOutcome
    (attributedSquare (targetEvidence alignmentLocalStressFibre))
  ≡ Fibre.satisfied
targetLayerSupports = refl

alignmentLocalStressPoolsToConflict :
  pooledAttributionSquare alignmentLocalStressFibre ≡ Four.assess true true
alignmentLocalStressPoolsToConflict = refl

alignmentLocalStressPositionIsBoth :
  Four.polarPosition (pooledAttributionSquare alignmentLocalStressFibre)
  ≡ Tetralemma.both
alignmentLocalStressPositionIsBoth = refl

alignmentLocalStressTritIsLossyUnresolved :
  pooledAttributionTrit alignmentLocalStressFibre ≡ Trit.unresolved
alignmentLocalStressTritIsLossyUnresolved = refl

------------------------------------------------------------------------
-- Missing evidence is not refutation.
------------------------------------------------------------------------

missingLayerSquare : Four.PolarAssessment
missingLayerSquare = Square.squareFromPolarity Fibre.unresolved

missingLayerIsNeither :
  Four.polarPosition missingLayerSquare ≡ Tetralemma.neither
missingLayerIsNeither = refl

missingLayerOutcomeUndetermined :
  Square.squareOutcome missingLayerSquare ≡ Fibre.undetermined
missingLayerOutcomeUndetermined = refl
