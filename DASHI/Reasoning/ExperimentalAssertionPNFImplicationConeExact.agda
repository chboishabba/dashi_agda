module DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design

------------------------------------------------------------------------
-- EXPERIMENTAL ASSERTION -> PNF -> DESIGN LOCATION -> IMPLICATION CONE
--
-- Natural-language extraction, logical normalisation, experimental placement
-- and downstream implication are distinct proof obligations. This owner does
-- not claim to implement a general NLP parser: compilation is receipt-bearing.
------------------------------------------------------------------------

record NaturalLanguageExperimentalAssertion : Set where
  constructor naturalLanguageExperimentalAssertion
  field
    assertionKey : String
    exactText : String
    sourceLocator : String
    sourceKindReference : String
    extractionReference : String

open NaturalLanguageExperimentalAssertion public

record PNFCompilationReceipt
    (source : NaturalLanguageExperimentalAssertion) : Set₁ where
  constructor pnfCompilationReceipt
  field
    compiled : PNF.PredicateNormalAssertion
    textPreserved : PNF.naturalLanguage compiled ≡ exactText source
    quantifierReadingReference : String
    inferentialForceReadingReference : String
    predicateDecompositionReference : String
    scopeExtractionReference : String
    humanReviewReference : String

open PNFCompilationReceipt public

------------------------------------------------------------------------
-- Proof-relevant list membership. A design placement must point to an atom
-- actually present in the compiled PNF assertion, not merely repeat its label.
------------------------------------------------------------------------

infix 4 _∈_

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

------------------------------------------------------------------------
-- Each PNF atom is located in the experimental architecture. One prose claim
-- may therefore draw on several noninterchangeable design coordinates.
------------------------------------------------------------------------

data ExperimentalDesignSlot : Set where
  sourcePopulationSlot
  treatmentAssignmentSlot
  comparatorSlot
  baselineMeasurementSlot
  endpointMeasurementSlot
  timeSlot
  assaySlot
  nuisanceControlSlot
  statisticalContrastSlot
  causalIdentificationSlot
  mechanismIdentificationSlot
  transportSlot
  practicalSignificanceSlot
  : ExperimentalDesignSlot

record PredicateDesignPlacement
    (assertion : PNF.PredicateNormalAssertion) : Set where
  constructor predicateDesignPlacement
  field
    atom : PNF.PredicateAtom
    atomInAssertion : atom ∈ PNF.predicates assertion
    slot : ExperimentalDesignSlot
    obligation : PNF.AssertionObligation
    designEvidence : Design.EvidenceForObligation
    placementReference : String

open PredicateDesignPlacement public

record AssertionDesignMap
    (source : NaturalLanguageExperimentalAssertion) : Set₁ where
  constructor assertionDesignMap
  field
    compilation : PNFCompilationReceipt source
    placements : List (PredicateDesignPlacement (compiled compilation))
    designCoverageReference : String
    uncoveredObligationsReference : String

open AssertionDesignMap public

------------------------------------------------------------------------
-- Implication cone.
------------------------------------------------------------------------

data ConeEdgeStatus : Set where
  supportedEdge
  qualifiedEdge
  blockedEdge
  : ConeEdgeStatus

supportedNotBlocked : supportedEdge ≡ blockedEdge → ⊥
supportedNotBlocked ()

qualifiedNotSupported : qualifiedEdge ≡ supportedEdge → ⊥
qualifiedNotSupported ()

data ImplicationKind : Set where
  restatesMeasuredResult
  derivesBoundedContrast
  derivesResidualEnvelope
  associatesTreatmentAndOutcome
  attributesCausalEffect
  identifiesMechanism
  transportsPopulation
  recommendsPractice
  : ImplicationKind

record ImplicationNode : Set where
  constructor implicationNode
  field
    nodeKey : String
    assertion : PNF.PredicateNormalAssertion
    nodeReading : String

open ImplicationNode public

record ImplicationEdge : Set where
  constructor implicationEdge
  field
    fromNode : String
    toNode : String
    kind : ImplicationKind
    status : ConeEdgeStatus
    evidenceOrBlockReference : String
    residualReference : String

open ImplicationEdge public

record ExperimentalImplicationCone
    (source : NaturalLanguageExperimentalAssertion) : Set₁ where
  constructor experimentalImplicationCone
  field
    designMap : AssertionDesignMap source
    root : ImplicationNode
    nodes : List ImplicationNode
    edges : List ImplicationEdge
    safeConeReading : String
    blockedConeReading : String

open ExperimentalImplicationCone public

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data BlockedPromotionReceipt : Set where

blockedPromotionHasNoReceipt : BlockedPromotionReceipt → ⊥
blockedPromotionHasNoReceipt ()

record ExperimentalAssertionConeBoundary : Set where
  constructor experimentalAssertionConeBoundary
  field
    naturalLanguageEqualsPNFByDefinition : Bool
    naturalLanguageEqualsPNFByDefinitionIsFalse :
      naturalLanguageEqualsPNFByDefinition ≡ false
    placementMayNameAtomAbsentFromCompiledPNF : Bool
    placementMayNameAtomAbsentFromCompiledPNFIsFalse :
      placementMayNameAtomAbsentFromCompiledPNF ≡ false
    oneDischargedAtomClosesWholeAssertion : Bool
    oneDischargedAtomClosesWholeAssertionIsFalse :
      oneDischargedAtomClosesWholeAssertion ≡ false
    measuredResultAutomaticallyIdentifiesCausalEffect : Bool
    measuredResultAutomaticallyIdentifiesCausalEffectIsFalse :
      measuredResultAutomaticallyIdentifiesCausalEffect ≡ false
    causalEffectAutomaticallyIdentifiesMechanism : Bool
    causalEffectAutomaticallyIdentifiesMechanismIsFalse :
      causalEffectAutomaticallyIdentifiesMechanism ≡ false
    qualifiedImplicationsCanRemainUseful : Bool
    qualifiedImplicationsCanRemainUsefulIsTrue :
      qualifiedImplicationsCanRemainUseful ≡ true
    implicationConeRetainsBlockedPromotions : Bool
    implicationConeRetainsBlockedPromotionsIsTrue :
      implicationConeRetainsBlockedPromotions ≡ true

canonicalExperimentalAssertionConeBoundary : ExperimentalAssertionConeBoundary
canonicalExperimentalAssertionConeBoundary =
  experimentalAssertionConeBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
