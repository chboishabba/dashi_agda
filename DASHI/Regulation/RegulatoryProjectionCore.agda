module DASHI.Regulation.RegulatoryProjectionCore where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

----------------------------------------------------------------------
-- Cross-jurisdiction regulatory anatomy in DASHI terms.
--
-- A jurisdiction is an authority index, not a truth value.  The same
-- hidden activity may project to different obligation surfaces under
-- different authorities.  Comparison reports agreement, residual,
-- conflict, or unresolvedness without promoting any authority to a
-- universal law and without reconstructing hidden implementation state.
----------------------------------------------------------------------

data ComparisonResult : Set where
  agrees             : ComparisonResult
  leftAddsObligation : ComparisonResult
  rightAddsObligation : ComparisonResult
  incompatible       : ComparisonResult
  unresolved         : ComparisonResult

data Compatibility : Set where
  compatible   : Compatibility
  blocks       : Compatibility
  supersedes   : Compatibility
  requires     : Compatibility
  unknown      : Compatibility

record Jurisdiction : Set where
  field
    jurisdictionName : String
    authorityName    : String

open Jurisdiction public

record RegulatoryProjection : Set₁ where
  field
    HiddenActivity    : Set
    ObservableSurface : Set
    Obligation        : Set

    jurisdiction : Jurisdiction
    project      : HiddenActivity → ObservableSurface
    obligations  : ObservableSurface → List Obligation

    -- Governance guards: these are proof obligations, not status flags.
    authorityIsNotTruth : ⊤
    noHiddenReconstruction : ObservableSurface → Maybe HiddenActivity
    noHiddenReconstruction = λ _ → nothing

    projectionReading : String

open RegulatoryProjection public

record CrossJurisdictionComparison
  (L R : RegulatoryProjection) : Set₁ where
  field
    compareSurface :
      ObservableSurface L → ObservableSurface R → ComparisonResult

    compareObligation :
      Obligation L → Obligation R → Compatibility

    comparisonReading : String

open CrossJurisdictionComparison public

record RegulatoryResidual
  (L R : RegulatoryProjection)
  (C : CrossJurisdictionComparison L R) : Set₁ where
  field
    LeftResidual  : Set
    RightResidual : Set

    leftResidual :
      ObservableSurface L → ObservableSurface R → List LeftResidual

    rightResidual :
      ObservableSurface L → ObservableSurface R → List RightResidual

    -- A residual records non-coincidence; it is not itself a claim that
    -- either authority is false.
    residualIsNotRefutation : ⊤
    residualReading : String

open RegulatoryResidual public

record RegulatoryConflictGraph : Set₁ where
  field
    Node : Set
    relation : Node → Node → Compatibility
    graphReading : String

open RegulatoryConflictGraph public

record ComplianceEvidence (P : RegulatoryProjection) : Set₁ where
  field
    Candidate : Set
    Receipt   : Set
    Verifier  : Set

    candidateSurface : Candidate → ObservableSurface P
    receiptSupports  : Receipt → Candidate → Set
    verifierAccepts  : Verifier → Receipt → Set

    -- Promotion requires both evidence and an independent verifier.
    Promoted : Candidate → Set
    promote :
      (candidate : Candidate) →
      (receipt : Receipt) →
      (verifier : Verifier) →
      receiptSupports receipt candidate →
      verifierAccepts verifier receipt →
      Promoted candidate

    documentationIsNotCompliance : ⊤
    promotionReading : String

open ComplianceEvidence public

record RegulatoryGuardBundle : Set where
  field
    noUniversalJurisdiction : ⊤
    noAutomaticCompliance  : ⊤
    noPolicyToTruth         : ⊤
    noAIAsLegalAuthority    : ⊤
    noFibreReconstruction   : ⊤

open RegulatoryGuardBundle public

canonicalJurisdiction : Jurisdiction
canonicalJurisdiction = record
  { jurisdictionName = "Canonical jurisdiction"
  ; authorityName = "Canonical authority"
  }

canonicalRegulatoryProjection : RegulatoryProjection
canonicalRegulatoryProjection = record
  { HiddenActivity = ⊤
  ; ObservableSurface = ⊤
  ; Obligation = ⊤
  ; jurisdiction = canonicalJurisdiction
  ; project = λ _ → tt
  ; obligations = λ _ → tt ∷ []
  ; authorityIsNotTruth = tt
  ; noHiddenReconstruction = λ _ → nothing
  ; projectionReading = "Canonical regulatory projection: authority-indexed and non-reconstructive."
  }

canonicalComparison :
  CrossJurisdictionComparison
    canonicalRegulatoryProjection
    canonicalRegulatoryProjection
canonicalComparison = record
  { compareSurface = λ _ _ → agrees
  ; compareObligation = λ _ _ → compatible
  ; comparisonReading = "Canonical comparison: identical trivial surfaces agree."
  }

canonicalGuards : RegulatoryGuardBundle
canonicalGuards = record
  { noUniversalJurisdiction = tt
  ; noAutomaticCompliance = tt
  ; noPolicyToTruth = tt
  ; noAIAsLegalAuthority = tt
  ; noFibreReconstruction = tt
  }

canonicalProjectionAgrees :
  compareSurface canonicalComparison tt tt ≡ agrees
canonicalProjectionAgrees = refl
