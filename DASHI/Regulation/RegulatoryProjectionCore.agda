module DASHI.Regulation.RegulatoryProjectionCore where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

infix 4 _≢_
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

data ComparisonResult : Set where
  agrees              : ComparisonResult
  leftAddsObligation  : ComparisonResult
  rightAddsObligation : ComparisonResult
  incompatible        : ComparisonResult
  unresolved          : ComparisonResult

data Compatibility : Set where
  compatible : Compatibility
  blocks     : Compatibility
  supersedes : Compatibility
  requires   : Compatibility
  unknown    : Compatibility

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
    projectionReading : String

  Fibre : ObservableSurface → Set
  Fibre o = Σ HiddenActivity λ h → project h ≡ o

  Section : Set
  Section = Σ (ObservableSurface → HiddenActivity)
              λ recover → (o : ObservableSurface) → project (recover o) ≡ o

  NoSection : Set
  NoSection = Section → ⊥

  FibreAmbiguity : Set
  FibreAmbiguity = Σ HiddenActivity λ x →
                   Σ HiddenActivity λ y →
                     Σ (x ≢ y) λ _ → project x ≡ project y
open RegulatoryProjection public

record CrossJurisdictionComparison (L R : RegulatoryProjection) : Set₁ where
  field
    compareSurface : ObservableSurface L → ObservableSurface R → ComparisonResult
    compareObligation : Obligation L → Obligation R → Compatibility
    comparisonReading : String
open CrossJurisdictionComparison public

record RegulatoryResidual
  (L R : RegulatoryProjection)
  (C : CrossJurisdictionComparison L R) : Set₁ where
  field
    LeftResidual  : Set
    RightResidual : Set
    leftResidual  : ObservableSurface L → ObservableSurface R → List LeftResidual
    rightResidual : ObservableSurface L → ObservableSurface R → List RightResidual
    agreementLeftEmpty :
      (l : ObservableSurface L) → (r : ObservableSurface R) →
      compareSurface C l r ≡ agrees → leftResidual l r ≡ []
    agreementRightEmpty :
      (l : ObservableSurface L) → (r : ObservableSurface R) →
      compareSurface C l r ≡ agrees → rightResidual l r ≡ []
    residualReading : String
open RegulatoryResidual public

record RegulatoryConflictGraph : Set₁ where
  field
    Node : Set
    relation : Node → Node → Compatibility
    graphReading : String

  record Conflict (x y : Node) : Set where
    constructor conflict
    field
      blocksProof : relation x y ≡ blocks
open RegulatoryConflictGraph public

record ComplianceEvidence (P : RegulatoryProjection) : Set₁ where
  field
    Candidate : Set
    Receipt   : Set
    Verifier  : Set
    candidateSurface : Candidate → ObservableSurface P
    receiptSupports  : Receipt → Candidate → Set
    verifierAccepts  : Verifier → Receipt → Set
    promotionReading : String

  record Promoted (candidate : Candidate) : Set where
    constructor promoted-by
    field
      receipt       : Receipt
      verifier      : Verifier
      supportProof  : receiptSupports receipt candidate
      verifierProof : verifierAccepts verifier receipt

  promote :
    (candidate : Candidate) →
    (receipt : Receipt) →
    (verifier : Verifier) →
    receiptSupports receipt candidate →
    verifierAccepts verifier receipt →
    Promoted candidate
  promote candidate receipt verifier support accepted =
    promoted-by receipt verifier support accepted
open ComplianceEvidence public

record RegulatoryGuardBundle (P : RegulatoryProjection) : Set₁ where
  field
    noGlobalReconstruction : NoSection P
    noAutomaticPromotion :
      (E : ComplianceEvidence P) →
      (candidate : Candidate E) →
      Promoted E candidate →
      Σ (Receipt E) λ receipt →
      Σ (Verifier E) λ verifier →
        Σ (receiptSupports E receipt candidate) λ _ →
          verifierAccepts E verifier receipt
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
  ; projectionReading = "Canonical authority-indexed regulatory projection."
  }

canonicalComparison :
  CrossJurisdictionComparison canonicalRegulatoryProjection canonicalRegulatoryProjection
canonicalComparison = record
  { compareSurface = λ _ _ → agrees
  ; compareObligation = λ _ _ → compatible
  ; comparisonReading = "Canonical comparison: identical trivial surfaces agree."
  }

canonicalProjectionAgrees : compareSurface canonicalComparison tt tt ≡ agrees
canonicalProjectionAgrees = refl
