module DASHI.Regulation.RegulatoryAuthorityBundle where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Regulation.RegulatoryProjectionCore

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

record AuthorityBundle : Set₁ where
  field
    SharedActivity : Set
    AuthorityIndex : Set
    projectionAt : AuthorityIndex → RegulatoryProjection
    embedActivity :
      (i : AuthorityIndex) →
      SharedActivity → HiddenActivity (projectionAt i)
    bundleReading : String
open AuthorityBundle public

TaggedObligation : (B : AuthorityBundle) → Set
TaggedObligation B =
  Σ (AuthorityIndex B) λ i → Obligation (projectionAt B i)

collectObligations :
  (B : AuthorityBundle) →
  (i : AuthorityIndex B) →
  SharedActivity B →
  List (TaggedObligation B)
collectObligations B i activity =
  map (λ obligation → i , obligation)
      (obligations (projectionAt B i)
        (project (projectionAt B i) (embedActivity B i activity)))

record EffectiveObligationSurface (B : AuthorityBundle) : Set₁ where
  field
    normalize : TaggedObligation B → TaggedObligation B
    normalizationStable :
      (o : TaggedObligation B) → normalize (normalize o) ≡ normalize o
    effectiveReading : String

  collect :
    (i : AuthorityIndex B) →
    SharedActivity B →
    List (TaggedObligation B)
  collect i activity = map normalize (collectObligations B i activity)
open EffectiveObligationSurface public

record ObligationRelation
  (B : AuthorityBundle)
  (E : EffectiveObligationSurface B) : Set₁ where
  field
    relation : TaggedObligation B → TaggedObligation B → Compatibility
    relationReading : String
open ObligationRelation public

record ConflictWitness
  (B : AuthorityBundle)
  (E : EffectiveObligationSurface B)
  (R : ObligationRelation B E) : Set₁ where
  field
    leftObligation  : TaggedObligation B
    rightObligation : TaggedObligation B
    conflictProof : relation R leftObligation rightObligation ≡ blocks
    conflictReading : String
open ConflictWitness public

record RegulatoryPressure
  (B : AuthorityBundle)
  (E : EffectiveObligationSurface B) : Set₁ where
  field
    Cost : Set
    zeroCost : Cost
    combine  : Cost → Cost → Cost
    obligationCost : TaggedObligation B → Cost
    pressureReading : String
open RegulatoryPressure public

record NatRegulatoryPressure
  (B : AuthorityBundle)
  (E : EffectiveObligationSurface B) : Set₁ where
  field
    costOf : TaggedObligation B → Nat

  totalCost : List (TaggedObligation B) → Nat
  totalCost []       = zero
  totalCost (x ∷ xs) = costOf x + totalCost xs
open NatRegulatoryPressure public

record RegulatoryTheoryBundle : Set₁ where
  field
    authorities : AuthorityBundle
    obligations : EffectiveObligationSurface authorities
    obligationRelation : ObligationRelation authorities obligations
    conflictGraph : RegulatoryConflictGraph
    guardsAt :
      (i : AuthorityIndex authorities) →
      RegulatoryGuardBundle (projectionAt authorities i)
    theoryReading : String
open RegulatoryTheoryBundle public

canonicalAuthorityBundle : AuthorityBundle
canonicalAuthorityBundle = record
  { SharedActivity = ⊤
  ; AuthorityIndex = ⊤
  ; projectionAt = λ _ → canonicalRegulatoryProjection
  ; embedActivity = λ _ activity → activity
  ; bundleReading = "Canonical one-authority bundle."
  }

canonicalEffectiveSurface :
  EffectiveObligationSurface canonicalAuthorityBundle
canonicalEffectiveSurface = record
  { normalize = λ x → x
  ; normalizationStable = λ _ → Agda.Builtin.Equality.refl
  ; effectiveReading = "Canonical derived effective obligation surface."
  }
