module DASHI.Core.RelationAlgebraCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (Σ; _,_; _×_; proj₁; proj₂)

------------------------------------------------------------------------
-- Generic relation algebra surface.
--
-- This module is PM-neutral.  It exposes ordinary relation constructors and
-- keeps relation-algebra authority behind an explicit false boundary.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

Rel : Set → Set → Set₁
Rel A B =
  A → B → Set

Converse : ∀ {A B : Set} → Rel A B → Rel B A
Converse R b a =
  R a b

Domain : ∀ {A B : Set} → Rel A B → A → Set
Domain {B = B} R a =
  Σ B (λ b → R a b)

Range : ∀ {A B : Set} → Rel A B → B → Set
Range {A = A} R b =
  Σ A (λ a → R a b)

Field : ∀ {A : Set} → Rel A A → A → Set
Field R a =
  Domain R a

RelativeProduct :
  ∀ {A B C : Set} →
  Rel A B →
  Rel B C →
  Rel A C
RelativeProduct {B = B} R S a c =
  Σ B (λ b → R a b × S b c)

Restriction :
  ∀ {A B : Set} →
  (A → Set) →
  (B → Set) →
  Rel A B →
  Rel A B
Restriction PA PB R a b =
  PA a × R a b × PB b

Subrelation :
  ∀ {A B : Set} →
  Rel A B →
  Rel A B →
  Set
Subrelation R S =
  ∀ a b → R a b → S a b

converseInvolutive :
  ∀ {A B : Set} {R : Rel A B} →
  Converse (Converse R) ≡ R
converseInvolutive =
  refl

domainIsRangeOfConverse :
  ∀ {A B : Set} {R : Rel A B} →
  Domain R ≡ Range (Converse R)
domainIsRangeOfConverse =
  refl

rangeIsDomainOfConverse :
  ∀ {A B : Set} {R : Rel A B} →
  Range R ≡ Domain (Converse R)
rangeIsDomainOfConverse =
  refl

------------------------------------------------------------------------
-- Authority boundary.

data RelationAlgebraSurfaceKind : Set where
  converseSurface :
    RelationAlgebraSurfaceKind

  domainSurface :
    RelationAlgebraSurfaceKind

  rangeSurface :
    RelationAlgebraSurfaceKind

  fieldSurface :
    RelationAlgebraSurfaceKind

  relativeProductSurface :
    RelationAlgebraSurfaceKind

  restrictionSurface :
    RelationAlgebraSurfaceKind

  subrelationSurface :
    RelationAlgebraSurfaceKind

canonicalRelationAlgebraSurfaceKinds :
  List RelationAlgebraSurfaceKind
canonicalRelationAlgebraSurfaceKinds =
  converseSurface
  ∷ domainSurface
  ∷ rangeSurface
  ∷ fieldSurface
  ∷ relativeProductSurface
  ∷ restrictionSurface
  ∷ subrelationSurface
  ∷ []

canonicalRelationAlgebraSurfaceKindCount : Nat
canonicalRelationAlgebraSurfaceKindCount =
  listCount canonicalRelationAlgebraSurfaceKinds

record RelationAlgebraAuthorityBoundary : Set where
  constructor mkRelationAlgebraAuthorityBoundary
  field
    boundaryLabel :
      String

    pmRelationCalculusAuthority :
      Bool

    pmRelationCalculusAuthorityIsFalse :
      pmRelationCalculusAuthority ≡ false

    extensionalSetTheoryAuthority :
      Bool

    extensionalSetTheoryAuthorityIsFalse :
      extensionalSetTheoryAuthority ≡ false

    canonicalNotationAuthority :
      Bool

    canonicalNotationAuthorityIsFalse :
      canonicalNotationAuthority ≡ false

canonicalRelationAlgebraAuthorityBoundary :
  RelationAlgebraAuthorityBoundary
canonicalRelationAlgebraAuthorityBoundary =
  mkRelationAlgebraAuthorityBoundary
    "generic-relation-algebra-boundary"
    false
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Canonical Bool example.

BoolEqualityRel : Rel Bool Bool
BoolEqualityRel x y =
  x ≡ y

boolEqualityTrueDomain :
  Domain BoolEqualityRel true
boolEqualityTrueDomain =
  true , refl

boolEqualityTrueRange :
  Range BoolEqualityRel true
boolEqualityTrueRange =
  true , refl

boolEqualityRelativeProductTrue :
  RelativeProduct BoolEqualityRel BoolEqualityRel true true
boolEqualityRelativeProductTrue =
  true , refl , refl

boolEqualitySubrelationReflexive :
  Subrelation BoolEqualityRel BoolEqualityRel
boolEqualitySubrelationReflexive x y proof =
  proof

relationAlgebraBoundaryDoesNotPromotePM :
  RelationAlgebraAuthorityBoundary.pmRelationCalculusAuthority
    canonicalRelationAlgebraAuthorityBoundary
  ≡
  false
relationAlgebraBoundaryDoesNotPromotePM =
  refl
