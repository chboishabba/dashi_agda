module DASHI.Ontology.ContextualClaimComposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import DASHI.Ontology.EpistemicTrit
  using (EpistemicTrit; unresolved; _⊗ₑ_; ⊗ₑ-idempotent;
         ⊗ₑ-commutative; ⊗ₑ-associative)

------------------------------------------------------------------------
-- Provenance-bearing, context-indexed claims.
--
-- Axis may encode time, jurisdiction, source type, language, scope, rank,
-- or any other qualifier family.  The epistemic state is never detached from
-- that scope.

record ScopedClaim (Axis : Set) : Set where
  constructor scopedClaim
  field
    stateAt : Axis → EpistemicTrit
    references : List String

open ScopedClaim public

------------------------------------------------------------------------
-- Small local list append, kept explicit so provenance composition has no
-- hidden policy.

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

------------------------------------------------------------------------
-- Composition is pointwise consensus plus provenance accumulation.

infixl 6 _⊗ᶜ_

_⊗ᶜ_ : ∀ {Axis : Set} → ScopedClaim Axis → ScopedClaim Axis → ScopedClaim Axis
x ⊗ᶜ y =
  scopedClaim
    (λ axis → stateAt x axis ⊗ₑ stateAt y axis)
    (references x ++ references y)

composition-state :
  ∀ {Axis : Set} (x y : ScopedClaim Axis) (axis : Axis) →
  stateAt (x ⊗ᶜ y) axis ≡ stateAt x axis ⊗ₑ stateAt y axis
composition-state x y axis = refl

composition-idempotent-pointwise :
  ∀ {Axis : Set} (x : ScopedClaim Axis) (axis : Axis) →
  stateAt (x ⊗ᶜ x) axis ≡ stateAt x axis
composition-idempotent-pointwise x axis =
  ⊗ₑ-idempotent (stateAt x axis)

composition-commutative-pointwise :
  ∀ {Axis : Set} (x y : ScopedClaim Axis) (axis : Axis) →
  stateAt (x ⊗ᶜ y) axis ≡ stateAt (y ⊗ᶜ x) axis
composition-commutative-pointwise x y axis =
  ⊗ₑ-commutative (stateAt x axis) (stateAt y axis)

composition-associative-pointwise :
  ∀ {Axis : Set} (x y z : ScopedClaim Axis) (axis : Axis) →
  stateAt ((x ⊗ᶜ y) ⊗ᶜ z) axis ≡ stateAt (x ⊗ᶜ (y ⊗ᶜ z)) axis
composition-associative-pointwise x y z axis =
  ⊗ₑ-associative (stateAt x axis) (stateAt y axis) (stateAt z axis)

------------------------------------------------------------------------
-- Axis extension.
--
-- When the current ontology cannot resolve a claim, add a new qualifier axis
-- instead of forcing a Boolean decision.  Existing coordinates are embedded
-- without change; new coordinates start unresolved unless explicitly supplied.

extendAxis :
  ∀ {Axis Extra : Set} →
  ScopedClaim Axis →
  (Extra → EpistemicTrit) →
  ScopedClaim (Axis ⊎ Extra)
extendAxis {Axis} {Extra} claim extraState =
  scopedClaim extended (references claim)
  where
    extended : Axis ⊎ Extra → EpistemicTrit
    extended (inj₁ axis) = stateAt claim axis
    extended (inj₂ extra) = extraState extra

extendAxisUnresolved :
  ∀ {Axis Extra : Set} →
  ScopedClaim Axis →
  ScopedClaim (Axis ⊎ Extra)
extendAxisUnresolved claim =
  extendAxis claim (λ _ → unresolved)

oldAxisPreserved :
  ∀ {Axis Extra : Set} (claim : ScopedClaim Axis) (axis : Axis) →
  stateAt (extendAxisUnresolved {Extra = Extra} claim) (inj₁ axis)
  ≡ stateAt claim axis
oldAxisPreserved claim axis = refl

newAxisStartsUnresolved :
  ∀ {Axis Extra : Set} (claim : ScopedClaim Axis) (extra : Extra) →
  stateAt (extendAxisUnresolved claim) (inj₂ extra) ≡ unresolved
newAxisStartsUnresolved claim extra = refl
