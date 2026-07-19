module DASHI.Ontology.EpistemicTrit where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- A claim state is epistemic, not a Boolean truth value.
--
-- supported     : the available evidence supports the scoped claim
-- unresolved    : evidence is absent, incomplete, or conflicting
-- contradicted  : the available evidence contradicts the scoped claim

data EpistemicTrit : Set where
  contradicted unresolved supported : EpistemicTrit

------------------------------------------------------------------------
-- Consensus composition.
--
-- Equal determinate evidence remains determinate.  Every disagreement, and
-- every composition involving an unresolved input, remains unresolved.
-- Consequently composition cannot manufacture certainty.

infixl 6 _⊗ₑ_

_⊗ₑ_ : EpistemicTrit → EpistemicTrit → EpistemicTrit
contradicted ⊗ₑ contradicted = contradicted
supported    ⊗ₑ supported    = supported
_            ⊗ₑ _            = unresolved

⊗ₑ-idempotent : ∀ x → x ⊗ₑ x ≡ x
⊗ₑ-idempotent contradicted = refl
⊗ₑ-idempotent unresolved = refl
⊗ₑ-idempotent supported = refl

⊗ₑ-commutative : ∀ x y → x ⊗ₑ y ≡ y ⊗ₑ x
⊗ₑ-commutative contradicted contradicted = refl
⊗ₑ-commutative contradicted unresolved = refl
⊗ₑ-commutative contradicted supported = refl
⊗ₑ-commutative unresolved contradicted = refl
⊗ₑ-commutative unresolved unresolved = refl
⊗ₑ-commutative unresolved supported = refl
⊗ₑ-commutative supported contradicted = refl
⊗ₑ-commutative supported unresolved = refl
⊗ₑ-commutative supported supported = refl

⊗ₑ-associative : ∀ x y z → (x ⊗ₑ y) ⊗ₑ z ≡ x ⊗ₑ (y ⊗ₑ z)
⊗ₑ-associative contradicted contradicted contradicted = refl
⊗ₑ-associative contradicted contradicted unresolved = refl
⊗ₑ-associative contradicted contradicted supported = refl
⊗ₑ-associative contradicted unresolved contradicted = refl
⊗ₑ-associative contradicted unresolved unresolved = refl
⊗ₑ-associative contradicted unresolved supported = refl
⊗ₑ-associative contradicted supported contradicted = refl
⊗ₑ-associative contradicted supported unresolved = refl
⊗ₑ-associative contradicted supported supported = refl
⊗ₑ-associative unresolved contradicted contradicted = refl
⊗ₑ-associative unresolved contradicted unresolved = refl
⊗ₑ-associative unresolved contradicted supported = refl
⊗ₑ-associative unresolved unresolved contradicted = refl
⊗ₑ-associative unresolved unresolved unresolved = refl
⊗ₑ-associative unresolved unresolved supported = refl
⊗ₑ-associative unresolved supported contradicted = refl
⊗ₑ-associative unresolved supported unresolved = refl
⊗ₑ-associative unresolved supported supported = refl
⊗ₑ-associative supported contradicted contradicted = refl
⊗ₑ-associative supported contradicted unresolved = refl
⊗ₑ-associative supported contradicted supported = refl
⊗ₑ-associative supported unresolved contradicted = refl
⊗ₑ-associative supported unresolved unresolved = refl
⊗ₑ-associative supported unresolved supported = refl
⊗ₑ-associative supported supported contradicted = refl
⊗ₑ-associative supported supported unresolved = refl
⊗ₑ-associative supported supported supported = refl

unresolved-left-absorbing : ∀ x → unresolved ⊗ₑ x ≡ unresolved
unresolved-left-absorbing contradicted = refl
unresolved-left-absorbing unresolved = refl
unresolved-left-absorbing supported = refl

unresolved-right-absorbing : ∀ x → x ⊗ₑ unresolved ≡ unresolved
unresolved-right-absorbing contradicted = refl
unresolved-right-absorbing unresolved = refl
unresolved-right-absorbing supported = refl

disagreement-is-unresolved :
  contradicted ⊗ₑ supported ≡ unresolved
disagreement-is-unresolved = refl

------------------------------------------------------------------------
-- Binary forcing is necessarily information-losing.
-- These two common policies collapse unresolved into one determinate branch.

data BinaryDecision : Set where
  reject accept : BinaryDecision

forceUnresolvedToAccept : EpistemicTrit → BinaryDecision
forceUnresolvedToAccept contradicted = reject
forceUnresolvedToAccept unresolved = accept
forceUnresolvedToAccept supported = accept

forceUnresolvedToReject : EpistemicTrit → BinaryDecision
forceUnresolvedToReject contradicted = reject
forceUnresolvedToReject unresolved = reject
forceUnresolvedToReject supported = accept

acceptPolicyCollision :
  forceUnresolvedToAccept unresolved ≡
  forceUnresolvedToAccept supported
acceptPolicyCollision = refl

rejectPolicyCollision :
  forceUnresolvedToReject unresolved ≡
  forceUnresolvedToReject contradicted
rejectPolicyCollision = refl

------------------------------------------------------------------------
-- Decidable equality is useful for executable conformance tests.

equal? : EpistemicTrit → EpistemicTrit → Bool
equal? contradicted contradicted = true
equal? unresolved unresolved = true
equal? supported supported = true
equal? _ _ = false
