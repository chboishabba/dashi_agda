{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechJointStateConsumerQuotientExact where

-- Constructive full-tuple consumer quotient, NOT E independent router packets.
--
-- z = (shared activation x, histories indexed by Fin E).
-- A selected-execution consumer may observe x and only the histories
-- selected by an admitted route. Nonselected histories stay at their
-- authoritative owner; the receiver reconstructs them from that owner.
--
-- Inactive consistency is the exact precondition for full-state replay.
-- A selected consumer needs only selected-input equality, whereas a
-- full-world consumer must additionally check every inactive history.
-- This follows DASHI/Core/ConsumerQuotientBaseChangeExact and
-- Reasoning/HistoryTimeIndexedConsumerFibreExact rather than
-- treating a sign-orbit fingerprint as a semantic equality.
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

sym : ∀ {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

record JointState (E : Nat) (X H : Set) : Set where
  constructor jointState
  field
    activation : X
    history : Fin E → H
open JointState public

record SelectedQuotient (E : Nat) (X H : Set)
                       (selected : Fin E → Bool) : Set where
  constructor selectedQuotient
  field
    sharedActivation : X
    selectedHistory : (e : Fin E) → selected e ≡ true → H
open SelectedQuotient public

project :
  ∀ {E : Nat} {X H : Set} →
  (selected : Fin E → Bool) → JointState E X H →
  SelectedQuotient E X H selected
project selected source =
  selectedQuotient (activation source) (λ e selectedProof → history source e)

choose : ∀ {A : Set} → Bool → A → A → A
choose true whenSelected whenInactive = whenSelected
choose false whenSelected whenInactive = whenInactive

reopen :
  ∀ {E : Nat} {X H : Set} →
  (selected : Fin E → Bool) →
  JointState E X H →
  SelectedQuotient E X H selected →
  JointState E X H
reopen {E = E} {X = X} {H = H} selected retained payload =
  jointState (sharedActivation payload)
    (λ e → reopenOne e (selected e))
  where
    reopenOne : (e : Fin E) → (flag : Bool) → H
    reopenOne e true = selectedHistory payload e refl
    reopenOne e false = history retained e

reopenSharedActivation :
  ∀ {E : Nat}{X H : Set}
  (selected : Fin E → Bool) (source retained : JointState E X H) →
  activation (reopen selected retained (project selected source))
    ≡ activation source
reopenSharedActivation selected source retained = refl

reopenSelectedHistory :
  ∀ {E : Nat}{X H : Set}
  (selected : Fin E → Bool) (source retained : JointState E X H)
  (e : Fin E) →
  selected e ≡ true →
  history (reopen selected retained (project selected source)) e
    ≡ history source e
reopenSelectedHistory selected source retained e selectedTrue
  rewrite selectedTrue = refl

reopenInactiveHistory :
  ∀ {E : Nat}{X H : Set}
  (selected : Fin E → Bool) (source retained : JointState E X H)
  (e : Fin E) →
  selected e ≡ false →
  history (reopen selected retained (project selected source)) e
    ≡ history retained e
reopenInactiveHistory selected source retained e selectedFalse
  rewrite selectedFalse = refl

-- A legitimate consumer quotient is not an arbitrary hash or signed
-- projection. The consumer supplies a verified *fibre-constancy law*.
record SelectedConsumer
    {E : Nat} {X H : Set}
    (selected : Fin E → Bool) : Set₁ where
  field
    Observation : Set
    observe : JointState E X H → Observation
    sufficient :
      (left right : JointState E X H) →
      activation left ≡ activation right →
      ((e : Fin E) → selected e ≡ true →
         history left e ≡ history right e) →
      observe left ≡ observe right
open SelectedConsumer public

selectedExecutionConsumerExactlyPreserved :
  ∀ {E : Nat}{X H : Set}
  (selected : Fin E → Bool)
  (consumer : SelectedConsumer {E} {X} {H} selected)
  (source retained : JointState E X H) →
  observe consumer
    (reopen selected retained (project selected source))
    ≡ observe consumer source
selectedExecutionConsumerExactlyPreserved selected consumer source retained =
  sufficient consumer
    (reopen selected retained (project selected source))
    source
    (reopenSharedActivation selected source retained)
    (reopenSelectedHistory selected source retained)

-- If a *full-state* consumer needs all E histories, the inactive
-- equality is an independent necessary receipt. A prior peer snapshot
-- that contains different inactive histories cannot be silently merged.
fullHistoryReopenPointwise :
  ∀ {E : Nat}{X H : Set}
  (selected : Fin E → Bool)
  (source retained : JointState E X H) →
  ((e : Fin E) → selected e ≡ false →
    history retained e ≡ history source e) →
  (e : Fin E) →
  history (reopen selected retained (project selected source)) e
    ≡ history source e
fullHistoryReopenPointwise selected source retained inactiveAgreement e
  with selected e
... | true = refl
... | false = inactiveAgreement e refl
