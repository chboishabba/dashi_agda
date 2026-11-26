module DASHI.Physics.YangMills.BalabanCMP119Section2NestedOmegaOwnershipExact where

------------------------------------------------------------------------
-- Source calibration: Tadeusz Bałaban, "Convergent Renormalization
-- Expansions for Lattice Gauge Theories", Commun. Math. Phys. 119 (1988),
-- 243-285, DOI 10.1007/BF01217741, printed p. 254 Eq. (2.1): the selected
-- domain sequence is descending Ω₁ ⊃ Λ₁ ⊃ Ω₂ ⊃ Λ₂ ⊃ ⋯.  The visual
-- source ledger is Docs/physics/YMClayW0PrimaryVisualEquationCrosswalk20261126.md.
--
-- `Section2NestedOmegaCarrier` is the exact structural fragment of
-- `P10.P10P11WeightedRelativeDomainCarrier` used by these two lemmas.  It is a
-- DASHI abstraction, not an inhabited source Ω/Λ/S/B dictionary, and not a
-- physical covariance or Clay receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Nat.Base renaming (ℕ to Nat) using (zero; suc; _≤_; _+_; z≤n; s≤s)
open import Data.Product using (Σ; _,_; _×_; proj₁)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import Data.Nat.Base as N
import Data.Nat.Properties as NP

record Section2NestedOmegaCarrier : Set₁ where
  field
    Block : Set
    inOmega : Nat → Block → Set
    inRelativeDomain : Nat → Block → Set
    terminalOwner : Block → Nat

    nestedDomains :
      ∀ j B → inOmega (suc j) B → inOmega j B

    relativeDomainElimination :
      ∀ j B → inRelativeDomain j B →
        inOmega j B × (inOmega (suc j) B → ⊥)

    ownerInRelativeDomain :
      ∀ B → inRelativeDomain (terminalOwner B) B

open Section2NestedOmegaCarrier

private
  atMost : Nat → Nat → Set
  atMost = _≤_

  ownerIndex :
    (carrier : Section2NestedOmegaCarrier) → Block carrier → Nat
  ownerIndex carrier B = terminalOwner carrier B

  difference :
    ∀ {b a : Nat} → b ≤ a → Σ Nat (λ d → d + b ≡ a)
  difference {zero} {a} z≤n = a , NP.+-identityʳ a
  difference {suc b} {suc a} (s≤s bLeA) with difference bLeA
  ... | d , eq = d , trans (NP.+-suc d b) (cong suc eq)

  weakenBy :
    (carrier : Section2NestedOmegaCarrier) →
    {B : Block carrier} → (d b : Nat) →
    inOmega carrier (d + b) B → inOmega carrier b B
  weakenBy carrier {B} zero b Ω = Ω
  weakenBy carrier {B} (suc d) b Ω =
    weakenBy carrier {B} d b
      (nestedDomains carrier (d + b) B Ω)

  weakenWithinOmega :
    (carrier : Section2NestedOmegaCarrier) →
    {B : Block carrier} → {b a : Nat} →
    b ≤ a → inOmega carrier a B → inOmega carrier b B
  weakenWithinOmega carrier {B} {b} {a} bLeA Ωa
    with difference bLeA
  ... | d , eq =
    weakenBy carrier d b
      (subst (λ n → inOmega carrier n B) (sym eq) Ωa)

relativeOwnedBlockInAllEarlierOmega :
  (carrier : Section2NestedOmegaCarrier) →
  {B : Block carrier} → {m i : Nat} →
  i ≤ m →
  inRelativeDomain carrier m B →
  inOmega carrier i B
relativeOwnedBlockInAllEarlierOmega carrier {B} {m} {i} ile relativeAt =
  weakenWithinOmega carrier {B} {i} {m} ile
    (proj₁ (relativeDomainElimination carrier m B relativeAt))

ownedBlockInAllEarlierOmega :
  (carrier : Section2NestedOmegaCarrier) →
  {B : Block carrier} → {i : Nat} →
  atMost i (ownerIndex carrier B) →
  inOmega carrier i B
ownedBlockInAllEarlierOmega carrier {B} {i} ileOwner =
  relativeOwnedBlockInAllEarlierOmega carrier {B} {ownerIndex carrier B} {i}
    ileOwner (ownerInRelativeDomain carrier B)
