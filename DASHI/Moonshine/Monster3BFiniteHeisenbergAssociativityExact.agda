module DASHI.Moonshine.Monster3BFiniteHeisenbergAssociativityExact where

------------------------------------------------------------------------
-- ASSOCIATIVITY OF THE ACTUAL FINITE HEISENBERG MULTIPLICATION
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergDotBilinearityExact as Dot
import DASHI.Moonshine.Monster3BFiniteHeisenbergCocycleExact as Cocycle
import DASHI.Moonshine.Monster3BF3AlgebraExact as F3

infixl 6 _⊕_
_⊕_ : Trit → Trit → Trit
_⊕_ = G._+3_

------------------------------------------------------------------------
-- 1. Central-phase normalization from one cocycle equality.
------------------------------------------------------------------------

normalizeLeftPhase : (c d e p q : Trit) →
  (c ⊕ (d ⊕ p)) ⊕ (e ⊕ q)
  ≡ c ⊕ (d ⊕ (e ⊕ (p ⊕ q)))
normalizeLeftPhase c d e p q =
  trans
    (F3.plusAssoc c (d ⊕ p) (e ⊕ q))
    (trans
      (cong (λ x → c ⊕ x) (Dot.mergePairs d p e q))
      (cong (λ x → c ⊕ x) (F3.plusAssoc d e (p ⊕ q))))

normalizeRightPhase : (c d e r s : Trit) →
  c ⊕ ((d ⊕ (e ⊕ r)) ⊕ s)
  ≡ c ⊕ (d ⊕ (e ⊕ (r ⊕ s)))
normalizeRightPhase c d e r s =
  cong (λ x → c ⊕ x)
    (trans
      (F3.plusAssoc d (e ⊕ r) s)
      (cong (λ x → d ⊕ x) (F3.plusAssoc e r s)))

phaseAssociativityFromCocycle :
  (c d e p q r s : Trit) →
  p ⊕ q ≡ r ⊕ s →
  (c ⊕ (d ⊕ p)) ⊕ (e ⊕ q)
  ≡ c ⊕ ((d ⊕ (e ⊕ r)) ⊕ s)
phaseAssociativityFromCocycle c d e p q r s cocycleEq =
  trans
    (normalizeLeftPhase c d e p q)
    (trans
      (cong (λ x → c ⊕ (d ⊕ (e ⊕ x))) cocycleEq)
      (sym (normalizeRightPhase c d e r s)))

------------------------------------------------------------------------
-- 2. Associativity of compose on the same central-extension carrier.
------------------------------------------------------------------------

composeAssociative : (g h k : H.Heisenberg6) →
  H.compose (H.compose g h) k ≡ H.compose g (H.compose h k)
composeAssociative
  (H.heisenberg6 u c)
  (H.heisenberg6 v d)
  (H.heisenberg6 w e)
  rewrite Cocycle.addX6Assoc
            (H.translationPart u) (H.translationPart v) (H.translationPart w)
        | Cocycle.addX6Assoc
            (H.modulationPart u) (H.modulationPart v) (H.modulationPart w)
  = phaseAssociativityFromCocycle
      c d e
      (Cocycle.cocycle u v)
      (Cocycle.cocycle (Cocycle.addSymplectic u v) w)
      (Cocycle.cocycle v w)
      (Cocycle.cocycle u (Cocycle.addSymplectic v w))
      (Cocycle.cocycleIdentity u v w)

record HeisenbergAssociativityBoundary : Set where
  constructor heisenbergAssociativityBoundary
  field
    quotientAdditionAssociative : Bool
    cocycleIdentityUsed : Bool
    centralPhaseNormalizationProved : Bool
    actualComposeAssociative : Bool
open HeisenbergAssociativityBoundary public

canonicalHeisenbergAssociativityBoundary : HeisenbergAssociativityBoundary
canonicalHeisenbergAssociativityBoundary =
  heisenbergAssociativityBoundary true true true true
