module DASHI.Moonshine.Y443Original79CentralQuotientIs80Exact where

------------------------------------------------------------------------
-- ORIGINAL HISTORICAL QUOTIENT PRESENTATION, SOURCE-WORD EXACT.
--
-- Source: Ivanov/Bray Y443. The FIRST 79 original Coxeter/spider
-- relations, followed by the SINGLE central f312=1 equation,
-- generate precisely the preexisting universal 80-relator congruence.
--
-- This is a theorem about the ACTUAL PRESENTED QUOTIENT SETOID,
-- not merely a list count or conditional model satisfaction.
--
-- Still OPEN outside this file: historical group ISO Q80 ≅ Monster,
-- and nontriviality of the actual selected action.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443JMDNonadjacentRelatorConsequencesExact as Consequences
import DASHI.Moonshine.Y443Universal80RelatorCongruenceExact as U
import DASHI.Moonshine.Y443PresentedGroupNodeGenerationExact as Presented

infix 4 _≈₇₉⁺_

-- The historical operation: the least group congruence containing
-- the 79 source relation words AND Ivanov's central equation.
data _≈₇₉⁺_ : U.Expr → U.Expr → Set where
  refl79 : ∀ {x} → x ≈₇₉⁺ x
  sym79 : ∀ {x y} → x ≈₇₉⁺ y → y ≈₇₉⁺ x
  trans79 : ∀ {x y z} → x ≈₇₉⁺ y → y ≈₇₉⁺ z → x ≈₇₉⁺ z
  mul79 : ∀ {x x' y y'} →
    x ≈₇₉⁺ x' → y ≈₇₉⁺ y' →
    Presented.multiply x y ≈₇₉⁺ Presented.multiply x' y'
  inv79 : ∀ {x y} → x ≈₇₉⁺ y →
    Presented.inverse x ≈₇₉⁺ Presented.inverse y
  assoc79 : ∀ x y z →
    Presented.multiply (Presented.multiply x y) z
      ≈₇₉⁺ Presented.multiply x (Presented.multiply y z)
  leftId79 : ∀ x →
    Presented.multiply Presented.empty x ≈₇₉⁺ x
  rightId79 : ∀ x →
    Presented.multiply x Presented.empty ≈₇₉⁺ x
  leftInv79 : ∀ x →
    Presented.multiply (Presented.inverse x) x ≈₇₉⁺ Presented.empty
  rightInv79 : ∀ x →
    Presented.multiply x (Presented.inverse x) ≈₇₉⁺ Presented.empty

  original79 : (w : Y.Word) →
    Consequences._∈_ w Y.doubleMonsterRelators →
    U.wordExpr w ≈₇₉⁺ Presented.empty

  originalCentral :
    U.wordExpr Y.centralInvolutionRelator ≈₇₉⁺ Presented.empty

-- Finite original-list membership transport, generic in the word.
membershipLeft :
  ∀ {w : Y.Word} (prefix suffix : List Y.Word) →
  Consequences._∈_ w prefix →
  Consequences._∈_ w (Y._++_ prefix suffix)
membershipLeft [] suffix ()
membershipLeft (x ∷ xs) suffix Consequences.here =
  Consequences.here
membershipLeft (x ∷ xs) suffix (Consequences.there m) =
  Consequences.there (membershipLeft xs suffix m)

membershipRight :
  ∀ {w : Y.Word} (prefix suffix : List Y.Word) →
  Consequences._∈_ w suffix →
  Consequences._∈_ w (Y._++_ prefix suffix)
membershipRight [] suffix m = m
membershipRight (x ∷ xs) suffix m =
  Consequences.there (membershipRight xs suffix m)

membershipSplit :
  ∀ {w : Y.Word} (prefix suffix : List Y.Word) →
  Consequences._∈_ w (Y._++_ prefix suffix) →
  (Consequences._∈_ w prefix)
    ⊎ (Consequences._∈_ w suffix)
membershipSplit [] suffix m = inj₂ m
membershipSplit (x ∷ xs) suffix Consequences.here =
  inj₁ Consequences.here
membershipSplit (x ∷ xs) suffix (Consequences.there m)
  with membershipSplit xs suffix m
... | inj₁ first = inj₁ (Consequences.there first)
... | inj₂ second = inj₂ second

-- Forward: every original 79+central derivation is valid under all
-- 80 original relations, including group congruence closure.
historicalTo80 :
  ∀ {x y} → x ≈₇₉⁺ y → U._≈₈₀_ x y
historicalTo80 refl79 = U.eqRefl
historicalTo80 (sym79 p) = U.eqSym (historicalTo80 p)
historicalTo80 (trans79 p q) =
  U.eqTrans (historicalTo80 p) (historicalTo80 q)
historicalTo80 (mul79 p q) =
  U.mulCong (historicalTo80 p) (historicalTo80 q)
historicalTo80 (inv79 p) = U.invCong (historicalTo80 p)
historicalTo80 (assoc79 x y z) = U.groupAssoc x y z
historicalTo80 (leftId79 x) = U.groupLeftId x
historicalTo80 (rightId79 x) = U.groupRightId x
historicalTo80 (leftInv79 x) = U.groupLeftInverse x
historicalTo80 (rightInv79 x) = U.groupRightInverse x
historicalTo80 (original79 w member) =
  U.sourceRelator w
    (membershipLeft Y.doubleMonsterRelators
      (Y.centralInvolutionRelator ∷ []) member)
historicalTo80 originalCentral =
  U.sourceRelator Y.centralInvolutionRelator
    (membershipRight Y.doubleMonsterRelators
      (Y.centralInvolutionRelator ∷ []) Consequences.here)

-- Reverse: every ORIGINAL 80 relation is either one of the first
-- 79 original source relations or Ivanov's actual LAST central word.
-- No arbitrary alternate presentation, group, or word equation.
original80ToHistorical :
  ∀ {x y} → U._≈₈₀_ x y → x ≈₇₉⁺ y
original80ToHistorical U.eqRefl = refl79
original80ToHistorical (U.eqSym p) = sym79 (original80ToHistorical p)
original80ToHistorical (U.eqTrans p q) =
  trans79 (original80ToHistorical p) (original80ToHistorical q)
original80ToHistorical (U.mulCong p q) =
  mul79 (original80ToHistorical p) (original80ToHistorical q)
original80ToHistorical (U.invCong p) =
  inv79 (original80ToHistorical p)
original80ToHistorical (U.groupAssoc x y z) = assoc79 x y z
original80ToHistorical (U.groupLeftId x) = leftId79 x
original80ToHistorical (U.groupRightId x) = rightId79 x
original80ToHistorical (U.groupLeftInverse x) = leftInv79 x
original80ToHistorical (U.groupRightInverse x) = rightInv79 x
original80ToHistorical (U.sourceRelator w member)
  with membershipSplit Y.doubleMonsterRelators
         (Y.centralInvolutionRelator ∷ []) member
... | inj₁ first = original79 w first
... | inj₂ Consequences.here = originalCentral
... | inj₂ (Consequences.there ())

-- The identity-on-raw-words quotient equivalence is now CONSTRUCTED.
-- All infinite group consequences are covered by structural induction.
original80IffHistorical79Central :
  (x y : U.Expr) →
  (U._≈₈₀_ x y → x ≈₇₉⁺ y)
    × (x ≈₇₉⁺ y → U._≈₈₀_ x y)
original80IffHistorical79Central x y =
  original80ToHistorical , historicalTo80

historical79PlusCentralSetoidGroup : U.SetoidGroup
historical79PlusCentralSetoidGroup = record
  { U.SetoidGroup.Carrier = U.Expr
  ; U.SetoidGroup.Equivalent = _≈₇₉⁺_
  ; U.SetoidGroup.unit = Presented.empty
  ; U.SetoidGroup.product = Presented.multiply
  ; U.SetoidGroup.inverse = Presented.inverse
  ; U.SetoidGroup.reflexive = λ x → refl79
  ; U.SetoidGroup.symmetric = sym79
  ; U.SetoidGroup.transitive = trans79
  ; U.SetoidGroup.productCongruent = mul79
  ; U.SetoidGroup.inverseCongruent = inv79
  ; U.SetoidGroup.associative = assoc79
  ; U.SetoidGroup.leftUnit = leftId79
  ; U.SetoidGroup.rightUnit = rightId79
  ; U.SetoidGroup.leftInverse = leftInv79
  ; U.SetoidGroup.rightInverse = rightInv79
  }
