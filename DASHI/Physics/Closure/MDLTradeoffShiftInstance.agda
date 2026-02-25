module DASHI.Physics.Closure.MDLTradeoffShiftInstance where

open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst; sym)
open import Data.Nat using (_+_; _≤_; zero; z≤n)
open import Data.Nat.Properties as NatP using (≤-refl; ≤-trans; +-mono-≤; +-identityʳ; +-identityˡ; +-assoc; m≤n+m)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Base using (init; _∷ʳ_)
open import Data.Product using (_,_; proj₂)

open import DASHI.MDL.MDLDescentTradeoff as MDL using (OrderedMonoid; MDLParts; TradeoffLemma)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

-- Ordered monoid over Nat with + and ≤.
NatOrderedMonoid : MDL.OrderedMonoid
NatOrderedMonoid = record
  { M = record
      { N = Nat
      ; _+_ = Data.Nat._+_
      ; 0# = zero
      }
  ; _≤_ = Data.Nat._≤_
  ; refl≤ = λ _ → NatP.≤-refl
  ; trans≤ = λ _ _ _ → NatP.≤-trans
  ; mono+ = λ a b c d le1 le2 → NatP.+-mono-≤ le1 le2
  }

-- Simple nontrivial length: count nonzero trits.
nz : Trit → Nat
nz neg = 1
nz zer = 0
nz pos = 1

countNZ : ∀ {n : Nat} → Vec Trit n → Nat
countNZ [] = 0
countNZ (x ∷ xs) = nz x + countNZ xs

countNZ-snoc :
  ∀ {n : Nat} (xs : Vec Trit n) (a : Trit) →
  countNZ (xs ∷ʳ a) ≡ countNZ xs + nz a
countNZ-snoc [] a =
  trans (NatP.+-identityʳ (nz a))
        (sym (NatP.+-identityˡ (nz a)))
countNZ-snoc (x ∷ xs) a =
  trans (cong (λ k → nz x + k) (countNZ-snoc xs a))
        (sym (NatP.+-assoc (nz x) (countNZ xs) (nz a)))

countNZ-init≤ :
  ∀ {k : Nat} (t : Vec Trit (suc k)) → countNZ (init t) ≤ countNZ t
countNZ-init≤ {zero} (x ∷ []) = z≤n
countNZ-init≤ {suc k} (x ∷ y ∷ ys) =
  NatP.+-mono-≤ (NatP.≤-refl {nz x}) (countNZ-init≤ (y ∷ ys))

projTail-def :
  ∀ {k : Nat} (t : Vec Trit (suc k)) →
  TCP.projTail t ≡ (init t ∷ʳ zer)
projTail-def t = refl

shiftTail-def :
  ∀ {k : Nat} (x : Trit) (xs : Vec Trit k) →
  TCP.shiftTail (x ∷ xs) ≡ xs ∷ʳ zer
shiftTail-def x xs = refl

countNZ-projTail≤ :
  ∀ {k : Nat} (t : Vec Trit k) → countNZ (TCP.projTail t) ≤ countNZ t
countNZ-projTail≤ {zero} [] = NatP.≤-refl
countNZ-projTail≤ {suc k} t
  rewrite projTail-def t
        | countNZ-snoc (init t) zer
        | NatP.+-identityʳ (countNZ (init t))
  = countNZ-init≤ t

countNZ-shiftTail≤ :
  ∀ {k : Nat} (t : Vec Trit k) → countNZ (TCP.shiftTail t) ≤ countNZ t
countNZ-shiftTail≤ {zero} [] = NatP.≤-refl
countNZ-shiftTail≤ {suc k} (x ∷ xs)
  rewrite shiftTail-def x xs
        | countNZ-snoc xs zer
        | NatP.+-identityʳ (countNZ xs)
  = NatP.m≤n+m (countNZ xs) (nz x)

countNZ-tailStep≤ :
  ∀ {k : Nat} (t : Vec Trit k) → countNZ (TCP.tailStep t) ≤ countNZ t
countNZ-tailStep≤ t =
  NatP.≤-trans (countNZ-projTail≤ (TCP.shiftTail t)) (countNZ-shiftTail≤ t)

tailOf-Pᵣ :
  ∀ (m k : Nat) (x : RTC.Carrier (m + k)) →
  TCP.tailOf m k (TCP.Pᵣ {m} {k} x) ≡ TCP.projTail (TCP.tailOf m k x)
tailOf-Pᵣ m k x with TCP.split m k x
... | (c , t)
  rewrite TCP.Pᵣ-++ m k c t
        | TCP.split-++ m k c (TCP.projTail t)
  = refl

tailOf-Tᵣ :
  ∀ (m k : Nat) (x : RTC.Carrier (m + k)) →
  TCP.tailOf m k (TCP.Tᵣ {m} {k} x) ≡ TCP.tailStep (TCP.tailOf m k x)
tailOf-Tᵣ m k x =
  cong Data.Product.proj₂ (TCP.split-Tᵣ m k x)

resid-drop-lemma :
  ∀ {m k : Nat} (x : RTC.Carrier (m + k)) →
  countNZ (TCP.tailOf m k (TCP.Tᵣ {m} {k} x)) ≤ countNZ (TCP.tailOf m k x)
resid-drop-lemma {m} {k} x
  rewrite tailOf-Tᵣ m k x
  = countNZ-tailStep≤ (TCP.tailOf m k x)

coarse-invariant-R :
  ∀ (m k : Nat) (x : RTC.Carrier (m + k)) →
  TCP.coarseOf m k (TCP.Rᵣ {m} {k} x) ≡ TCP.coarseOf m k x
coarse-invariant-R m k x with TCP.split m k x
... | (c , t)
  rewrite TCP.split-++ m k c (TCP.shiftTail t)
  = refl

coarse-invariant-P :
  ∀ (m k : Nat) (x : RTC.Carrier (m + k)) →
  TCP.coarseOf m k (TCP.Pᵣ {m} {k} x) ≡ TCP.coarseOf m k x
coarse-invariant-P m k x with TCP.split m k x
... | (c , t)
  rewrite TCP.split-++ m k c (TCP.projTail t)
  = refl

coarse-invariant-T :
  ∀ (m k : Nat) (x : RTC.Carrier (m + k)) →
  TCP.coarseOf m k (TCP.Tᵣ {m} {k} x) ≡ TCP.coarseOf m k x
coarse-invariant-T m k x =
  trans (coarse-invariant-P m k (TCP.Rᵣ {m} {k} x))
        (coarse-invariant-R m k x)

coarseOf-PT-≡-P :
  ∀ (m k : Nat) (x : RTC.Carrier (m + k)) →
  TCP.coarseOf m k (TCP.Pᵣ {m} {k} (TCP.Tᵣ {m} {k} x)) ≡
  TCP.coarseOf m k (TCP.Pᵣ {m} {k} x)
coarseOf-PT-≡-P m k x =
  let
    p-idem = TCP.Pᵣ-idem m k (TCP.Rᵣ {m} {k} x)
    cPT : TCP.coarseOf m k (TCP.Pᵣ {m} {k} (TCP.Tᵣ {m} {k} x)) ≡
          TCP.coarseOf m k (TCP.Tᵣ {m} {k} x)
    cPT = cong (TCP.coarseOf m k) p-idem
    cT  = coarse-invariant-T m k x
    cP  = coarse-invariant-P m k x
  in
  trans cPT (trans cT (sym cP))

model-drop-lemma :
  ∀ {m k : Nat} (x : RTC.Carrier (m + k)) →
  countNZ (TCP.coarseOf m k (TCP.Pᵣ {m} {k} (TCP.Tᵣ {m} {k} x)))
    ≤ countNZ (TCP.coarseOf m k (TCP.Pᵣ {m} {k} x))
model-drop-lemma {m} {k} x
  rewrite coarseOf-PT-≡-P m k x
  = NatP.≤-refl

-- MDL parts: model length = countNZ of coarse, residual length = countNZ of tail.
MDLPartsShift : ∀ {m k : Nat} → MDL.MDLParts (RTC.Carrier (m + k)) NatOrderedMonoid
MDLPartsShift {m} {k} =
  record
    { P = TCP.Pᵣ {m} {k}
    ; D = λ x → x
    ; T = TCP.Tᵣ {m} {k}
    ; ModelLen = λ x → countNZ (TCP.coarseOf m k x)
    ; ResidLen = λ x → countNZ (TCP.tailOf m k x)
    ; MDL = λ x → countNZ (TCP.coarseOf m k (TCP.Pᵣ {m} {k} x)) + countNZ (TCP.tailOf m k x)
    ; MDL-def = λ _ → refl
    }

-- Tradeoff lemma from coarse invariance and projTail decreasing nonzero count.
TradeoffShift : ∀ {m k : Nat} → MDL.TradeoffLemma (MDLPartsShift {m} {k})
TradeoffShift {m} {k} =
  record
    { model-drop = model-drop-lemma {m} {k}
    ; resid-drop = resid-drop-lemma {m} {k}
    }
