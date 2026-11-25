module DASHI.Foundations.BishopChudnovskyAdjacentNestingExact where

-- SOURCE-WRITTEN, UNCOMPILED. Consume actual signed one-step and
-- two-step cross identities, not a supplied abstract convex sequence.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_)
open import Data.Empty using (⊥-elim)
import Data.Nat.Base as N
import Data.Integer.Base as Z
import Data.Integer.Properties as I
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyIndexedEdgeAlgebraExact as E
import DASHI.Foundations.BishopChudnovskyPositiveGapExact as G
import DASHI.Foundations.BishopChudnovskyPairedTotalityExact as T
import DASHI.Foundations.BishopChudnovskyPrefixSemanticsExact as P

positiveOrder : ∀ {z} → T.Positive z → Z._≤_ Z.0ℤ z
positiveOrder (T.pos a refl) = Z.+≤+ N.z≤n

negativeOrder : ∀ {z} → T.Negative z → Z._≤_ z Z.0ℤ
negativeOrder (T.neg a refl) = Z.-≤+

negativeTimesPositive : ∀ {x y} → T.Negative x → T.Positive y →
  T.Negative (Z._*_ x y)
negativeTimesPositive {x} {y} a b =
  subst T.Negative (I.*-comm y x) (T.positiveTimesNegative b a)

-- Additive cross identity: b = a + gap, with signs retained.
up : ∀ {a b g} → b ≡ Z._+_ a g → T.Positive g → Z._≤_ a b
up {a} {b} {g} eq h =
  subst (Z._≤_ a) (sym eq)
    (subst (λ v → Z._≤_ v (Z._+_ a g)) (I.+-identityʳ a)
      (I.+-monoʳ-≤ a (positiveOrder h)))

down : ∀ {a b g} → b ≡ Z._+_ a g → T.Negative g → Z._≤_ b a
down {a} {b} {g} eq h =
  subst (λ v → Z._≤_ v a) (sym eq)
    (subst (Z._≤_ (Z._+_ a g)) (I.+-identityʳ a)
      (I.+-monoʳ-≤ a (negativeOrder h)))

fracOrder : (a b : Z.ℤ) (d e : Nat) (hd : N.NonZero d) (he : N.NonZero e) →
  Z._≤_ (Z._*_ a (Z.+_ e)) (Z._*_ b (Z.+_ d)) →
  P.frac a d hd Q.≤ P.frac b e he
fracOrder a b zero e hd he h =
  ⊥-elim (N.≢-nonZero⁻¹ zero {{hd}} refl)
fracOrder a b (suc d) zero hd he h =
  ⊥-elim (N.≢-nonZero⁻¹ zero {{he}} refl)
fracOrder a b (suc d) (suc e) hd he h = Q.*≤* h

S : Nat → Q.ℚᵘ
S = P.rawSum

rawOrder : (n m : Nat) →
  Z._≤_ (Z._*_ (E.T n) (E.Q m)) (Z._*_ (E.T m) (E.Q n)) →
  S n Q.≤ S m
rawOrder n m h =
  fracOrder (E.T n) (E.T m) (G.qProduct n) (G.qProduct m)
    (G.qProductNonZero n) (G.qProductNonZero m) order
  where
  order : Z._≤_ (Z._*_ (E.T n) (Z.+_ (G.qProduct m)))
                 (Z._*_ (E.T m) (Z.+_ (G.qProduct n)))
  order rewrite sym (G.prefixQNatural n) | sym (G.prefixQNatural m) = h

-- Two-step cross uses the original positive pairGap, already supplied
-- by PairedTotalityExact. No fresh signed ratio division is necessary.
twoStepCross : (n : Nat) →
  Z._*_ (E.T (suc (suc n))) (E.Q n) ≡
  Z._+_ (Z._*_ (E.T n) (E.Q (suc (suc n))))
         (Z._*_ (Z._*_ (T.W n) (T.pairGap n)) (E.Q n))
twoStepCross n rewrite G.twoStepSource n | E.prefixQStep (suc n) | E.prefixQStep n =
  solve 6 (λ t q r d w g →
    ((t :* q :* r) :+ (w :* g)) :* d
      := (t :* (d :* q :* r)) :+ ((w :* g) :* d))
    refl (E.T n) (CH.sourceQ n) (CH.sourceQ (suc n)) (E.Q n)
      (T.W n) (T.pairGap n)

oneUp : (n : Nat) → T.Positive (T.W n) → S n Q.≤ S (suc n)
oneUp n w = rawOrder n (suc n)
  (up (E.sourceAdjacentCrossIdentity n)
    (T.positiveTimesPositive
      (T.positiveTimesPositive w (T.weightPositive n)) (T.prefixQPositive n)))

oneDown : (n : Nat) → T.Negative (T.W n) → S (suc n) Q.≤ S n
oneDown n w = rawOrder (suc n) n
  (down (E.sourceAdjacentCrossIdentity n)
    (negativeTimesPositive
      (negativeTimesPositive w (T.weightPositive n)) (T.prefixQPositive n)))

twoUp : (n : Nat) → T.Positive (T.W n) → S n Q.≤ S (suc (suc n))
twoUp n w = rawOrder n (suc (suc n))
  (up (twoStepCross n)
    (T.positiveTimesPositive
      (T.positiveTimesPositive w (T.pairGapPositive n)) (T.prefixQPositive n)))

twoDown : (n : Nat) → T.Negative (T.W n) → S (suc (suc n)) Q.≤ S n
twoDown n w = rawOrder (suc (suc n)) n
  (down (twoStepCross n)
    (negativeTimesPositive
      (negativeTimesPositive w (T.pairGapPositive n)) (T.prefixQPositive n)))

evenBracket : (k : Nat) →
  (S (T.twice k) Q.≤ S (suc (suc (T.twice k)))) ×
  (S (suc (suc (T.twice k))) Q.≤ S (suc (T.twice k)))
evenBracket k =
  twoUp (T.twice k) (T.evenWPositive k) ,
  oneDown (suc (T.twice k)) (T.oddWNegative k)

-- Actual adjacent sorted prefix, not an alternative midpoint stream.
lower upper : Nat → Q.ℚᵘ
lower n = S n Q.⊓ S (suc n)
upper n = S n Q.⊔ S (suc n)

nested : (n : Nat) →
  (lower n Q.≤ lower (suc n)) × (upper (suc n) Q.≤ upper n)
nested n with T.parity n
... | T.even k =
  let
    x = T.twice k
    a = oneUp x (T.evenWPositive k)
    b = twoUp x (T.evenWPositive k)
    c = oneDown (suc x) (T.oddWNegative k)
  in QP.≤-respˡ-≃ (QP.≃-sym (QP.p≤q⇒p⊓q≃p a))
       (QP.≤-respʳ-≃ (QP.≃-sym (QP.p≥q⇒p⊓q≃q c)) b) ,
     QP.≤-respˡ-≃ (QP.≃-sym (QP.p≥q⇒p⊔q≃p c))
       (QP.≤-respʳ-≃ (QP.≃-sym (QP.p≤q⇒p⊔q≃q a)) QP.≤-refl)
... | T.odd k =
  let
    x = suc (T.twice k)
    a = oneDown x (T.oddWNegative k)
    b = twoDown x (T.oddWNegative k)
    c = oneUp (T.twice (suc k)) (T.evenWPositive (suc k))
  in QP.≤-respˡ-≃ (QP.≃-sym (QP.p≥q⇒p⊓q≃q a))
       (QP.≤-respʳ-≃ (QP.≃-sym (QP.p≤q⇒p⊓q≃p c)) QP.≤-refl) ,
     QP.≤-respˡ-≃ (QP.≃-sym (QP.p≤q⇒p⊔q≃q c))
       (QP.≤-respʳ-≃ (QP.≃-sym (QP.p≥q⇒p⊔q≃p a)) b)
