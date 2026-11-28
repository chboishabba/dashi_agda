module DASHI.Mathematics.Complexity.PNPF3CollectiveNormalExact where

-- Reuse the exact F3 vector and image owner. A pairwise factor graph
-- alone is not an independence certificate; agreement is on the entire
-- collective intersection. Native table/rank reification remains separate.
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)
import DASHI.Foundations.Base369TriTruthField as F
import DASHI.Foundations.FiniteLinear.F3Subspace as L
import DASHI.Foundations.FiniteLinear.AntiDiagonalKernel as Scalar
import DASHI.Mathematics.Complexity.PNPF3SyndromeBoundaryExact as S
open S using (V; addV; minusV; negV; scaleV; syndromeSpace; restoreV)

exchangeTrit : ∀ a b c d →
  F.triAdd a b ≡ F.triAdd c d →
  F.triAdd (F.triNeg c) a ≡ F.triAdd (F.triNeg b) d
exchangeTrit a b c d eq =
  trans (sym (F.triAdd-identityʳ (F.triAdd (F.triNeg c) a)))
    (trans (cong (F.triAdd (F.triAdd (F.triNeg c) a)) (sym (F.triAdd-inverseˡ b)))
      (trans (L.addInterchange (F.triNeg c) a (F.triNeg b) b)
        (trans (cong (F.triAdd (F.triAdd (F.triNeg c) (F.triNeg b))) eq)
          (trans (sym (L.addInterchange (F.triNeg c) c (F.triNeg b) d))
            (trans (cong (λ x → F.triAdd x (F.triAdd (F.triNeg b) d))
              (F.triAdd-inverseˡ c))
              (F.triAdd-identityˡ (F.triAdd (F.triNeg b) d)))))))

exchangeV : ∀ {n} (a b c d : V n) → addV a b ≡ addV c d →
  minusV a c ≡ minusV d b
exchangeV [] [] [] [] refl = refl
exchangeV (a ∷ as) (b ∷ bs) (c ∷ cs) (d ∷ ds) eq =
  cong₂ _∷_ (exchangeTrit a b c d (cong head eq))
    (exchangeV as bs cs ds (cong tail eq))
  where
    head : ∀ {n} → V (suc n) → TriTruth
    head (x ∷ xs) = x
    tail : ∀ {n} → V (suc n) → V n
    tail (x ∷ xs) = xs

negScaleTrit : ∀ x → F.triMul tri-high x ≡ F.triNeg x
negScaleTrit tri-low = refl
negScaleTrit tri-mid = refl
negScaleTrit tri-high = refl

negScaleV : ∀ {n} (v : V n) → scaleV tri-high v ≡ negV v
negScaleV [] = refl
negScaleV (x ∷ xs) = cong₂ _∷_ (negScaleTrit x) (negScaleV xs)

differenceMember : ∀ {n} (U : L.F3Subspace (syndromeSpace n))
  {a c : V n} → L.Member U a → L.Member U c → L.Member U (minusV a c)
differenceMember U {a} {c} ha hc =
  transport (negScaleV c) (L.addMember U (L.scaleMember U tri-high hc) ha)
  where
    transport : ∀ {x y} → x ≡ y → L.Member U (addV x a) → L.Member U (addV y a)
    transport refl h = h

module Glue {n : Nat}
  (U W : L.F3Subspace (syndromeSpace n))
  (f g : L.F3LinearMap (syndromeSpace n) Scalar.scalarSpace)
  (agree : ∀ x → L.Member U x → L.Member W x → L.apply f x ≡ L.apply g x)
  where

  evaluatedRestore : ∀ (m : L.F3LinearMap (syndromeSpace n) Scalar.scalarSpace)
    x y → F.triAdd (L.apply m x) (L.apply m (minusV y x)) ≡ L.apply m y
  evaluatedRestore m x y =
    trans (sym (L.preservesAdd m x (minusV y x))) (cong (L.apply m) (restoreV x y))

  stable : ∀ a b c d → L.Member U a → L.Member W b →
    L.Member U c → L.Member W d → addV a b ≡ addV c d →
    F.triAdd (L.apply f a) (L.apply g b) ≡ F.triAdd (L.apply f c) (L.apply g d)
  stable a b c d ha hb hc hd eq =
    trans (cong (λ x → F.triAdd x (L.apply g b)) (sym (evaluatedRestore f c a)))
      (trans (sym (F.triAdd-assoc (L.apply f c) (L.apply f (minusV a c)) (L.apply g b)))
        (trans (cong (F.triAdd (L.apply f c))
          (trans (cong (λ x → F.triAdd x (L.apply g b)) evalEq)
            (F.triAdd-comm (L.apply g (minusV d b)) (L.apply g b))))
          (cong (F.triAdd (L.apply f c)) (evaluatedRestore g b d))))
    where
      diffEq = exchangeV a b c d eq
      inW : L.Member W (minusV a c)
      inW = transport (sym diffEq) (differenceMember W hd hb)
        where
          transport : ∀ {x y} → x ≡ y → L.Member W x → L.Member W y
          transport refl h = h
      evalEq : L.apply f (minusV a c) ≡ L.apply g (minusV d b)
      evalEq = trans (agree (minusV a c) (differenceMember U ha hc) inW)
        (cong (L.apply g) diffEq)
