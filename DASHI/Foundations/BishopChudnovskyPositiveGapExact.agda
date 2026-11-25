module DASHI.Foundations.BishopChudnovskyPositiveGapExact where

-- SOURCE-WRITTEN, not kernel checked. Universal original weighted
-- contraction by a positive polynomial, not finite sampling.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_; _≤_; NonZero; nonZero)
open import Data.Nat using (_^_)
import Data.Nat.Properties as NP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
import Data.Integer.Base as Z
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyIndexedEdgeAlgebraExact as E

weight : Nat → Nat
weight i = CH.A + CH.B * i

leafMagnitude : Nat → Nat
leafMagnitude i = 24 * (2 * i + 1) * (6 * i + 1) * (6 * i + 5)

qNat : Nat → Nat
qNat zero = 1
qNat (suc i) = CH.C * (suc i ^ 3)

sourceQNatural : (n : Nat) → CH.sourceQ n ≡ Z.+_ (qNat n)
sourceQNatural zero = refl
sourceQNatural (suc i) = refl

sourcePNegativeMagnitude : (i : Nat) →
  CH.sourceP (suc i) ≡ Z.-_ (Z.+_ (leafMagnitude i))
sourcePNegativeMagnitude i = refl

-- The constant coefficient minus one, so the full gap is a successor.
gapTail : Nat → Nat
gapTail i =
  3420813714202353688903679 +
  i * (152324142589183949932855296 +
  i * (435555656263180381923311616 +
  i * (427696936518221473282523136 +
  i * 141048195668958693853495296)))

scaledTerm : Nat → Nat
scaledTerm i = (2 ^ 41) * (leafMagnitude i * weight (suc i))

weightedGapIdentity : (i : Nat) →
  scaledTerm i + suc (gapTail i) ≡ qNat (suc i) * weight i
weightedGapIdentity i =
  solve 1
    (λ x →
      (con (2 ^ 41) :*
        ((con 24 :* (con 2 :* x :+ con 1)
                 :* (con 6 :* x :+ con 1)
                 :* (con 6 :* x :+ con 5))
          :* (con CH.A :+ con CH.B :* (con 1 :+ x))))
      :+ (con 1 :+
        (con 3420813714202353688903679 :+
        x :* (con 152324142589183949932855296 :+
        x :* (con 435555656263180381923311616 :+
        x :* (con 427696936518221473282523136 :+
        x :* con 141048195668958693853495296)))))
      :=
      (con CH.C :*
        ((con 1 :+ x) :* ((con 1 :+ x) :* ((con 1 :+ x) :* con 1))))
        :* (con CH.A :+ con CH.B :* x))
    refl i

weightedContraction : (i : Nat) →
  scaledTerm i < qNat (suc i) * weight i
weightedContraction i =
  subst (λ v → suc (scaledTerm i) ≤ v)
    (trans (sym (NP.+-suc (scaledTerm i) (gapTail i)))
           (weightedGapIdentity i))
    (NP.m≤m+n (suc (scaledTerm i)) (gapTail i))

qNatNonZero : (n : Nat) → NonZero (qNat n)
qNatNonZero zero = nonZero
qNatNonZero (suc i) =
  NP.m*n≢0 CH.C (suc i ^ 3)
    {{nonZero}} {{NP.m^n≢0 (suc i) 3}}

qProduct : Nat → Nat
qProduct zero = 1
qProduct (suc n) = qProduct n * qNat n

qProductNonZero : (n : Nat) → NonZero (qProduct n)
qProductNonZero zero = nonZero
qProductNonZero (suc n) =
  NP.m*n≢0 (qProduct n) (qNat n)
    {{qProductNonZero n}} {{qNatNonZero n}}

-- This refers to the literal raw prefix, not a parallel Q coordinate.
prefixQNatural : (n : Nat) → E.Q n ≡ Z.+_ (qProduct n)
prefixQNatural zero = refl
prefixQNatural (suc n)
  rewrite E.prefixQStep n | prefixQNatural n | sourceQNatural n = refl

-- Two-step original affine identity. This is the carrier on which
-- the positive gap can be consumed after signed-product transport.
open import Data.Integer.Solver
  renaming (module +-*-Solver to ZSolver)
open ZSolver using () renaming
  (solve to zsolve; _:+_ to _⊕_; _:*_ to _⊗_; con to zk; _:=_ to _⊜_)

twoStepSource :
  (n : Nat) →
  E.T (suc (suc n)) ≡
  Z._+_
    (Z._*_ (Z._*_ (E.T n) (CH.sourceQ n)) (CH.sourceQ (suc n)))
    (Z._*_
      (Z._*_ (E.P n) (CH.sourceP n))
      (Z._+_
        (Z._*_ (E.a n) (CH.sourceQ (suc n)))
        (Z._*_ (CH.sourceP (suc n)) (E.a (suc n)))))
twoStepSource n
  rewrite E.prefixTStep (suc n) | E.prefixTStep n | E.sourceDeltaStep n =
  zsolve 7
    (λ t q r p u a v →
      (((t ⊗ q) ⊕ (p ⊗ u ⊗ a)) ⊗ r)
        ⊕ (p ⊗ u ⊗ v)
      ⊜ (t ⊗ q ⊗ r) ⊕ ((p ⊗ u) ⊗ ((a ⊗ r) ⊕ v)))
    refl (E.T n) (CH.sourceQ n) (CH.sourceQ (suc n))
      (E.P n) (CH.sourceP n) (E.a n)
      (Z._*_ (CH.sourceP (suc n)) (E.a (suc n)))
