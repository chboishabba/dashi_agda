module DASHI.Foundations.BishopChudnovskyWidthSourceExact where

-- Source-written; not kernel checked. Width source arithmetic, independent
-- of the analytic Chudnovsky identity and of any finite decimal samples.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _^_)
import Data.Nat.Properties as NP
import Data.Nat.DivMod as ND
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)
import Data.Integer.Base as Z
import Data.Integer.Properties as ZP
open import Data.Integer.Solver renaming (module +-*-Solver to ZSolver)
open ZSolver using () renaming
  (solve to zsolve; _:+_ to _⊕_; _:*_ to _⊗_; con to zk; _:=_ to _⊜_)
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyIndexedEdgeAlgebraExact as E
import DASHI.Foundations.BishopChudnovskyPositiveGapExact as G
import DASHI.Foundations.BishopChudnovskyPairedTotalityExact as T
import DASHI.Foundations.BishopNatSquareRootFloorApproximationExact as Root
import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact as Floor

M : Nat
M = 2 ^ 41

-- Same signed product, with magnitude taken only at the consumer.
wAbs : Nat → Nat
wAbs n = Z.∣ T.W n ∣
H : Nat → Nat
H n = wAbs n * G.weight n

hIsOriginalDefectMagnitude : (n : Nat) → Z.∣ E.delta n ∣ ≡ H n
hIsOriginalDefectMagnitude n = ZP.abs-* (T.W n) (E.a n)

wAbsStep : (n : Nat) → wAbs (suc n) ≡ wAbs n * G.leafMagnitude n
wAbsStep n rewrite T.WStep n | G.sourcePNegativeMagnitude n =
  trans (ZP.abs-* (T.W n) (Z.-_ (Z.+_ (G.leafMagnitude n))))
    (cong (wAbs n *_) (ZP.∣-i∣≡∣i∣ (Z.+_ (G.leafMagnitude n))))

-- M H_(n+1) <= q_(n+1) H_n; all products are nonnegative.
defectContraction : (n : Nat) → M * H (suc n) ≤ G.qNat (suc n) * H n
defectContraction n =
  let
    a = wAbs n
    m = G.leafMagnitude n
    v = G.weight (suc n)
    q = G.qNat (suc n)
    u = G.weight n
    left : M * ((a * m) * v) ≡ a * (M * (m * v))
    left = solve 4 (λ a′ m′ v′ b →
      b :* ((a′ :* m′) :* v′) := a′ :* (b :* (m′ :* v′)))
      refl a m v M
    right : a * (q * u) ≡ q * (a * u)
    right = solve 3 (λ a′ q′ u′ → a′ :* (q′ :* u′) := q′ :* (a′ :* u′))
      refl a q u
  in
  subst (λ x → x ≤ q * H n)
    (sym (trans (cong (λ v′ → M * (v′ * v)) (wAbsStep n)) left))
    (subst (λ y → a * (M * (m * v)) ≤ y) right
      (NP.*-mono-≤ NP.≤-refl (NP.<⇒≤ (G.weightedContraction n))))

-- Explicit all-index bound, no division by original source products.
scaledDefectBound : (n : Nat) → (M ^ n) * H n ≤ CH.A * G.qProduct (suc n)
scaledDefectBound zero = NP.≤-refl
scaledDefectBound (suc n) =
  let
    p = M ^ n
    h = H n
    h′ = H (suc n)
    q = G.qNat (suc n)
    Q = G.qProduct (suc n)
    left = solve 3 (λ p′ m h″ → (m :* p′) :* h″ := p′ :* (m :* h″))
      refl p M h′
    middle = solve 3 (λ p′ q′ h″ → p′ :* (q′ :* h″) := (p′ :* h″) :* q′)
      refl p q h
    right = solve 3 (λ a Q′ q′ → (a :* Q′) :* q′ := a :* (Q′ :* q′))
      refl CH.A Q q
    step = NP.*-mono-≤ NP.≤-refl (defectContraction n)
    step2 = NP.*-mono-≤ (scaledDefectBound n) NP.≤-refl
  in NP.≤-trans (NP.≤-reflexive left)
    (NP.≤-trans step
      (NP.≤-trans (NP.≤-reflexive middle)
        (NP.≤-trans step2 (NP.≤-reflexive right))))

-- Translate the original numerator by the desired lower-bound plane.
-- Slack = 2T-AQ; positivity is stronger than T>0.
negA : Z.ℤ
negA = Z.-_ (Z.+_ CH.A)

slack : Nat → Z.ℤ
slack n = Z._+_ (Z._*_ (Z.+_ 2) (E.T n)) (Z._*_ negA (E.Q n))

slackPair : (n : Nat) →
  slack (suc (suc n)) ≡
    Z._+_ (Z._*_ (Z._*_ (slack n) (CH.sourceQ n)) (CH.sourceQ (suc n)))
      (Z._*_ (Z.+_ 2) (Z._*_ (T.W n) (T.pairGap n)))
slackPair n rewrite G.twoStepSource n | E.prefixQStep (suc n) | E.prefixQStep n =
  zsolve 7
    (λ t q r v w g a →
      (zk (Z.+_ 2) ⊗ ((t ⊗ q ⊗ r) ⊕ (w ⊗ g)))
        ⊕ (a ⊗ (v ⊗ q ⊗ r))
      ⊜ (((zk (Z.+_ 2) ⊗ t) ⊕ (a ⊗ v)) ⊗ q ⊗ r)
        ⊕ (zk (Z.+_ 2) ⊗ (w ⊗ g)))
    refl (E.T n) (CH.sourceQ n) (CH.sourceQ (suc n))
      (E.Q n) (T.W n) (T.pairGap n) negA

slackSingle : (n : Nat) →
  slack (suc n) ≡
    Z._+_ (Z._*_ (slack n) (CH.sourceQ n))
      (Z._*_ (Z.+_ 2) (Z._*_ (T.W n) (E.a n)))
slackSingle n rewrite E.prefixTStep n | E.prefixQStep n =
  zsolve 6
    (λ t q v w a b →
      (zk (Z.+_ 2) ⊗ ((t ⊗ q) ⊕ (w ⊗ a))) ⊕ (b ⊗ (v ⊗ q))
      ⊜ (((zk (Z.+_ 2) ⊗ t) ⊕ (b ⊗ v)) ⊗ q)
        ⊕ (zk (Z.+_ 2) ⊗ (w ⊗ a)))
    refl (E.T n) (CH.sourceQ n) (E.Q n) (T.W n) (E.a n) negA

twoPositive : T.Positive (Z.+_ 2)
twoPositive = T.pos 1 refl

evenSlack : (k : Nat) → T.Positive (slack (T.twice (suc k)))
evenSlack zero = T.pos 3568253353002313866541679 refl
evenSlack (suc k) rewrite slackPair (T.twice (suc k)) =
  T.nonnegativePlusPositive
    (T.positiveIsNonnegative
      (T.positiveTimesPositive
        (T.positiveTimesPositive (evenSlack k) (T.qPositive (T.twice (suc k))))
        (T.qPositive (suc (T.twice (suc k))))))
    (T.positiveTimesPositive twoPositive
      (T.positiveTimesPositive (T.evenWPositive (suc k))
        (T.pairGapPositive (T.twice (suc k)))))

oddSlack : (k : Nat) → T.Positive (slack (suc (T.twice k)))
oddSlack zero = T.pos 13591408 refl
oddSlack (suc k) rewrite slackSingle (T.twice (suc k)) =
  T.nonnegativePlusPositive
    (T.positiveIsNonnegative
      (T.positiveTimesPositive (evenSlack k) (T.qPositive (T.twice (suc k)))))
    (T.positiveTimesPositive twoPositive
      (T.positiveTimesPositive (T.evenWPositive (suc k))
        (T.weightPositive (T.twice (suc k)))))

nonemptyLowerPlane : (n : Nat) → T.Positive (slack (suc n))
nonemptyLowerPlane n with T.parity n
... | T.even k = oddSlack k
... | T.odd k = evenSlack k

-- Original radical numerator only; no approximate root identification.
radicalUpper : (k : Nat) → CH.rootNumerator k ≤ 101 * CH.rootScale k
radicalUpper k =
  let
    s = CH.rootScale k
    bound = NP.*-mono-≤
      (NP.*-mono-≤ (NP.m≤m+n 10005 196) NP.≤-refl) NP.≤-refl
    square = solve 1
      (λ x → con 10201 :* x :* x := (con 101 :* x) :* (con 101 :* x))
      refl s
  in Floor.squareOrderReflects
    (NP.≤-trans (CH.rootLowerSquare k)
      (NP.≤-trans bound (NP.≤-reflexive square)))

-- The existing literal cutoff satisfies k+5 <= 41 n.
cutoffExponent : (k : Nat) → suc (k + 4) ≤ CH.cutoff k * 41
cutoffExponent k = ND.m<suc[m/n]*n (k + 4) 41

-- A final finite width numerator consumer. Inputs are the original
-- positive cross residual J and two already established budgets.
widthNumeratorBudget :
  (dL tL tH R J : Nat) →
  426880 * dL ≤ tL →
  426880 * (R * J) ≤ 2 * (tL * tH) →
  426880 * (dL * tH + R * J) ≤ 3 * (tL * tH)
widthNumeratorBudget dL tL tH R J base tail =
  let
    left = solve 3
      (λ d t r → con 426880 :* (d :* t :+ r)
        := ((con 426880 :* d) :* t) :+ (con 426880 :* r))
      refl dL tH (R * J)
    right = solve 1 (λ x → x :+ (con 2 :* x) := con 3 :* x)
      refl (tL * tH)
  in NP.≤-trans (NP.≤-reflexive left)
    (NP.≤-trans (NP.+-mono-≤ (NP.*-mono-≤ base NP.≤-refl) tail)
      (NP.≤-reflexive right))
