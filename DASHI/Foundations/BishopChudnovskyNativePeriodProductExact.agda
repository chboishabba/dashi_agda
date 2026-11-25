module DASHI.Foundations.BishopChudnovskyNativePeriodProductExact where

-- SOURCE-WRITTEN, UNCOMPILED. The product of the actual native
-- Chudnovsky real and actual native factorial limit equals the
-- already-owned canonical square root times 426880, independently
-- of Machin pi. No inverse of an arbitrary constructive real used.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _^_)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
import Data.Nat.DivMod as ND
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
open import Relation.Nullary.Decidable.Core using (yes; no; from-yes)
import Data.Integer.Base as Z
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import Real as R
import RealProperties as RP
import Sequence as S
import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as Root
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyRationalOverlapExact as O
import DASHI.Foundations.BishopChudnovskyPairedTotalityExact as T
import DASHI.Foundations.BishopChudnovskyPrefixSemanticsExact as P
import DASHI.Foundations.BishopChudnovskyWindowNestingExact as W
import DASHI.Foundations.BishopChudnovskyWidthReflectionExact as Width
import DASHI.Foundations.BishopChudnovskyOverlapBudgetExact as B
import DASHI.Foundations.BishopChudnovskyNativeRealExact as C
import DASHI.Foundations.BishopChudnovskyNativeFactorialLimitExact as F
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Foundations.BishopChudnovskySignedCrossReflectionExact as X
import DASHI.Analysis.BishopPolynomialSuccessorFactorLimitExact as Const

-- Choose a cofinal synchronized chart, not a changed production cutoff.
-- At k=41*n the actual cutoff is precisely n+1.
stage : Nat → Nat
stage n = n * 41

stageGrow : (n : Nat) → n ≤ stage n
stageGrow n = NP.m≤m*n n 41

idxStage : (n : Nat) → W.idx (stage n) ≡ n
idxStage n =
  trans (ND.+-distrib-/ (stage n) 4 {41}
    (subst (λ r → r + (4 ND.% 41) N.< 41)
      (sym (ND.m*n%n≡0 n 41)) (from-yes (5 NP.≤? 41))))
    (trans (cong (λ x → x + (4 ND./ 41)) (ND.m*n/n≡m n 41))
      (NP.+-identityʳ n))

-- The actual sorted high view selects one of two original prefix
-- indices. Preserve the equality/touching branch of the source sort.
highIndex : Nat → Nat
highIndex n with (CH.num (W.v n) * CH.den (W.v (suc n))) NP.≤?
                 (CH.num (W.v (suc n)) * CH.den (W.v n))
... | yes _ = suc (suc n)
... | no _ = suc n

highGrow : (n : Nat) → n ≤ highIndex n
highGrow n with (CH.num (W.v n) * CH.den (W.v (suc n))) NP.≤?
                (CH.num (W.v (suc n)) * CH.den (W.v n))
... | yes _ = NP.≤-step (NP.≤-step NP.≤-refl)
... | no _ = NP.≤-step NP.≤-refl

highValue : (n : Nat) → F.s (highIndex n) Q.≃ P.viewFraction (W.highV n)
highValue n with (CH.num (W.v n) * CH.den (W.v (suc n))) NP.≤?
                 (CH.num (W.v (suc n)) * CH.den (W.v n))
... | yes _ = W.vEq (suc n)
... | no _ = W.vEq n

highQ : Nat → Q.ℚᵘ
highQ n = P.viewFraction (W.highV n)

highConverges : S._ConvergesTo_ (λ n → R._⋆ (highQ n)) F.seriesReal
highConverges = S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
  (λ n → RP.⋆-cong (highValue n))
  (F.seriesReal , F.sampleConverges F.seriesReal highIndex highGrow)

sqrtReal : R.ℝ
sqrtReal = Root.canonicalFloorSquareRootReal 10005

scaleGrow : (n : Nat) → n ≤ CH.rootScale (stage n)
scaleGrow n = NP.≤-trans (stageGrow n)
  (NP.≤-trans (NP.m≤m+n (stage n) 2)
    (NP.≤-trans (NP.≤-step NP.≤-refl)
      (B.dyadicDenominator (CH.rootBits (stage n)))))

rootQ : Nat → Q.ℚᵘ
rootQ n = R.seq sqrtReal (CH.rootScale (stage n))

rootConverges : S._ConvergesTo_ (λ n → R._⋆ (rootQ n)) sqrtReal
rootConverges = F.sampleConverges sqrtReal (λ n → CH.rootScale (stage n)) scaleGrow

lowerQ : Nat → Q.ℚᵘ
lowerQ n = C.L (stage n)

-- Native interval membership supplies a direct convergence bound,
-- not an appeal to a second analytic limit. All arithmetic is on
-- the original literal window and its existing dyadic width.
lowerError : (k : Nat) →
  R._≤_ (R.∣ R._-_ (R._⋆ (C.L k)) C.chudnovskyReal ∣)
       (R._⋆ (B.dyadic k))
lowerError k =
  let
    l = R._⋆ (C.L k)
    u = R._⋆ (C.U k)
    x = C.chudnovskyReal
    bound : R._≤_ (R._-_ x l) (R._⋆ (B.dyadic k))
    bound = RP.≤-trans
      (RP.+-mono-≤ (C.upperMember k) RP.≤-refl)
      (RP.≤-respˡ-≃ (RP.⋆-distrib-to-p⋆-q⋆ (C.U k) (C.L k))
        (RP.p≤q⇒p⋆≤q⋆ (B.literalWidth k) (B.dyadic k) (Width.literalWidthBound k)))
  in RP.≤-respˡ-≃ (RP.∣x-y∣≃∣y-x∣ x l)
    (RP.≤-respˡ-≃ (RP.≃-symm (RP.nonNegx⇒∣x∣≃x (C.lowerMember k))) bound)

lowerConverges : S._ConvergesTo_ (λ n → R._⋆ (lowerQ n)) C.chudnovskyReal
lowerConverges = S.con* λ { (suc k) →
  k , λ n h →
    RP.≤-trans (lowerError (stage n))
      (RP.p≤q⇒p⋆≤q⋆ (B.dyadic (stage n)) (Z.+_ 1 Q./ suc k)
        (C.dyadicBelowInv (suc k) (stage n) (NP.≤-trans h (stageGrow n)))) }

KQ : Q.ℚᵘ
KQ = Z.+_ 426880 Q./ 1

target : R.ℝ
target = R._*_ (R._⋆ KQ) sqrtReal

-- This identity clears only positive Nat denominators. It is the
-- literal lower reciprocal corner, not a new evaluator:
-- (426880*r*d/(s*t)) * (t/d) = 426880*(r/s).
cornerCancels : (sp r : Nat) (v : CH.PositiveSum) →
  (CH.endpoint sp r v Q.* P.viewFraction v) Q.≃
    (KQ Q.* (Z.+_ r Q./ suc sp))
cornerCancels sp r v@(CH.positiveSum a b) = Q.*≡*
  (cong Z.+_
    (solve 5 (λ k r s t d →
      (((k :* r :* d) :* t) :* (con 1 :* s))
      := ((k :* r) :* ((s :* t) :* d)))
      refl 426880 r (suc sp) (suc a) (suc b)))

actualCornerCancels : (n : Nat) →
  (lowerQ n Q.* highQ n) Q.≃ (KQ Q.* rootQ n)
actualCornerCancels n
  with T.successorWitness (CH.rootScale (stage n))
    (NP.m^n≢0 2 (CH.rootBits (stage n)))
... | sp , se
  rewrite W.windowEq (stage n) sp se | idxStage n | se =
  cornerCancels sp (CH.rootNumerator (stage n)) (W.highV n)

cornerProductsConverge :
  S._ConvergesTo_ (λ n → R._*_ (R._⋆ (lowerQ n)) (R._⋆ (highQ n)))
    (R._*_ C.chudnovskyReal F.seriesReal)
cornerProductsConverge = S.xₙyₙ→x₀y₀
  (C.chudnovskyReal , lowerConverges) (F.seriesReal , highConverges)

rootProductsConverge :
  S._ConvergesTo_ (λ n → R._*_ (R._⋆ KQ) (R._⋆ (rootQ n))) target
rootProductsConverge = S.xₙyₙ→x₀y₀
  (R._⋆ KQ , Const.constantSequenceConverges (R._⋆ KQ))
  (sqrtReal , rootConverges)

pointwiseProduct : (n : Nat) →
  R._≃_ (R._*_ (R._⋆ (lowerQ n)) (R._⋆ (highQ n)))
        (R._*_ (R._⋆ KQ) (R._⋆ (rootQ n)))
pointwiseProduct n =
  RP.≃-trans (RP.≃-symm (RP.⋆-distrib-* (lowerQ n) (highQ n)))
    (RP.≃-trans (RP.⋆-cong (actualCornerCancels n))
      (RP.⋆-distrib-* KQ (rootQ n)))

-- UNCONDITIONAL relative to the source-written arithmetic dependencies.
-- This is the actual native series-period product, not the assertion
-- that either real is Machin pi.
actualProduct : R._≃_ (R._*_ C.chudnovskyReal F.seriesReal) target
actualProduct = S.uniqueness-of-limits
  (S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ n → pointwiseProduct n)
    (R._*_ C.chudnovskyReal F.seriesReal , cornerProductsConverge))
  rootProductsConverge

-- Exact residual of the remaining classical modular-period theorem
-- on the native objects. A positive factorial sum licenses
-- cancellation by the original vendor reciprocal.
NativePeriod : Set
NativePeriod = R._≃_ (R._*_ M.bishopMachinPi F.seriesReal) target

sameRealToPeriod : R._≃_ C.chudnovskyReal M.bishopMachinPi → NativePeriod
sameRealToPeriod eq = RP.≃-trans (RP.*-congʳ (RP.≃-symm eq)) actualProduct

expandedToPeriod : ((k : Nat) → X.ExpandedCross k) → NativePeriod
expandedToPeriod e = sameRealToPeriod (C.expandedToSameReal e)
