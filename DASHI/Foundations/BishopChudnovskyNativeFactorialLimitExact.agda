module DASHI.Foundations.BishopChudnovskyNativeFactorialLimitExact where

-- SOURCE-WRITTEN, UNCOMPILED. Construct the actual weighted factorial
-- series limit independently of either pi real or a modular identity.
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _^_)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
open import Data.Empty using (⊥-elim)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
import Data.Integer.Base as Z
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import NonReflectiveQ as QS
import Real as R
import RealProperties as RP
import Sequence as S
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyIndexedEdgeAlgebraExact as E
import DASHI.Foundations.BishopChudnovskyPositiveGapExact as G
import DASHI.Foundations.BishopChudnovskyWidthSourceExact as D
import DASHI.Foundations.BishopChudnovskyWidthReflectionExact as W
import DASHI.Foundations.BishopChudnovskyPrefixSemanticsExact as P
import DASHI.Foundations.BishopChudnovskyAdjacentNestingExact as A
import DASHI.Foundations.BishopChudnovskyWindowNestingExact as Nests
import DASHI.Foundations.BishopChudnovskyFactorialSourceExact as F
import DASHI.Foundations.BishopChudnovskyOverlapBudgetExact as B
import DASHI.Foundations.BishopChudnovskyNativeRealExact as C
import DASHI.Foundations.BishopChudnovskyRationalOverlapExact as O
import DASHI.Foundations.RationalDirectedDifferenceAbsoluteBoundExact as Directed
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as Order
import DASHI.Foundations.BishopRegularRationalApproximationExact as Regular

s : Nat → Q.ℚᵘ
s = P.rawSum

edge : Nat → Q.ℚᵘ
edge n = P.frac (E.delta n) (G.qProduct (suc n)) (G.qProductNonZero (suc n))

edgeAdd : (n : Nat) → s (suc n) Q.≃ (s n Q.+ edge n)
edgeAdd n rewrite E.prefixTStep n | G.sourceQNatural n =
  P.fracAddEdge (E.T n) (E.delta n) (G.qProduct n) (G.qNat n)
    (G.qProductNonZero n) (G.qNatNonZero n)

edgeDifference : (n : Nat) → (s (suc n) Q.- s n) Q.≃ edge n
edgeDifference n = QP.≃-trans
  (QP.+-cong (edgeAdd n) QP.≃-refl)
  (let open QS in solve 2 (λ x y → (x ⊕ y) ⊖ x ⊜ y)
    QP.≃-refl (s n) (edge n))

absFrac : (a : Z.ℤ) (d : Nat) (nz : N.NonZero d) →
  Q.∣ P.frac a d nz ∣ Q.≃ P.frac (Z.+_ Z.∣ a ∣) d nz
absFrac a zero nz = ⊥-elim (N.≢-nonZero⁻¹ zero {{nz}} refl)
absFrac (Z.+_ a) (suc d) nz = QP.≃-refl
absFrac (Z.-[1+_] a) (suc d) nz = QP.≃-refl

edgeMagnitude : (n : Nat) →
  Q.∣ s (suc n) Q.- s n ∣ Q.≃
  P.frac (Z.+_ (D.H n)) (G.qProduct (suc n)) (G.qProductNonZero (suc n))
edgeMagnitude n = QP.≃-trans (QP.∣-∣-cong (edgeDifference n))
  (QP.≃-trans (absFrac (E.delta n) (G.qProduct (suc n)) (G.qProductNonZero (suc n)))
    (subst (λ h → P.frac (Z.+_ Z.∣ E.delta n ∣)
      (G.qProduct (suc n)) (G.qProductNonZero (suc n)) Q.≃
      P.frac (Z.+_ h) (G.qProduct (suc n)) (G.qProductNonZero (suc n)))
      (D.hIsOriginalDefectMagnitude n) QP.≃-refl))

edgeBudget : (n : Nat) → Q.ℚᵘ
edgeBudget n = P.frac (Z.+_ CH.A) (D.M ^ n) (NP.m^n≢0 D.M n)

edgeBound : (n : Nat) → Q.∣ s (suc n) Q.- s n ∣ Q.≤ edgeBudget n
edgeBound n = QP.≤-respˡ-≃ (QP.≃-sym (edgeMagnitude n))
  (A.fracOrder (Z.+_ (D.H n)) (Z.+_ CH.A)
    (G.qProduct (suc n)) (D.M ^ n)
    (G.qProductNonZero (suc n)) (NP.m^n≢0 D.M n)
    (Z.+≤+ (W.move (NP.*-comm (D.H n) (D.M ^ n)) refl (D.scaledDefectBound n))))

-- The positive series gap is tiny: A/M^n <= 1/n for every n>=1.
positiveBudget : (n : Nat) → CH.A * suc n ≤ D.M ^ suc n
positiveBudget n = NP.*-mono-≤
  (NP.m≤m+n CH.A 2199009664143)
  (NP.≤-trans (B.dyadicDenominator n)
    (NP.^-monoˡ-≤ (NP.m≤m+n 2 2199023255550)))

budgetInv : (n : Nat) → edgeBudget (suc n) Q.≤ (Z.+_ 1 Q./ suc n)
budgetInv n = A.fracOrder (Z.+_ CH.A) (Z.+_ 1)
  (D.M ^ suc n) (suc n) (NP.m^n≢0 D.M (suc n)) N.nonZero
  (Z.+≤+ (W.move refl (NP.*-identityˡ (D.M ^ suc n)) (positiveBudget n)))

lo hi : Nat → Q.ℚᵘ
lo = A.lower
hi = A.upper

-- No real trichotomy. Rational sign cases only, at the actual source
-- edge. The sorted interval width equals its unsigned signed defect.
widthEq : (n : Nat) → (hi n Q.- lo n) Q.≃ Q.∣ s (suc n) Q.- s n ∣
widthEq n with QP.≤-total (s n) (s (suc n))
... | inj₁ h =
  QP.≃-trans
    (QP.+-cong (QP.p≤q⇒p⊔q≃q h) (QP.neg-cong (QP.p≤q⇒p⊓q≃p h)))
    (QP.≃-sym (QP.0≤p⇒∣p∣≃p (QP.p≤q⇒0≤q-p h)))
... | inj₂ h =
  QP.≃-trans
    (QP.+-cong (QP.p≥q⇒p⊔q≃p h) (QP.neg-cong (QP.p≥q⇒p⊓q≃q h)))
    (QP.≃-trans
      (QP.≃-sym (QP.0≤p⇒∣p∣≃p (QP.p≤q⇒0≤q-p h)))
      (QP.≃-trans
        (QP.∣-∣-cong (QP.≃-sym (Directed.negDifferenceEquivalentReverse (s (suc n)) (s n))))
        (QP.∣-p∣≃∣p∣ (s (suc n) Q.- s n))))

widthBound : (n : Nat) → (hi (suc n) Q.- lo (suc n)) Q.≤ (Z.+_ 1 Q./ suc n)
widthBound n = QP.≤-trans (QP.≤-reflexive (widthEq (suc n)))
  (QP.≤-trans (edgeBound (suc n)) (budgetInv n))

inside : (n m : Nat) → n ≤ m → (lo n Q.≤ s m) × (s m Q.≤ hi n)
inside n m h =
  QP.≤-trans (Nests.lowerMono′ (NP.≤⇒≤′ h)) (QP.p⊓q≤p (s m) (s (suc m))) ,
  QP.≤-trans (QP.p≤p⊔q (s m) (s (suc m))) (Nests.upperAnti′ (NP.≤⇒≤′ h))

distance : (n p q : Nat) → n ≤ p → n ≤ q →
  Q.∣ s p Q.- s q ∣ Q.≤ (hi n Q.- lo n)
distance n p q hp hq with inside n p hp | inside n q hq
... | lp , pu | lq , qu =
  O.sharpAbs (C.differenceBound pu lq) (C.differenceBound qu lp)

regularSeries : (m n : Nat) → .{{_ : N.NonZero m}} → .{{_ : N.NonZero n}} →
  Q.∣ s m Q.- s n ∣ Q.≤ ((Z.+_ 1 Q./ m) Q.+ (Z.+_ 1 Q./ n))
regularSeries zero n {{nz}} = ⊥-elim (N.≢-nonZero⁻¹ zero {{nz}} refl)
regularSeries (suc m) zero {{_}} {{nz}} = ⊥-elim (N.≢-nonZero⁻¹ zero {{nz}} refl)
regularSeries (suc m) (suc n) with NP.≤-total (suc m) (suc n)
... | inj₁ h = QP.≤-trans (distance (suc m) (suc m) (suc n) NP.≤-refl h)
  (QP.≤-trans (widthBound m) (C.invSumLeft (suc m) (suc n)))
... | inj₂ h = QP.≤-trans (distance (suc n) (suc m) (suc n) h NP.≤-refl)
  (QP.≤-trans (widthBound n) (C.invSumRight (suc m) (suc n)))

seriesRegular : Regular.BishopRegularRationalApproximation
seriesRegular = record { approximation = s ; regular = regularSeries }

seriesReal : R.ℝ
seriesReal = Regular.realizeRegularApproximation seriesRegular

seriesPositive : R.Positive seriesReal
seriesPositive = R.pos* (zero , Q.*<* (Z.+<+ (NP.m≤m+n 2 13591407)))

-- The actual sequence is the original prefix including n=0. The
-- vendor's 1/n approximation lemma gives convergence at positive n.
sampleConverges : (x : R.ℝ) (f : Nat → Nat) →
  ((n : Nat) → n ≤ f n) →
  S._ConvergesTo_ (λ n → R._⋆ (R.seq x (f n))) x
sampleConverges x f grow = S.con* λ { (suc k) →
  k , λ n h →
    sampleBound x (suc k) (f n) (NP.≤-trans h (grow n)) }}
  where
  sampleBound : (x : R.ℝ) (k j : Nat) → .{{_ : N.NonZero k}} →
    k ≤ j → R._≤_ (R.∣ R._-_ (R._⋆ (R.seq x j)) x ∣) (R._⋆ (Z.+_ 1 Q./ k))
  sampleBound x zero j {{nz}} h = ⊥-elim (N.≢-nonZero⁻¹ zero {{nz}} refl)
  sampleBound x (suc k) zero ()
  sampleBound x (suc k) (suc j) h = RP.≤-trans
    (RP.≤-respˡ-≃ (RP.∣x-y∣≃∣y-x∣ x (R._⋆ (R.seq x (suc j))))
      (RP.lemma-2-14 x (suc j)))
    (RP.p≤q⇒p⋆≤q⋆ (Z.+_ 1 Q./ suc j) (Z.+_ 1 Q./ suc k)
      (Order.natFractionLe (NP.*-mono-≤ NP.≤-refl h)))

seriesConverges : S._ConvergesTo_ (λ n → R._⋆ (s n)) seriesReal
seriesConverges = sampleConverges seriesReal (λ n → n) (λ n → NP.≤-refl)

factorialConverges : S._ConvergesTo_ (λ n → R._⋆ (F.factorialPrefix n)) seriesReal
factorialConverges = S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
  (λ n → RP.⋆-cong (F.sumFactorial n)) (seriesReal , seriesConverges)
