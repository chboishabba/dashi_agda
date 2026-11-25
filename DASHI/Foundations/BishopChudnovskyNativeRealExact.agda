module DASHI.Foundations.BishopChudnovskyNativeRealExact where

-- SOURCE-WRITTEN, UNCOMPILED. Construct the original Bishop real
-- directly from the literal nested windows and width. The classical
-- analytic equality is NOT assumed in constructing this real.
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (refl)
open import Data.Nat.Base using (_≤_; _^_)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
open import Data.Empty using (⊥-elim)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Integer.Base using (+_)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import NonReflectiveQ as QS
import Real as R
import RealProperties as RP
import Sequence as S
import DASHI.Foundations.BishopRegularRationalApproximationExact as Regular
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as F
import DASHI.Foundations.RationalDirectedDifferenceAbsoluteBoundExact as Directed
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyRationalOverlapExact as O
import DASHI.Foundations.BishopChudnovskyOverlapBudgetExact as B
import DASHI.Foundations.BishopChudnovskyWidthReflectionExact as W
import DASHI.Foundations.BishopChudnovskyWindowNestingExact as Nests
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Stage
import DASHI.Foundations.BishopChudnovskyCrossOnlyEndpointExact as End
import DASHI.Foundations.BishopChudnovskySignedCrossReflectionExact as X

L U mid : Nat → Q.ℚᵘ
L k = CH.lower (O.window k)
U k = CH.upper (O.window k)
mid k = CH.midpoint (O.window k)

widthNonnegative : (k : Nat) → Q.0ℚᵘ Q.≤ B.literalWidth k
widthNonnegative k = QP.p≤q⇒0≤q-p (Nests.windowOrdered k)

halfDouble : (q : Q.ℚᵘ) → ((+ 1 Q./ 2) Q.* (q Q.+ q)) Q.≃ q
halfDouble q = let open QS in
  solve 1 (λ x → Κ (+ 1 Q./ 2) ⊗ (x ⊕ x) ⊜ x) QP.≃-refl q

midInside : (k : Nat) → (L k Q.≤ mid k) × (mid k Q.≤ U k)
midInside k =
  QP.≤-respˡ-≃ (halfDouble (L k))
    (QP.*-monoʳ-≤-nonNeg (+ 1 Q./ 2)
      (QP.+-mono-≤ QP.≤-refl (Nests.windowOrdered k))) ,
  QP.≤-respʳ-≃ (halfDouble (U k))
    (QP.*-monoʳ-≤-nonNeg (+ 1 Q./ 2)
      (QP.+-mono-≤ (Nests.windowOrdered k) QP.≤-refl))

insideEarlier : (k j : Nat) → k ≤ j →
  (L k Q.≤ mid j) × (mid j Q.≤ U k)
insideEarlier k j h with midInside j
... | lo , hi =
  QP.≤-trans (Nests.windowLowerMono (NP.≤⇒≤′ h)) lo ,
  QP.≤-trans hi (Nests.windowUpperAnti (NP.≤⇒≤′ h))

differenceBound : ∀ {p q l u : Q.ℚᵘ} →
  p Q.≤ u → l Q.≤ q → (p Q.- q) Q.≤ (u Q.- l)
differenceBound pu lq = QP.+-mono-≤ pu (QP.neg-mono-≤ lq)

insideDistance : (k : Nat) (p q : Q.ℚᵘ) →
  L k Q.≤ p → p Q.≤ U k → L k Q.≤ q → q Q.≤ U k →
  Q.∣ p Q.- q ∣ Q.≤ B.literalWidth k
insideDistance k p q lp pu lq qu =
  O.sharpAbs (differenceBound pu lq) (differenceBound qu lp)

-- For every positive n ≤ k, 2^k ≥ k+1 ≥ n.
dyadicBelowInv : (n k : Nat) → .{{_ : N.NonZero n}} →
  n ≤ k → B.dyadic k Q.≤ (+ 1 Q./ n)
dyadicBelowInv n k h =
  let instance nz = NP.m^n≢0 2 k in
  F.natFractionLe (NP.*-mono-≤ NP.≤-refl
    (NP.≤-trans h (NP.≤-trans (NP.≤-step NP.≤-refl) (B.dyadicDenominator k))))

invNN : (n : Nat) → .{{_ : N.NonZero n}} → Q.0ℚᵘ Q.≤ (+ 1 Q./ n)
invNN zero {{nz}} = ⊥-elim (N.≢-nonZero⁻¹ zero {{nz}} refl)
invNN (suc n) = QP.nonNegative⁻¹ _

invSumLeft : (m n : Nat) → .{{_ : N.NonZero m}} → .{{_ : N.NonZero n}} →
  (+ 1 Q./ m) Q.≤ ((+ 1 Q./ m) Q.+ (+ 1 Q./ n))
invSumLeft m n =
  QP.≤-respˡ-≃ (QP.+-identityʳ (+ 1 Q./ m))
    (QP.+-monoʳ-≤ (+ 1 Q./ m) (invNN n))

invSumRight : (m n : Nat) → .{{_ : N.NonZero m}} → .{{_ : N.NonZero n}} →
  (+ 1 Q./ n) Q.≤ ((+ 1 Q./ m) Q.+ (+ 1 Q./ n))
invSumRight m n =
  QP.≤-respʳ-≃ (QP.+-comm (+ 1 Q./ n) (+ 1 Q./ m)) (invSumLeft n m)

regularMidpoints : (m n : Nat) → .{{_ : N.NonZero m}} → .{{_ : N.NonZero n}} →
  Q.∣ mid m Q.- mid n ∣ Q.≤ ((+ 1 Q./ m) Q.+ (+ 1 Q./ n))
regularMidpoints m n with NP.≤-total m n
... | inj₁ le with midInside m | insideEarlier m n le
... | lm , mu | ln , nu =
  QP.≤-trans (insideDistance m (mid m) (mid n) lm mu ln nu)
    (QP.≤-trans (W.literalWidthBound m)
      (QP.≤-trans (dyadicBelowInv m m NP.≤-refl) (invSumLeft m n)))
regularMidpoints m n | inj₂ le with insideEarlier n m le | midInside n
... | lm , mu | ln , nu =
  QP.≤-trans (insideDistance n (mid m) (mid n) lm mu ln nu)
    (QP.≤-trans (W.literalWidthBound n)
      (QP.≤-trans (dyadicBelowInv n n NP.≤-refl) (invSumRight m n)))

actualRegular : Regular.BishopRegularRationalApproximation
actualRegular = record { approximation = mid ; regular = regularMidpoints }

-- This is literally the existing vendored Real.mkℝ constructor.
-- It is not a replacement real carrier, and does not yet assert pi.
chudnovskyReal : R.ℝ
chudnovskyReal = Regular.realizeRegularApproximation actualRegular

-- The gap to a fixed window is at most the width of the CURRENT
-- window even when the current index is earlier. This removes any
-- eventual-order/limit axiom from native membership.
lowerGap : (k j : Nat) → (L k Q.- mid j) Q.≤ B.literalWidth j
lowerGap k j with NP.≤-total k j
... | inj₁ le with insideEarlier k j le
... | lo , hi = QP.≤-trans (QP.p≤q⇒p-q≤0 lo) (widthNonnegative j)
lowerGap k j | inj₂ le with midInside j
... | lo , hi = differenceBound
  (QP.≤-trans (Nests.windowOrdered k) (Nests.windowUpperAnti (NP.≤⇒≤′ le))) lo

upperGap : (k j : Nat) → (mid j Q.- U k) Q.≤ B.literalWidth j
upperGap k j with NP.≤-total k j
... | inj₁ le with insideEarlier k j le
... | lo , hi = QP.≤-trans (QP.p≤q⇒p-q≤0 hi) (widthNonnegative j)
upperGap k j | inj₂ le with midInside j
... | lo , hi = differenceBound hi
  (QP.≤-trans (Nests.windowLowerMono (NP.≤⇒≤′ le)) (Nests.windowOrdered k))

twiceBound : (n : Nat) → n ≤ 2 * n
twiceBound n = subst (λ x → x ≤ 2 * n) (NP.*-identityˡ n)
  (NP.*-mono-≤ (NP.≤-step NP.≤-refl) NP.≤-refl)

-- The pinned Bishop order is NonNegative (y-x), evaluated at 2*n
-- by the original real addition. The exact rational width pays the
-- original 1/n allowance directly, including every positive n.
lowerMember : (k : Nat) → R._≤_ (R._⋆ (L k)) chudnovskyReal
lowerMember k = R.nonNeg* λ n {n≢0} →
  let instance nz = N.≢-nonZero n≢0
      j = 2 * n
      h = QP.≤-trans (lowerGap k j)
        (QP.≤-trans (W.literalWidthBound j) (dyadicBelowInv n j (twiceBound n)))
  in QP.≤-respʳ-≃ (Directed.negDifferenceEquivalentReverse (L k) (mid j))
       (QP.neg-mono-≤ h)

upperMember : (k : Nat) → R._≤_ chudnovskyReal (R._⋆ (U k))
upperMember k = R.nonNeg* λ n {n≢0} →
  let instance nz = N.≢-nonZero n≢0
      j = 2 * n
      h = QP.≤-trans (upperGap k j)
        (QP.≤-trans (W.literalWidthBound j) (dyadicBelowInv n j (twiceBound n)))
  in QP.≤-respʳ-≃ (Directed.negDifferenceEquivalentReverse (mid j) (U k))
       (QP.neg-mono-≤ h)

-- Original RealProperties.lemma-2-14 bounds distance to the embedded
-- n-th rational term by 1/n. Use the literal convergence constructor.
nativeConverges : S._ConvergesTo_ (λ n → R._⋆ (mid n)) chudnovskyReal
nativeConverges = S.con* λ { (suc k) →
  k , λ { zero () ; (suc n) h →
    RP.≤-trans
      (RP.≤-respˡ-≃
        (RP.∣x-y∣≃∣y-x∣ chudnovskyReal (R._⋆ (mid (suc n))))
        (RP.lemma-2-14 chudnovskyReal (suc n)))
      (RP.p≤q⇒p⋆≤q⋆ (+ 1 Q./ suc n) (+ 1 Q./ suc k)
        (F.natFractionLe (NP.*-mono-≤ NP.≤-refl h))) }}

-- BIDI terminal: the only additional mathematical input is the
-- equality of the two ACTUAL Bishop reals. No cofinal overlap or
-- Machin nesting hypothesis is required by this route.
AllCross : Set
AllCross = (k : Nat) → O.Cross (O.window k) (Stage.qMachinStage k) (O.machinRadius k)

sameRealToCross : R._≃_ chudnovskyReal M.bishopMachinPi → AllCross
sameRealToCross eq k = O.nativeMembershipToCross k
  (RP.≤-respʳ-≃ eq (lowerMember k))
  (RP.≤-respˡ-≃ eq (upperMember k))

crossToSameReal : AllCross → R._≃_ chudnovskyReal M.bishopMachinPi
crossToSameReal c =
  S.uniqueness-of-limits nativeConverges (End.literalConvergenceFromCrossOnly c)

sameRealToExpanded : R._≃_ chudnovskyReal M.bishopMachinPi →
  (k : Nat) → X.ExpandedCross k
sameRealToExpanded eq k = X.crossToExpanded k (X.fromCross k (sameRealToCross eq k))

expandedToSameReal : ((k : Nat) → X.ExpandedCross k) →
  R._≃_ chudnovskyReal M.bishopMachinPi
expandedToSameReal c = crossToSameReal (λ k → X.toCross k (X.expandedToCross k (c k)))
