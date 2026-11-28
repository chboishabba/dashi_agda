module DASHI.Foundations.BishopChudnovskyRationalOverlapExact where

-- Source-written; not kernel checked. All windows below are the actual
-- computed interval and actual original rational Machin stage.
-- Crossed endpoint inequalities remain analytic evidence, not axioms.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using
  (ℚᵘ; 0ℚᵘ; _/_; _+_; _-_; _*_; _≤_; _≃_; ∣_∣)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Binary.PropositionalEquality using (subst; sym)
import NonReflectiveQ as QS
import Real as R
import RealProperties as RP
import Sequence as S
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyPairedTotalityExact as Total
import DASHI.Foundations.BishopChudnovskySourceBoundLimitExact as Limit
import DASHI.Foundations.RationalDirectedDifferenceAbsoluteBoundExact as Directed
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Stage
import DASHI.Analysis.BishopMachinCrossEnvelopeBishopOrderExact as Rate
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Foundations.BishopMachinPiRationalWindowExact as MachinWindow

window : Nat → CH.Interval
window k = proj₁ (Total.intervalAtTotal k)

computed : (k : Nat) → CH.intervalAt k ≡ just (window k)
computed k = proj₂ (Total.intervalAtTotal k)

halfWidth : CH.Interval → ℚᵘ
halfWidth w = (+ 1 / 2) Q.* (CH.upper w Q.- CH.lower w)

-- Use the sharper existing Machin window at zero. The geometric 4
-- bound has no slack for any nonzero Chudnovsky radius at k=0.
machinRadius : Nat → ℚᵘ
machinRadius zero = MachinWindow.twentyTwoSevenths
machinRadius (suc k) = Rate.sourceGeometricRationalEnvelope (suc k)

machinRadiusSound : (k : Nat) →
  R._≤_ (R.∣ R._-_ M.bishopMachinPi (R._⋆ (Stage.qMachinStage k)) ∣)
        (R._⋆ (machinRadius k))
machinRadiusSound zero =
  let
    open RP.ℝ-Solver
    p = M.bishopMachinPi
    positiveP = RP.<-trans
      (RP.p<q⇒p⋆<q⋆ 0ℚᵘ MachinWindow.three
        (QP.positive⁻¹ MachinWindow.three))
      MachinWindow.threeBelowMachinPi
    diffZero : R._≃_ (R._-_ p (R._⋆ 0ℚᵘ)) p
    diffZero = solve 1 (λ p′ → p′ ⊖ Κ 0ℚᵘ ⊜ p′)
      RP.≃-refl p
  in RP.≤-respˡ-≃
    (RP.≃-symm
      (RP.≃-trans (RP.∣-∣-cong diffZero)
        (RP.nonNegx⇒∣x∣≃x (RP.0≤x⇒nonNegx (RP.<⇒≤ positiveP)))))
    MachinWindow.machinPiBelowTwentyTwoSeventhsNonStrict
machinRadiusSound (suc k) = Rate.machinActualCrossDenominatorFourOver25 (suc k)

-- No real trichotomy: two rational cross inequalities retain the
-- signed gap, including equality/touching. No chosen overlap point.
record Cross (w : CH.Interval) (m e : ℚᵘ) : Set where
  constructor cross
  field
    lowerCross : CH.lower w Q.≤ m Q.+ e
    upperCross : m Q.≤ CH.upper w Q.+ e
open Cross

lowerPlusHalf : (w : CH.Interval) →
  (CH.lower w Q.+ halfWidth w) Q.≃ CH.midpoint w
lowerPlusHalf w =
  let open QS in
  solve 2 (λ l u → l ⊕ (Κ (+ 1 / 2) ⊗ (u ⊖ l))
                    ⊜ Κ (+ 1 / 2) ⊗ (l ⊕ u))
    QP.≃-refl (CH.lower w) (CH.upper w)

centerPlusHalf : (w : CH.Interval) →
  (CH.midpoint w Q.+ halfWidth w) Q.≃ CH.upper w
centerPlusHalf w =
  let open QS in
  solve 2 (λ l u → (Κ (+ 1 / 2) ⊗ (l ⊕ u))
                   ⊕ (Κ (+ 1 / 2) ⊗ (u ⊖ l)) ⊜ u)
    QP.≃-refl (CH.lower w) (CH.upper w)

radius : CH.Interval → ℚᵘ → ℚᵘ
radius w e = halfWidth w Q.+ e

-- Both directed errors have the same sharp radius. Reuse the existing
-- directed difference theorem with its unused side set to ZERO,
-- rather than summing two copies of the radius.
oneSided : ∀ {x y b : ℚᵘ} →
  x Q.≤ y Q.+ b → (x Q.- y) Q.≤ b
oneSided {x} {y} {b} h =
  QP.≤-respʳ-≃ (QP.+-identityˡ b)
    (Directed.differenceUpperFromRight {x = x} {y = y}
      {leftError = 0ℚᵘ} {rightError = b} h)

sharpAbs : ∀ {x y b : ℚᵘ} →
  (x Q.- y) Q.≤ b → (y Q.- x) Q.≤ b →
  Q.∣ x Q.- y ∣ Q.≤ b
sharpAbs {x} {y} {b} xy yx with QP.∣p∣≡p∨∣p∣≡-p (x Q.- y)
... | inj₁ p = subst (λ v → v Q.≤ b) (sym p) xy
... | inj₂ p = subst (λ v → v Q.≤ b) (sym p)
  (QP.≤-respˡ-≃ (QP.≃-sym (Directed.negDifferenceEquivalentReverse x y)) yx)

crossSharpError : (w : CH.Interval) (m e : ℚᵘ) →
  Cross w m e → Q.∣ CH.midpoint w Q.- m ∣ Q.≤ radius w e
crossSharpError w m e c =
  let
    open QS
    h = halfWidth w
    l = CH.lower w
    u = CH.upper w
    x = CH.midpoint w
    lowerRearrange : ((m Q.+ e) Q.+ h) Q.≃ (m Q.+ radius w e)
    lowerRearrange = solve 3
      (λ m′ e′ h′ → (m′ ⊕ e′) ⊕ h′ ⊜ m′ ⊕ (h′ ⊕ e′))
      QP.≃-refl m e h
    upperRearrange : (u Q.+ e) Q.≃ (x Q.+ radius w e)
    upperRearrange = QP.≃-trans
      (QP.+-cong (QP.≃-sym (centerPlusHalf w)) QP.≃-refl)
      (QP.+-assoc x h e)
    xBound : x Q.≤ m Q.+ radius w e
    xBound = QP.≤-respʳ-≃ lowerRearrange
      (QP.≤-respˡ-≃ (lowerPlusHalf w)
        (QP.+-monoˡ-≤ h (lowerCross c)))
    mBound : m Q.≤ x Q.+ radius w e
    mBound = QP.≤-respʳ-≃ upperRearrange (upperCross c)
  in sharpAbs (oneSided xBound) (oneSided mBound)

-- Native interval membership implies the crossed rational inequalities
-- by the EXISTING bidirectional rational-order reflection.
moveDifference : (a b e : R.ℝ) →
  R._≤_ (R._-_ a b) e → R._≤_ a (R._+_ b e)
moveDifference a b e d =
  let open RP.ℝ-Solver in
  RP.≤-respˡ-≃
    (solve 2 (λ a′ b′ → b′ ⊕ (a′ ⊖ b′) ⊜ a′)
      RP.≃-refl a b)
    (RP.+-monoʳ-≤ b d)

nativeMembershipToCross : (k : Nat) →
  R._≤_ (R._⋆ (CH.lower (window k))) M.bishopMachinPi →
  R._≤_ M.bishopMachinPi (R._⋆ (CH.upper (window k))) →
  Cross (window k) (Stage.qMachinStage k) (machinRadius k)
nativeMembershipToCross k lo hi =
  let
    w = window k
    m = Stage.qMachinStage k
    e = machinRadius k
    p = M.bishopMachinPi
    mr = R._⋆ m
    er = R._⋆ e
    pm : R._≤_ (R._-_ p mr) er
    pm = RP.≤-trans RP.x≤∣x∣ (machinRadiusSound k)
    mp : R._≤_ (R._-_ mr p) er
    mp = RP.≤-trans RP.x≤∣x∣
      (RP.≤-respˡ-≃ (RP.∣x-y∣≃∣y-x∣ p mr) (machinRadiusSound k))
    pUpper = moveDifference p mr er pm
    mUpper = moveDifference mr p er mp
    lCross = RP.p⋆≤q⋆⇒p≤q (CH.lower w) (m Q.+ e)
      (RP.≤-respʳ-≃ (RP.≃-symm (RP.⋆-distrib-+ m e))
        (RP.≤-trans lo pUpper))
    uCross = RP.p⋆≤q⋆⇒p≤q m (CH.upper w Q.+ e)
      (RP.≤-respʳ-≃ (RP.≃-symm (RP.⋆-distrib-+ (CH.upper w) e))
        (RP.≤-trans mUpper (RP.+-monoˡ-≤ er hi)))
  in cross lCross uCross

-- This is the actual endpoint consumer. The remaining input is two
-- crossed rational inequalities and a source-width/rate budget, not
-- an arbitrary sequence or an asserted common real.
stageFromCross : (k : Nat) →
  Cross (window k) (Stage.qMachinStage k) (machinRadius k) →
  radius (window k) (machinRadius k) Q.≤ Limit.errorQ k →
  Limit.StageCertificate k
stageFromCross k c b = record
  { window = window k
  ; computed = computed k
  ; rationalError = QP.≤-trans
      (crossSharpError (window k) (Stage.qMachinStage k) (machinRadius k) c)
      b
  }

literalConvergenceFromCross :
  (c : ∀ k → Cross (window k) (Stage.qMachinStage k) (machinRadius k)) →
  (b : ∀ k → radius (window k) (machinRadius k) Q.≤ Limit.errorQ k) →
  S._ConvergesTo_ (λ k → R._⋆ (CH.midpoint (window k))) M.bishopMachinPi
literalConvergenceFromCross c b =
  Limit.literalMidpointsConvergeToOriginalMachin (λ k → stageFromCross k (c k) (b k))
