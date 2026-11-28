module DASHI.Physics.YangMills.YMClayCMP102OriginalOuterWingsClosedExact where

-- Actual signed complement -> positive filtered cells -> original factorial
-- mass -> both original outer wings -> original represented scalar G=0.
-- SOURCE WRITTEN ONLY. Native Agda safe acceptance remains mandatory.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base as N using (_≤_; z≤n; s≤s; _∸_)
import Data.Nat.Properties as NP
open import Relation.Nullary using (yes; no)
open import Data.Product using (_,_)
open import Data.Rational.Unnormalised using (0ℚᵘ)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Foundations.BishopFiniteShiftedTriangleComplementExact as Comp
import DASHI.Foundations.BishopFiniteFilteredCellSumExact as Mask
import DASHI.Foundations.BishopFiniteSeriesShiftScaleExact as Scale
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFiniteSeriesAbsoluteBoundExact as Abs
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as Order
import DASHI.Foundations.BishopFiniteCauchyWeightedPowerExact as Power
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rect
import DASHI.Physics.YangMills.BalabanCMP109BishopRootFreeSeriesExact as CMP
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.YMClayCMP102OriginalFilteredRectangleMassExact as Mass
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact as Tail
import DASHI.Physics.YangMills.YMClayCMP102OriginalTwoOuterWingsToLimitExact as Two
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original

signedCell : (Nat → R.ℝ) → R.ℝ → Nat → Nat → Nat → R.ℝ
signedCell a X s i j =
  R._*_ (R._*_ (R.pow X s) (CMP.term a X i)) (CMP.term a X j)

signedRow : (Nat → R.ℝ) → R.ℝ → Nat → Nat → Nat → Nat → R.ℝ
signedRow a X s k height i =
  Seq.SeriesOf (Mask.masked (λ j → k ≤ i + j)
    (λ j → k NP.≤? (i + j)) (signedCell a X s i)) height

signedRectangle : (Nat → R.ℝ) → R.ℝ → Nat → Nat → Nat → R.ℝ
signedRectangle a X s k height =
  Seq.SeriesOf (signedRow a X s k height) height

scaledAfterCell : ∀ a X s k i j →
  R._≃_
    (R._*_ (R._*_ (R.pow X s) (CMP.term a X i))
      (Comp.after (k ∸ i) (CMP.term a X) j))
    (Mask.masked (λ j′ → k ≤ i + j′)
      (λ j′ → k NP.≤? (i + j′)) (signedCell a X s i) j)
scaledAfterCell a X s k i j with k NP.≤? (i + j)
... | yes h = P.*-congˡ (Comp.afterSelected (k ∸ i)
  (CMP.term a X) j (Comp.cutToRow k i j h))
... | no h =
  P.≃-trans
    (P.*-congˡ (Comp.afterRejected (k ∸ i) (CMP.term a X) j
      (λ p → h (Comp.rowToCut k i j p))))
    (let open P.ℝ-Solver in
      solve 1 (λ z → z ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl
        (R._*_ (R.pow X s) (CMP.term a X i)))

scaledWingIsSignedRectangle : ∀ a X s k height → k ≤ height →
  R._≃_
    (R._*_ (R.pow X s)
      (R._-_ (Rect.rectangleSum (CMP.term a X) (CMP.term a X) height height)
        (Row.trianglePartial (CMP.term a X) (CMP.term a X) k)))
    (signedRectangle a X s k height)
scaledWingIsSignedRectangle a X s k height h =
  let z = R.pow X s
      f = CMP.term a X
      r = λ i → R._*_ (f i) (Seq.SeriesOf (Comp.after (k ∸ i) f) height)
  in P.≃-trans (P.*-congˡ (Comp.originalTriangleComplement f f k height h))
    (P.≃-trans (P.≃-symm (Scale.finiteSeriesScale z r height))
      (Ext.finiteSumCongruent
        (λ i →
          let u = Seq.SeriesOf (Comp.after (k ∸ i) f) height
              open P.ℝ-Solver
          in P.≃-trans
            (solve 3 (λ z x u → z ⊗ (x ⊗ u) ⊜ (z ⊗ x) ⊗ u)
              P.≃-refl z (f i) u)
            (P.≃-trans
              (P.≃-symm (Scale.finiteSeriesScale (R._*_ z (f i))
                (Comp.after (k ∸ i) f) height))
              (Ext.finiteSumCongruent (scaledAfterCell a X s k i) height)))
        height))

termAbsolutePower : ∀ a X i → R.NonNegative (a i) →
  R._≃_ (R.∣ CMP.term a X i ∣) (R._*_ (a i) (R.pow (R.∣ X ∣) i))
termAbsolutePower a X i h =
  P.≃-trans (CMP.termAbs a X i h) (P.*-congˡ (Seq.∣xⁿ∣≃∣x∣ⁿ X i))

signedCellAbsolute : ∀ a X s i j →
  (∀ n → R.NonNegative (a n)) →
  R._≃_ (R.∣ signedCell a X s i j ∣)
    (R._*_ (R._*_ (a i) (a j)) (R.pow (R.∣ X ∣) (s + (i + j))))
signedCellAbsolute a X s i j an =
  let z = R.pow X s
      f = CMP.term a X
      u = R.∣ X ∣
      p = R.pow u s
      v = R.pow u i
      w = R.pow u j
      open P.ℝ-Solver
  in P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ (R._*_ z (f i)) (f j))
    (P.≃-trans
      (P.*-cong (P.∣x*y∣≃∣x∣*∣y∣ z (f i)) (termAbsolutePower a X j (an j)))
      (P.≃-trans
        (P.*-cong
          (P.*-cong (Seq.∣xⁿ∣≃∣x∣ⁿ X s) (termAbsolutePower a X i (an i)))
          P.≃-refl)
        (P.≃-trans
          (solve 5 (λ p a v b w → (p ⊗ (a ⊗ v)) ⊗ (b ⊗ w)
            ⊜ (a ⊗ b) ⊗ (p ⊗ (v ⊗ w)))
            P.≃-refl p (a i) v (a j) w)
          (P.*-congˡ (P.≃-symm
            (P.≃-trans (Power.bishopPowerAddition u s (i + j))
              (P.*-congˡ (Power.bishopPowerAddition u i j))))))))

maskedCellAbsolute : ∀ a X s k i j →
  (∀ n → R.NonNegative (a n)) →
  R._≃_
    (R.∣ Mask.masked (λ j′ → k ≤ i + j′)
      (λ j′ → k NP.≤? (i + j′)) (signedCell a X s i) j ∣)
    (Mask.masked (λ j′ → k ≤ i + j′)
      (λ j′ → k NP.≤? (i + j′))
      (λ j′ → R._*_ (R._*_ (a i) (a j′))
        (R.pow (R.∣ X ∣) (s + (i + j′)))) j)
maskedCellAbsolute a X s k i j an with k NP.≤? (i + j)
... | yes h = signedCellAbsolute a X s i j an
... | no h = P.nonNegx⇒∣x∣≃x P.nonNeg0

signedRectangleAbsolute : ∀ a X s k height →
  (∀ n → R.NonNegative (a n)) →
  R._≤_ (R.∣ signedRectangle a X s k height ∣)
    (Mass.filteredPowerRectangle (λ i j → k ≤ i + j)
      (λ i j → k NP.≤? (i + j)) a X s height)
signedRectangleAbsolute a X s k height an =
  P.≤-trans (Abs.finiteSeriesAbsoluteBound (signedRow a X s k height) height)
    (Order.finitePointwiseBound height (λ i _ →
      P.≤-trans
        (Abs.finiteSeriesAbsoluteBound
          (Mask.masked (λ j → k ≤ i + j)
            (λ j → k NP.≤? (i + j)) (signedCell a X s i)) height)
        (P.≤-reflexive
          (Ext.finiteSumCongruent (λ j → maskedCellAbsolute a X s k i j an)
            height))))

scaledWingAbsolute : ∀ a X s k height → k ≤ height →
  (∀ n → R.NonNegative (a n)) →
  R._≤_
    (R.∣ R._*_ (R.pow X s)
      (R._-_ (Rect.rectangleSum (CMP.term a X) (CMP.term a X) height height)
        (Row.trianglePartial (CMP.term a X) (CMP.term a X) k)) ∣)
    (Mass.filteredPowerRectangle (λ i j → k ≤ i + j)
      (λ i j → k NP.≤? (i + j)) a X s height)
scaledWingAbsolute a X s k height h an =
  P.≤-respˡ-≃ (P.≃-symm (P.∣-∣-cong
    (scaledWingIsSignedRectangle a X s k height h)))
    (signedRectangleAbsolute a X s k height an)

actualAOuter : ∀ X →
  R._≤_ (R.∣ X ∣) Half.bishopQuarter → ∀ n →
  R._≤_ (R.∣ R.- (R._*_ X (Tail.originalAWing X (suc n))) ∣)
    (R.pow Half.bishopQuarter (suc n))
actualAOuter X inside n =
  P.≤-respˡ-≃
    (P.≃-trans (P.∣-∣-cong (P.*-congʳ (P.*-identityˡ X)))
      (P.≃-symm P.∣-x∣≃∣x∣))
    (P.≤-trans (scaledWingAbsolute CMP.aCoefficient X 1 n (suc n)
      (NP.n≤1+n n) CMP.aNN) (Mass.originalAFilteredQuarter X inside n))

powerTwo : ∀ X → R._≃_ (R.pow X 2) (R._*_ X X)
powerTwo X = P.*-congʳ (P.*-identityˡ X)

actualBOuter : ∀ X →
  R._≤_ (R.∣ X ∣) Half.bishopQuarter → ∀ n →
  R._≤_ (R.∣ R._*_ (R._*_ X X) (Tail.originalBWing X (suc n)) ∣)
    (R.pow Half.bishopQuarter (suc n))
actualBOuter X inside zero =
  P.≤-respˡ-≃ (P.∣-∣-cong (P.*-congʳ (powerTwo X)))
    (P.≤-trans (scaledWingAbsolute CMP.bCoefficient X 2 0 1
      z≤n CMP.bNN) (Mass.originalBFirstFilteredQuarter X inside))
actualBOuter X inside (suc n) =
  P.≤-respˡ-≃ (P.∣-∣-cong (P.*-congʳ (powerTwo X)))
    (P.≤-trans (scaledWingAbsolute CMP.bCoefficient X 2 n (suc (suc n))
      (NP.≤-step (NP.n≤1+n n)) CMP.bNN)
      (Mass.originalBFilteredQuarter X inside n))

originalOuterTwoWings : ∀ X →
  R._≤_ (R.∣ X ∣) Half.bishopQuarter → Two.OriginalOuterTwoWings X
originalOuterTwoWings X inside n = actualAOuter X inside n , actualBOuter X inside n

originalCMP102ScalarGZero : ∀ X
  (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  R._≃_ (Original.originalG X inside) R.0ℝ
originalCMP102ScalarGZero X inside =
  Two.originalGZeroFromActualTwoOuterWings X inside (originalOuterTwoWings X inside)
