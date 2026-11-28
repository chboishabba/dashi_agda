module DASHI.Foundations.BishopFiniteShiftedTriangleComplementExact where

-- Exact signed rectangular complement of the original Cauchy triangle.
-- No positivity premise; cutoff <= square height is the only geometry.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base as N using (_≤_; z≤n; s≤s; _∸_)
import Data.Nat.Properties as NP
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import Data.Rational.Unnormalised using (0ℚᵘ)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFiniteSeriesShiftScaleExact as Scale
import DASHI.Foundations.BishopFiniteSeriesDifferenceExact as Diff
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as Fin
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rect

after : Nat → (Nat → R.ℝ) → Nat → R.ℝ
after zero f j = f j
after (suc k) f zero = R.0ℝ
after (suc k) f (suc j) = after k (Row.shift f) j

afterSelected : ∀ k f j → k ≤ j → R._≃_ (after k f j) (f j)
afterSelected zero f j h = P.≃-refl
afterSelected (suc k) f zero ()
afterSelected (suc k) f (suc j) (s≤s h) = afterSelected k (Row.shift f) j h

afterRejected : ∀ k f j → ¬ (k ≤ j) → R._≃_ (after k f j) R.0ℝ
afterRejected zero f j h = ⊥-elim (h z≤n)
afterRejected (suc k) f zero h = P.≃-refl
afterRejected (suc k) f (suc j) h =
  afterRejected k (Row.shift f) j (λ p → h (s≤s p))

cutToRow : ∀ k i j → k ≤ i + j → k ∸ i ≤ j
cutToRow zero i j h = z≤n
cutToRow (suc k) zero j h = h
cutToRow (suc k) (suc i) j (s≤s h) = cutToRow k i j h

rowToCut : ∀ k i j → k ∸ i ≤ j → k ≤ i + j
rowToCut zero i j h = z≤n
rowToCut (suc k) zero j h = h
rowToCut (suc k) (suc i) j h = s≤s (rowToCut k i j h)

zeroPrefix : ∀ n → R._≃_ (Seq.SeriesOf (λ _ → R.0ℝ) n) R.0ℝ
zeroPrefix zero = P.≃-refl
zeroPrefix (suc n) =
  P.≃-trans (P.+-cong (zeroPrefix n) P.≃-refl) (P.+-identityʳ R.0ℝ)

-- Signed suffix is precisely whole prefix minus omitted prefix.
afterPrefixDifference : ∀ k width f → k ≤ width →
  R._≃_ (R._-_ (Seq.SeriesOf f width) (Seq.SeriesOf f k))
    (Seq.SeriesOf (after k f) width)
afterPrefixDifference zero width f h =
  let open P.ℝ-Solver
  in solve 1 (λ a → a ⊖ Κ 0ℚᵘ ⊜ a) P.≃-refl (Seq.SeriesOf f width)
afterPrefixDifference (suc k) zero f ()
afterPrefixDifference (suc k) (suc width) f (s≤s h) =
  let a = f zero
      u = Seq.SeriesOf (Row.shift f) width
      v = Seq.SeriesOf (Row.shift f) k
      open P.ℝ-Solver
  in P.≃-trans
    (P.+-cong (Scale.finiteSeriesHeadShift f width)
      (P.-‿cong (Scale.finiteSeriesHeadShift f k)))
    (P.≃-trans
      (solve 3 (λ a u v → (a ⊕ u) ⊖ (a ⊕ v) ⊜ Κ 0ℚᵘ ⊕ (u ⊖ v))
        P.≃-refl a u v)
      (P.≃-trans
        (P.+-cong P.≃-refl (afterPrefixDifference k width (Row.shift f) h))
        (P.≃-symm (Scale.finiteSeriesHeadShift (after (suc k) f) width))))

paddedRows : (Nat → R.ℝ) → (Nat → R.ℝ) → Nat → Nat → R.ℝ
paddedRows a b k height =
  Seq.SeriesOf (λ i → R._*_ (a i) (Fin.finSum b (k ∸ i))) height

paddedRowsAreMertens : ∀ a b k height → k ≤ height →
  R._≃_ (paddedRows a b k height) (Row.mertensRowPartial a b k)
paddedRowsAreMertens a b zero height h =
  P.≃-trans
    (Ext.finiteSumCongruent
      (λ i → let open P.ℝ-Solver in
        solve 1 (λ x → x ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl (a i)) height)
    (zeroPrefix height)
paddedRowsAreMertens a b (suc k) zero ()
paddedRowsAreMertens a b (suc k) (suc height) (s≤s h) =
  P.≃-trans
    (Scale.finiteSeriesHeadShift (λ i → R._*_ (a i)
      (Fin.finSum b (suc k ∸ i))) height)
    (P.≃-trans
      (P.+-cong P.≃-refl
        (paddedRowsAreMertens (Row.shift a) b k height h))
      (P.≃-symm (Row.mertensRowHead a b k)))

wingRows : (Nat → R.ℝ) → (Nat → R.ℝ) → Nat → Nat → R.ℝ
wingRows a b k height =
  Seq.SeriesOf (λ i → R._*_ (a i)
    (Seq.SeriesOf (after (k ∸ i) b) height)) height

originalTriangleComplement : ∀ a b k height → k ≤ height →
  R._≃_
    (R._-_ (Rect.rectangleSum a b height height)
      (Row.trianglePartial a b k))
    (wingRows a b k height)
originalTriangleComplement a b k height h =
  P.≃-trans
    (P.+-cong P.≃-refl (P.-‿cong
      (P.≃-trans (Row.triangleIsMertensRow a b k)
        (P.≃-symm (paddedRowsAreMertens a b k height h)))))
    (P.≃-trans
      (Diff.finiteSeriesDifference
        (λ i → Rect.rectangleRow a b i height)
        (λ i → R._*_ (a i) (Fin.finSum b (k ∸ i))) height)
      (Ext.finiteSumCongruent
        (λ i →
          let x = a i
              u = Seq.SeriesOf b height
              v = Fin.finSum b (k ∸ i)
              open P.ℝ-Solver
          in P.≃-trans
            (solve 3 (λ x u v → (x ⊗ u) ⊖ (x ⊗ v) ⊜ x ⊗ (u ⊖ v))
              P.≃-refl x u v)
            (P.*-congˡ
              (P.≃-trans
                (P.+-cong P.≃-refl (P.-‿cong (Fin.finSumIsSeriesOf b (k ∸ i))))
                (afterPrefixDifference (k ∸ i) height b
                  (NP.≤-trans (NP.m∸n≤m k i) h))))) height))
