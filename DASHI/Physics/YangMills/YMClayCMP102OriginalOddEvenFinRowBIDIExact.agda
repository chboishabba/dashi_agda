module DASHI.Physics.YangMills.YMClayCMP102OriginalOddEvenFinRowBIDIExact where

------------------------------------------------------------------------
-- Section 32: original CMP102 shifted Cauchy row reverse solving.
--
-- The actual original shiftedNativeBracketCoefficient = oddPart-evenPart
-- is multiplied by the *actual* Bishop power X^k, then summed over the
-- original Sequence.SeriesOf (count, not inclusive).
--
-- Instead of re-proving all of the original Cauchy rows, identify the
-- precise two independently native Fin-index lemmas:
--   odd row: original singleton + shifted B + low B Cauchy triangle
--   even row: original doubled A + low A Cauchy triangle.
-- Their joint implication IS proved here in original represented reals.
--
-- The finite odd/even row producers below are NOT assumed as axioms or
-- postulates: they are explicit premises to be discharged from
-- CMP102 original oddPart/evenPart and Bishop finite Cauchy summation.
-- No native Agda 2.9 typecheck in this environment.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)
import Real as R
import RealProperties as P
import Sequence as Seq

import DASHI.Foundations.BishopFiniteSeriesDifferenceExact as Difference
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as CMP102
import DASHI.Physics.YangMills.YMClayCMP102OriginalSignedTriangleZeroExact as Signed
import DASHI.Physics.YangMills.YMClayCMP102OriginalGToTailAlgebraExact as Tail
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original

originalOddAt originalEvenAt : R.ℝ → Nat → R.ℝ
originalOddAt X k = R._*_ (CMP102.oddPart k) (R.pow X k)
originalEvenAt X k = R._*_ (CMP102.evenPart k) (R.pow X k)

originalOddFinite originalEvenFinite : R.ℝ → Nat → R.ℝ
originalOddFinite X count = Seq.SeriesOf (originalOddAt X) count
originalEvenFinite X count = Seq.SeriesOf (originalEvenAt X) count

-- All-degree original signed triangle is EXACTLY odd minus even finite
-- source row. This part is already a consequence of two previously
-- source-written Bishop finite-series lemmas, no CMP109 factorial
-- order estimates and no higher-level analytic convergence premise.
originalSignedTriangleOddMinusEven : ∀ X count →
  R._≃_
    (Signed.originalSignedTriangle X count)
    (R._-_ (originalOddFinite X count) (originalEvenFinite X count))
originalSignedTriangleOddMinusEven X count =
  P.≃-trans
    (Ext.seriesPartialSumsCongruent
      (λ k →
        let
          o = CMP102.oddPart k
          e = CMP102.evenPart k
          p = R.pow X k
          open P.ℝ-Solver
        in solve 3
          (λ odd even power →
             (odd ⊖ even) ⊗ power
             ⊜ (odd ⊗ power) ⊖ (even ⊗ power))
          P.≃-refl o e p)
      count)
    (P.≃-symm
      (Difference.finiteSeriesDifference
        (originalOddAt X) (originalEvenAt X) count))

-- EXACT original odd source row normal form at c=suc n. This
-- is a native Fin-index sum target (not an independent carrier).
originalOddFinRow : R.ℝ → Nat → Set
originalOddFinRow X n =
  R._≃_
    (originalOddFinite X (suc n))
    (R._+_
      (R._+_
        R.1ℝ
        (R._*_ (R._*_ CMP102.two X)
          (R._-_ (Original.bPrefix X (suc n))
            (Tail.originalLastB X n))))
      (R._*_ (R._*_ X X)
        (Tail.originalBLowTriangle X (suc n))))

-- EXACT original even source row normal form at c=suc n.
originalEvenFinRow : R.ℝ → Nat → Set
originalEvenFinRow X n =
  R._≃_
    (originalEvenFinite X (suc n))
    (R._+_
      (R._*_ CMP102.two (Original.aPrefix X (suc n)))
      (R._*_ X (Tail.originalALowTriangle X (suc n))))

-- Both real original rows imply the single original Fin-index weld,
-- without any assumption that G(X)=0 or that finite G_c=0.
originalShiftedRowFinReindexFromOriginalOddEven :
  ∀ X n → originalOddFinRow X n → originalEvenFinRow X n →
  Tail.OriginalShiftedRowFinReindex X n
originalShiftedRowFinReindexFromOriginalOddEven X n odd even =
  let
    A = Original.aPrefix X (suc n)
    B = Original.bPrefix X (suc n)
    TA = Tail.originalALowTriangle X (suc n)
    TB = Tail.originalBLowTriangle X (suc n)
    last = Tail.originalLastB X n
    open P.ℝ-Solver
    rearranged =
      solve 6
        (λ x a b ta tb last →
          ((Κ 1ℚᵘ ⊕
            ((Κ (+ 2 / 1) ⊗ x) ⊗ (b ⊖ last)) ⊕
            ((x ⊗ x) ⊗ tb))
           ⊖
           ((Κ (+ 2 / 1) ⊗ a) ⊕ (x ⊗ ta)))
          ⊜
          (((Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ a)) ⊖
             (x ⊗ ta))
           ⊕ ((Κ (+ 2 / 1) ⊗ x) ⊗ (b ⊖ last))
           ⊕ ((x ⊗ x) ⊗ tb)))
        P.≃-refl X A B TA TB last
  in
  P.≃-trans
    (originalSignedTriangleOddMinusEven X (suc n))
    (P.≃-trans
      (P.+-cong odd (P.-‿cong even))
      rearranged)

-- The actual G-count-to-Cauchy-tail theorem now consumes only the
-- TWO source-native row endpoints; it does not assume the desired
-- shifted row identity as an unanalysed all-in-one premise.
originalGIsCauchyTailFromNativeOddEven :
  ∀ X n → originalOddFinRow X n → originalEvenFinRow X n →
  R._≃_
    (Original.originalGPrefix X (suc n))
    (Tail.originalSignedCauchyTail X n)
originalGIsCauchyTailFromNativeOddEven X n odd even =
  Tail.originalGIsOriginalSignedCauchyTail X n
    (originalShiftedRowFinReindexFromOriginalOddEven X n odd even)
