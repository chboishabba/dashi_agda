module DASHI.Moonshine.OggSSP2BIteratedTateDefectTargetExact where

------------------------------------------------------------------------
-- ITERATED C2-TATE DEFECT TARGET FOR THE WITHIN-FIBRE OUTER ACTION
--
-- Geometry distinction:
--   * the sourced S3 factor in the 2B-pure Klein-four normalizer permutes the
--     three 2B fibres;
--   * the Completion10 involution is the outer involution in the within-fibre
--     M22:2 <= M24 factor.
--
-- Therefore this owner does NOT identify that outer involution with a second
-- nontrivial element of the pure Klein four.  It records the C2-Tate defect of
-- its action on one already-formed 2B Tate fibre.
--
-- For an involution h in characteristic two, N = h - 1 satisfies N^2 = 0.
-- If the module decomposes as J1^a + J2^b then:
--
--   ambient dimension = a + 2 b
--   rank(N)           = b
--   dim Hhat^0(<h>,M) = a.
--
-- Hence the iterated Tate defect is characterized subtraction-free by
--
--   defect + 2 * rank(N) = ambient dimension.
--
-- The Completion10 target J2^5 has ambient=10, rank=5, defect=0.
-- On the full 276 Tate head the GAP/duad route computes a corresponding
-- within-fibre M22:2 outer-class target.  The actual Moonshine value remains a
-- same-object extension test, not a promoted pure-Klein-four identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

record C2TateDefectReceipt : Set where
  constructor c2-tate-defect-receipt
  field
    ambientDimension : Nat
    rankGMinusI : Nat
    tateDefectDimension : Nat
    dimensionClosure : tateDefectDimension + (2 * rankGMinusI) ≡ ambientDimension

open C2TateDefectReceipt public

completion10DefectReceipt : C2TateDefectReceipt
completion10DefectReceipt = c2-tate-defect-receipt 10 5 0 refl

completion10AmbientIsTen : ambientDimension completion10DefectReceipt ≡ 10
completion10AmbientIsTen = refl

completion10RankIsFive : rankGMinusI completion10DefectReceipt ≡ 5
completion10RankIsFive = refl

completion10IteratedTateDefectIsZero :
  tateDefectDimension completion10DefectReceipt ≡ 0
completion10IteratedTateDefectIsZero = refl

record IteratedTateComparisonBoundary : Set where
  constructor iterated-tate-comparison-boundary
  field
    genericDefectFormulaFormalized : Bool
    completion10ZeroDefectTargetFormalized : Bool
    duadOuterClassRuntimeScreenImplemented : Bool
    outerActionIdentifiedWithPureKleinFourElement : Bool
    actualTwoBTateFibreOuterDefectComputed : Bool
    actualTateDefectMatchedToDuadExtension : Bool

canonicalIteratedTateComparisonBoundary : IteratedTateComparisonBoundary
canonicalIteratedTateComparisonBoundary =
  iterated-tate-comparison-boundary
    true true true false false false
