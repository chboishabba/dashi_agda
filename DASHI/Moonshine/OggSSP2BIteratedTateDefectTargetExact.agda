module DASHI.Moonshine.OggSSP2BIteratedTateDefectTargetExact where

------------------------------------------------------------------------
-- ITERATED TATE DEFECT TARGET FOR THE 2B-PURE KLEIN-FOUR TEST
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
-- On the full 276 Tate head the new GAP screen computes the corresponding
-- duad-side target for every outer M22:2 involution class; the actual Moonshine
-- iterated-Tate value remains a same-object test, not a promoted theorem.
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
    actualTwoBKleinFourIteratedTateComputed : Bool
    actualTateDefectMatchedToDuadExtension : Bool

canonicalIteratedTateComparisonBoundary : IteratedTateComparisonBoundary
canonicalIteratedTateComparisonBoundary =
  iterated-tate-comparison-boundary
    true true true false false
