module DASHI.Reasoning.Ternary27AlbertShapeFullE6BoundaryExact where

------------------------------------------------------------------------
-- SAME-CARRIER ALBERT-SHAPE / FULL-E6 ACTION BOUNDARY
--
-- Existing Agda source pays a two-sided
--
--   Ternary27Point <-> ScalarLine + NonOrigin26
--
-- on the same raw 27 carrier, with the geometric origin selected as the scalar
-- shaped point.  Companion Lean #47 now independently source-writes the full
-- faithful 51,840-element E6 minuscule action on those same 27 coordinates.
--
-- The new finite audit shows that a simple E6 reflection moves the selected
-- origin, and the punctured 26 is not invariant under the full E6 action.
-- Therefore `27=1+26` is not an E6 orbit/representation decomposition.  This is
-- exactly consistent with the genuine Albert story: the distinguished unit and
-- trace-zero 26 require the stronger Jordan/F4 layer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record AlbertShapeFullE6Boundary : Set where
  constructor albert-shape-full-e6-boundary
  field
    sameTernary27CarrierUsed : Bool
    agdaOriginPlus26BijectionPaid : Bool
    leanFullE6Ternary27ActionSourceWritten : Bool
    leanSelectedOriginMovedByE6SourceWritten : Bool
    leanResidual26NotFullE6InvariantSourceWritten : Bool
    onePlus26NotPromotedToE6RepresentationSplit : Bool
    jordanProductPaid : Bool
    cubicNormPaid : Bool
    jordanAdjointPaid : Bool
    distinguishedJordanUnitPaid : Bool
    f4AutomorphismActionPaid : Bool
    boundaryNote : String
open AlbertShapeFullE6Boundary public

canonicalAlbertShapeFullE6Boundary : AlbertShapeFullE6Boundary
canonicalAlbertShapeFullE6Boundary =
  albert-shape-full-e6-boundary
    true true true true true true
    false false false false false
    "The same ternary 27 now carries both the exact origin+26 puncture and the full E6 minuscule action. The selected origin is not E6-fixed, so the puncture is not an E6 representation splitting. A genuine Albert promotion still requires a Jordan product/unit, cubic norm/adjoint and compatible F4 automorphism action; those are not present in the current exceptional-algebra owners."
