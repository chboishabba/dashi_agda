module DASHI.Moonshine.OggSSP2BCo1FrobeniusHomRigidityExact where

------------------------------------------------------------------------
-- CO1 FROBENIUS-SQUARE HOM RIGIDITY FRONTIER
--
-- The source-native weight-two Tate cokernel problem has been reduced to the
-- C_M(2B)-equivariant map
--
--   L-/2L-  ---->  L+/2L+
--   dim 98304       dim 98580.
--
-- The ordinary branching and characteristic-two Co1 tests isolate the
-- candidate residual lane
--
--   24  ---->  300 = Sym^2(24),
--
-- where the explicit Frobenius-square map x |-> x^2 has image dimension 24
-- and cokernel wedge^2(24) of dimension 276.
--
-- The accompanying GAP screen computes
--   Hom_Co1(24, Sym^2(24)).
-- If that Hom space is one-dimensional, then over F2 there is a unique nonzero
-- Co1-equivariant 24 -> 300 map, necessarily the explicit Frobenius-square
-- embedding.  In that case the 24-dimensional part of the vertical weld is
-- rigid and the only remaining map-level seam is the common 98280 lane.
--
-- This owner is fail-closed until the runtime screen is executed and ingested.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _-_)

naturalDimension : Nat
naturalDimension = 24

symmetricSquareDimension : Nat
symmetricSquareDimension = 300

frobeniusImageDimension : Nat
frobeniusImageDimension = 24

exteriorQuotientDimension : Nat
exteriorQuotientDimension = symmetricSquareDimension - frobeniusImageDimension

exteriorQuotientDimensionIs276 : exteriorQuotientDimension ≡ 276
exteriorQuotientDimensionIs276 = refl

record FrobeniusHomRuntimeReceipt : Set where
  constructor frobenius-hom-runtime-receipt
  field
    hom24ToSym2Dimension : Nat
    explicitFrobeniusRank : Nat
    uniqueNonzeroHomLine : Bool
    explicitFrobeniusSpansHom : Bool

record FrobeniusHomRigidityBoundary : Set where
  constructor frobenius-hom-rigidity-boundary
  field
    explicitFrobeniusEmbeddingConstructed : Bool
    homUniquenessScreenImplemented : Bool
    homUniquenessRuntimePaid : Bool
    residual24LaneRigid : Bool
    common98280MapIdentified : Bool
    actualTateExteriorSquareWeldPaid : Bool

canonicalFrobeniusHomRigidityBoundary : FrobeniusHomRigidityBoundary
canonicalFrobeniusHomRigidityBoundary =
  frobenius-hom-rigidity-boundary
    true true false false false false

homUniquenessRuntimeStillOpen :
  FrobeniusHomRigidityBoundary.homUniquenessRuntimePaid
    canonicalFrobeniusHomRigidityBoundary
  ≡ false
homUniquenessRuntimeStillOpen = refl

common98280MapStillOpen :
  FrobeniusHomRigidityBoundary.common98280MapIdentified
    canonicalFrobeniusHomRigidityBoundary
  ≡ false
common98280MapStillOpen = refl

actualTateExteriorSquareWeldStillOpen :
  FrobeniusHomRigidityBoundary.actualTateExteriorSquareWeldPaid
    canonicalFrobeniusHomRigidityBoundary
  ≡ false
actualTateExteriorSquareWeldStillOpen = refl
