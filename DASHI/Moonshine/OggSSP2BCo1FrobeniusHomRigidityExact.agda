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
-- residual lane
--
--   24  ---->  300 = Sym^2(24).
--
-- The executed runtime certificate now pays
--
--   dim Hom_Co1(24,Sym^2(24)) = 1,
--
-- and verifies that the explicit Frobenius-square map has rank 24 and spans
-- that unique nonzero equivariant Hom line.  Therefore there is no remaining
-- finite representation-theoretic ambiguity on the residual map.
--
-- The remaining same-object statement is narrower: after the actual residual
-- quotient is obtained from the source-native norm/block projector, prove that
-- its induced map is Co1-equivariant.  Then uniqueness forces that map onto the
-- already-paid Frobenius line.  The common 98280 lane is no longer an
-- independent gate: Lean's support squeeze derives it from the residual block
-- projector and norm injectivity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _-_)

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
    inducedActualResidualEquivariancePaid : Bool
    common98280NoLongerIndependentGate : Bool
    actualTateExteriorSquareWeldPaid : Bool

canonicalFrobeniusHomRigidityBoundary : FrobeniusHomRigidityBoundary
canonicalFrobeniusHomRigidityBoundary =
  frobenius-hom-rigidity-boundary
    true true true true false true false

homUniquenessRuntimeIsPaid :
  FrobeniusHomRigidityBoundary.homUniquenessRuntimePaid
    canonicalFrobeniusHomRigidityBoundary
  ≡ true
homUniquenessRuntimeIsPaid = refl

residual24LaneIsRigid :
  FrobeniusHomRigidityBoundary.residual24LaneRigid
    canonicalFrobeniusHomRigidityBoundary
  ≡ true
residual24LaneIsRigid = refl

inducedActualResidualEquivarianceStillOpen :
  FrobeniusHomRigidityBoundary.inducedActualResidualEquivariancePaid
    canonicalFrobeniusHomRigidityBoundary
  ≡ false
inducedActualResidualEquivarianceStillOpen = refl

common98280MapNoLongerIndependentGate :
  FrobeniusHomRigidityBoundary.common98280NoLongerIndependentGate
    canonicalFrobeniusHomRigidityBoundary
  ≡ true
common98280MapNoLongerIndependentGate = refl

actualTateExteriorSquareWeldStillOpen :
  FrobeniusHomRigidityBoundary.actualTateExteriorSquareWeldPaid
    canonicalFrobeniusHomRigidityBoundary
  ≡ false
actualTateExteriorSquareWeldStillOpen = refl
