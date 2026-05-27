module DASHI.Physics.QFT.W3ToM3Iso where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.QFT.W3ClockShiftAlgebra

------------------------------------------------------------------------
-- Downstream SU(3) matrix realization of the concrete W3 clock-shift
-- algebra.
--
-- The source algebra is the existing finite W3 witness.  The target is the
-- same 3x3 matrix carrier, now packaged as the matrix-algebra presentation
-- used by the SU(3) route note.  Since both sides are concrete record data
-- over the same finite carrier, the isomorphism is a structural copy and its
-- inverse is the reverse copy.

M3Carrier : Set
M3Carrier = Matrix3

record M3ClockShiftAlgebra : Set where
  field
    m3Clock : M3Carrier
    m3Shift : M3Carrier
    m3ClockCubedIsIdentity :
      matrixMul (matrixMul m3Clock m3Clock) m3Clock ≡ identityMatrix3
    m3ShiftCubedIsIdentity :
      matrixMul (matrixMul m3Shift m3Shift) m3Shift ≡ identityMatrix3
    m3CommutationRelation :
      matrixMul m3Shift m3Clock
      ≡ scalarMul omega (matrixMul m3Clock m3Shift)

open M3ClockShiftAlgebra public

canonicalM3ClockShiftAlgebra : M3ClockShiftAlgebra
canonicalM3ClockShiftAlgebra =
  record
    { m3Clock = clockMatrix
    ; m3Shift = shiftMatrix
    ; m3ClockCubedIsIdentity = clockCubedIsIdentity
    ; m3ShiftCubedIsIdentity = shiftCubedIsIdentity
    ; m3CommutationRelation = commutationRelation
    }

record W3ToM3Iso : Set where
  field
    source : W3ClockShiftAlgebra
    target : M3ClockShiftAlgebra
    to : W3ClockShiftAlgebra → M3ClockShiftAlgebra
    from : M3ClockShiftAlgebra → W3ClockShiftAlgebra
    toFrom : ∀ m → to (from m) ≡ m
    fromTo : ∀ w → from (to w) ≡ w

sourceToTarget :
  W3ClockShiftAlgebra → M3ClockShiftAlgebra
sourceToTarget record
  { clock = c
  ; shift = s
  ; clock³≡I = c³
  ; shift³≡I = s³
  ; commutation = comm
  } =
  record
    { m3Clock = c
    ; m3Shift = s
    ; m3ClockCubedIsIdentity = c³
    ; m3ShiftCubedIsIdentity = s³
    ; m3CommutationRelation = comm
    }

targetToSource :
  M3ClockShiftAlgebra → W3ClockShiftAlgebra
targetToSource record
  { m3Clock = c
  ; m3Shift = s
  ; m3ClockCubedIsIdentity = c³
  ; m3ShiftCubedIsIdentity = s³
  ; m3CommutationRelation = comm
  } =
  record
    { clock = c
    ; shift = s
    ; clock³≡I = c³
    ; shift³≡I = s³
    ; commutation = comm
    }

toFromSourceTarget :
  ∀ m → sourceToTarget (targetToSource m) ≡ m
toFromSourceTarget _ = refl

fromToSourceTarget :
  ∀ w → targetToSource (sourceToTarget w) ≡ w
fromToSourceTarget _ = refl

canonicalW3ToM3Iso : W3ToM3Iso
canonicalW3ToM3Iso =
  record
    { source = canonicalW3ClockShiftAlgebra
    ; target = canonicalM3ClockShiftAlgebra
    ; to = sourceToTarget
    ; from = targetToSource
    ; toFrom = toFromSourceTarget
    ; fromTo = fromToSourceTarget
    }

------------------------------------------------------------------------
-- Public aliases for the downstream SU(3) route.

W3ToM3SourceWitness : W3ClockShiftAlgebra
W3ToM3SourceWitness = W3ToM3Iso.source canonicalW3ToM3Iso

W3ToM3TargetWitness : M3ClockShiftAlgebra
W3ToM3TargetWitness = W3ToM3Iso.target canonicalW3ToM3Iso
