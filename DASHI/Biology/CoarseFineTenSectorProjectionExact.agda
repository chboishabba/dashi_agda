module DASHI.Biology.CoarseFineTenSectorProjectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Fan R. K. Chung,
-- "Spectral Graph Theory", CBMS 92, American Mathematical Society, 1997.
-- DOI: 10.1090/cbms/092.
--
-- DASHI CONTRIBUTION
--
-- Realise j_coarse / j_fine as an exact operator pair on the existing
-- ten-sector T^2 disjoint-union {j} carrier.  Broadcast embeds one common
-- mode into ten coordinates.  Averaging is its left inverse; their reverse
-- composite is the idempotent common-mode projector.  Subtracting it gives
-- a zero-sum nine-relative-degree residual.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Sector
import DASHI.Biology.ModularCoarseFineAddressFibrationExact as Address

record TenField : Set where
  constructor tenField
  field
    at0 : ℚ
    at1 : ℚ
    at2 : ℚ
    at3 : ℚ
    at4 : ℚ
    at5 : ℚ
    at6 : ℚ
    at7 : ℚ
    at8 : ℚ
    atJ : ℚ

open TenField public

at :
  Sector.DecimalCompletionState →
  TenField →
  ℚ
at Sector.d0 field = at0 field
at Sector.d1 field = at1 field
at Sector.d2 field = at2 field
at Sector.d3 field = at3 field
at Sector.d4 field = at4 field
at Sector.d5 field = at5 field
at Sector.d6 field = at6 field
at Sector.d7 field = at7 field
at Sector.d8 field = at8 field
at Sector.j9 field = atJ field

sumTen : TenField → ℚ
sumTen field =
  at0 field + at1 field + at2 field + at3 field + at4 field
  + at5 field + at6 field + at7 field + at8 field + atJ field

oneTenth : ℚ
oneTenth = + 1 / 10

ten : ℚ
ten = + 10 / 1

average : TenField → ℚ
average field = oneTenth * sumTen field

broadcast : ℚ → TenField
broadcast value =
  tenField value value value value value value value value value value

atBroadcast :
  (sector : Sector.DecimalCompletionState) →
  (value : ℚ) →
  at sector (broadcast value) ≡ value
atBroadcast Sector.d0 value = refl
atBroadcast Sector.d1 value = refl
atBroadcast Sector.d2 value = refl
atBroadcast Sector.d3 value = refl
atBroadcast Sector.d4 value = refl
atBroadcast Sector.d5 value = refl
atBroadcast Sector.d6 value = refl
atBroadcast Sector.d7 value = refl
atBroadcast Sector.d8 value = refl
atBroadcast Sector.j9 value = refl

averageBroadcast :
  (value : ℚ) →
  average (broadcast value) ≡ value
averageBroadcast value = ℚRing.solve-∀ value

projectCommon : TenField → TenField
projectCommon field = broadcast (average field)

projectCommonAt :
  (field : TenField) →
  (sector : Sector.DecimalCompletionState) →
  at sector (projectCommon field) ≡ average field
projectCommonAt field Sector.d0 = refl
projectCommonAt field Sector.d1 = refl
projectCommonAt field Sector.d2 = refl
projectCommonAt field Sector.d3 = refl
projectCommonAt field Sector.d4 = refl
projectCommonAt field Sector.d5 = refl
projectCommonAt field Sector.d6 = refl
projectCommonAt field Sector.d7 = refl
projectCommonAt field Sector.d8 = refl
projectCommonAt field Sector.j9 = refl

projectCommonIdempotentAt :
  (field : TenField) →
  (sector : Sector.DecimalCompletionState) →
  at sector (projectCommon (projectCommon field))
  ≡ at sector (projectCommon field)
projectCommonIdempotentAt field sector
  rewrite averageBroadcast (average field) =
  refl

fieldSubtract : TenField → TenField → TenField
fieldSubtract left right =
  tenField
    (at0 left - at0 right)
    (at1 left - at1 right)
    (at2 left - at2 right)
    (at3 left - at3 right)
    (at4 left - at4 right)
    (at5 left - at5 right)
    (at6 left - at6 right)
    (at7 left - at7 right)
    (at8 left - at8 right)
    (atJ left - atJ right)

fieldAdd : TenField → TenField → TenField
fieldAdd left right =
  tenField
    (at0 left + at0 right)
    (at1 left + at1 right)
    (at2 left + at2 right)
    (at3 left + at3 right)
    (at4 left + at4 right)
    (at5 left + at5 right)
    (at6 left + at6 right)
    (at7 left + at7 right)
    (at8 left + at8 right)
    (atJ left + atJ right)

fineResidual : TenField → TenField
fineResidual field = fieldSubtract field (projectCommon field)

reconstructsAt :
  (field : TenField) →
  (sector : Sector.DecimalCompletionState) →
  at sector (fieldAdd (projectCommon field) (fineResidual field))
  ≡ at sector field
reconstructsAt field Sector.d0 =
  ℚRing.solve-∀ (at0 field) (average field)
reconstructsAt field Sector.d1 =
  ℚRing.solve-∀ (at1 field) (average field)
reconstructsAt field Sector.d2 =
  ℚRing.solve-∀ (at2 field) (average field)
reconstructsAt field Sector.d3 =
  ℚRing.solve-∀ (at3 field) (average field)
reconstructsAt field Sector.d4 =
  ℚRing.solve-∀ (at4 field) (average field)
reconstructsAt field Sector.d5 =
  ℚRing.solve-∀ (at5 field) (average field)
reconstructsAt field Sector.d6 =
  ℚRing.solve-∀ (at6 field) (average field)
reconstructsAt field Sector.d7 =
  ℚRing.solve-∀ (at7 field) (average field)
reconstructsAt field Sector.d8 =
  ℚRing.solve-∀ (at8 field) (average field)
reconstructsAt field Sector.j9 =
  ℚRing.solve-∀ (atJ field) (average field)

fineResidualHasZeroSum :
  (field : TenField) →
  sumTen (fineResidual field) ≡ 0ℚ
fineResidualHasZeroSum
  (tenField x0 x1 x2 x3 x4 x5 x6 x7 x8 xJ) =
  ℚRing.solve-∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 xJ

fineResidualKillsBroadcast :
  (value : ℚ) →
  (sector : Sector.DecimalCompletionState) →
  at sector (fineResidual (broadcast value)) ≡ 0ℚ
fineResidualKillsBroadcast value Sector.d0
  rewrite averageBroadcast value = ℚRing.solve-∀ value
fineResidualKillsBroadcast value Sector.d1
  rewrite averageBroadcast value = ℚRing.solve-∀ value
fineResidualKillsBroadcast value Sector.d2
  rewrite averageBroadcast value = ℚRing.solve-∀ value
fineResidualKillsBroadcast value Sector.d3
  rewrite averageBroadcast value = ℚRing.solve-∀ value
fineResidualKillsBroadcast value Sector.d4
  rewrite averageBroadcast value = ℚRing.solve-∀ value
fineResidualKillsBroadcast value Sector.d5
  rewrite averageBroadcast value = ℚRing.solve-∀ value
fineResidualKillsBroadcast value Sector.d6
  rewrite averageBroadcast value = ℚRing.solve-∀ value
fineResidualKillsBroadcast value Sector.d7
  rewrite averageBroadcast value = ℚRing.solve-∀ value
fineResidualKillsBroadcast value Sector.d8
  rewrite averageBroadcast value = ℚRing.solve-∀ value
fineResidualKillsBroadcast value Sector.j9
  rewrite averageBroadcast value = ℚRing.solve-∀ value

dot : TenField → TenField → ℚ
dot left right =
  at0 left * at0 right + at1 left * at1 right
  + at2 left * at2 right + at3 left * at3 right
  + at4 left * at4 right + at5 left * at5 right
  + at6 left * at6 right + at7 left * at7 right
  + at8 left * at8 right + atJ left * atJ right

normSq : TenField → ℚ
normSq field = dot field field

commonResidualOrthogonal :
  (field : TenField) →
  dot (projectCommon field) (fineResidual field) ≡ 0ℚ
commonResidualOrthogonal
  (tenField x0 x1 x2 x3 x4 x5 x6 x7 x8 xJ) =
  ℚRing.solve-∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 xJ

commonResidualNormSplit :
  (field : TenField) →
  normSq field
  ≡ normSq (projectCommon field) + normSq (fineResidual field)
commonResidualNormSplit
  (tenField x0 x1 x2 x3 x4 x5 x6 x7 x8 xJ) =
  ℚRing.solve-∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 xJ

record NineRelativeField : Set where
  constructor nineRelativeField
  field
    relative0 : ℚ
    relative1 : ℚ
    relative2 : ℚ
    relative3 : ℚ
    relative4 : ℚ
    relative5 : ℚ
    relative6 : ℚ
    relative7 : ℚ
    relative8 : ℚ

open NineRelativeField public

completeMeanZero : NineRelativeField → TenField
completeMeanZero relative =
  let firstNine =
        relative0 relative + relative1 relative + relative2 relative
        + relative3 relative + relative4 relative + relative5 relative
        + relative6 relative + relative7 relative + relative8 relative
  in
  tenField
    (relative0 relative)
    (relative1 relative)
    (relative2 relative)
    (relative3 relative)
    (relative4 relative)
    (relative5 relative)
    (relative6 relative)
    (relative7 relative)
    (relative8 relative)
    (0ℚ - firstNine)

completedRelativeFieldHasZeroSum :
  (relative : NineRelativeField) →
  sumTen (completeMeanZero relative) ≡ 0ℚ
completedRelativeFieldHasZeroSum
  (nineRelativeField x0 x1 x2 x3 x4 x5 x6 x7 x8) =
  ℚRing.solve-∀ x0 x1 x2 x3 x4 x5 x6 x7 x8

coarseOverFine : ℚ
coarseOverFine = oneTenth

fineOverCoarse : ℚ
fineOverCoarse = ten

coarseFineAddressLaw :
  Address.jAbsoluteAddressDepth
  ≡ Address.jCoarseAddressDepth + Address.jFineAddressDepth
coarseFineAddressLaw = Address.jAbsoluteAddressDepthReconstructs

record TenSectorProjectionBoundary : Set where
  constructor tenSectorProjectionBoundary
  field
    tenMeansTenIndependentJInvariants : Bool
    tenMeansTenIndependentJInvariantsIsFalse :
      tenMeansTenIndependentJInvariants ≡ false
    nineRelativeCoordinatesAreAChosenBasis : Bool
    nineRelativeCoordinatesAreAChosenBasisIsTrue :
      nineRelativeCoordinatesAreAChosenBasis ≡ true
    commonModeProjectorIsModularHauptmodul : Bool
    commonModeProjectorIsModularHauptmodulIsFalse :
      commonModeProjectorIsModularHauptmodul ≡ false

canonicalTenSectorProjectionBoundary : TenSectorProjectionBoundary
canonicalTenSectorProjectionBoundary =
  tenSectorProjectionBoundary false refl true refl false refl
