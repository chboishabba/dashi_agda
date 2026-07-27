module DASHI.Physics.Closure.SU2SO3369HypervoxelBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

open import Base369 using
  ( TriTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  ; HexTruth
  ; NonaryTruth
  ; non-0
  ; non-1
  ; non-2
  ; non-3
  ; non-4
  ; non-5
  ; non-6
  ; non-7
  ; non-8
  )

import DASHI.Foundations.HexTruthPolarityFactor as HexFactor
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper

open import DASHI.Foundations.Base369MobiusTransport using
  ( OrientationPolarity
  ; positive
  ; negative
  ; flipOrientationPolarity
  )

------------------------------------------------------------------------
-- Axis role and signed coefficient role are deliberately different types.
------------------------------------------------------------------------

SU2Axis : Set
SU2Axis = Hyper.Axis3

axis₁ : SU2Axis
axis₁ = Hyper.axis-low

axis₂ : SU2Axis
axis₂ = Hyper.axis-mid

axis₃ : SU2Axis
axis₃ = Hyper.axis-high

axisToTriTruth : SU2Axis → TriTruth
axisToTriTruth Hyper.axis-low = tri-low
axisToTriTruth Hyper.axis-mid = tri-mid
axisToTriTruth Hyper.axis-high = tri-high

triTruthToAxis : TriTruth → SU2Axis
triTruthToAxis tri-low = Hyper.axis-low
triTruthToAxis tri-mid = Hyper.axis-mid
triTruthToAxis tri-high = Hyper.axis-high

axisTriRoundTrip : ∀ axis → triTruthToAxis (axisToTriTruth axis) ≡ axis
axisTriRoundTrip Hyper.axis-low = refl
axisTriRoundTrip Hyper.axis-mid = refl
axisTriRoundTrip Hyper.axis-high = refl

triAxisRoundTrip : ∀ tone → axisToTriTruth (triTruthToAxis tone) ≡ tone
triAxisRoundTrip tri-low = refl
triAxisRoundTrip tri-mid = refl
triAxisRoundTrip tri-high = refl

LiftPolarity : Set
LiftPolarity = OrientationPolarity

AxisLift : Set
AxisLift = SU2Axis × LiftPolarity

flipAxisLift : AxisLift → AxisLift
flipAxisLift (axis , lift) = axis , flipOrientationPolarity lift

projectAxisLift : AxisLift → SU2Axis
projectAxisLift = proj₁

projectAxisLiftFlipInvariant :
  ∀ lifted → projectAxisLift (flipAxisLift lifted) ≡ projectAxisLift lifted
projectAxisLiftFlipInvariant (axis , lift) = refl

flipAxisLiftInvolutive : ∀ lifted → flipAxisLift (flipAxisLift lifted) ≡ lifted
flipAxisLiftInvolutive (axis , positive) = refl
flipAxisLiftInvolutive (axis , negative) = refl

------------------------------------------------------------------------
-- HexTruth is used as a finite adapter for axis x lift polarity.
------------------------------------------------------------------------

axisLiftToHexTruth : AxisLift → HexTruth
axisLiftToHexTruth (axis , lift) =
  HexFactor.hexFactorToTruth (axisToTriTruth axis) lift

hexTruthToAxisLift : HexTruth → AxisLift
hexTruthToAxisLift hex =
  triTruthToAxis (proj₁ (HexFactor.hexTruthToFactor hex))
  , proj₂ (HexFactor.hexTruthToFactor hex)

axisLiftHexRoundTrip :
  ∀ lifted → hexTruthToAxisLift (axisLiftToHexTruth lifted) ≡ lifted
axisLiftHexRoundTrip (Hyper.axis-low , positive) = refl
axisLiftHexRoundTrip (Hyper.axis-low , negative) = refl
axisLiftHexRoundTrip (Hyper.axis-mid , positive) = refl
axisLiftHexRoundTrip (Hyper.axis-mid , negative) = refl
axisLiftHexRoundTrip (Hyper.axis-high , positive) = refl
axisLiftHexRoundTrip (Hyper.axis-high , negative) = refl

hexAxisLiftRoundTrip :
  ∀ hex → axisLiftToHexTruth (hexTruthToAxisLift hex) ≡ hex
hexAxisLiftRoundTrip HexFactor.hex-0 = refl
hexAxisLiftRoundTrip HexFactor.hex-1 = refl
hexAxisLiftRoundTrip HexFactor.hex-2 = refl
hexAxisLiftRoundTrip HexFactor.hex-3 = refl
hexAxisLiftRoundTrip HexFactor.hex-4 = refl
hexAxisLiftRoundTrip HexFactor.hex-5 = refl

------------------------------------------------------------------------
-- NonaryTruth is an index adapter for output-axis x input-axis matrix slots.
------------------------------------------------------------------------

MatrixSlot : Set
MatrixSlot = SU2Axis × SU2Axis

matrixSlotToNonary : MatrixSlot → NonaryTruth
matrixSlotToNonary (Hyper.axis-low , Hyper.axis-low) = non-0
matrixSlotToNonary (Hyper.axis-low , Hyper.axis-mid) = non-1
matrixSlotToNonary (Hyper.axis-low , Hyper.axis-high) = non-2
matrixSlotToNonary (Hyper.axis-mid , Hyper.axis-low) = non-3
matrixSlotToNonary (Hyper.axis-mid , Hyper.axis-mid) = non-4
matrixSlotToNonary (Hyper.axis-mid , Hyper.axis-high) = non-5
matrixSlotToNonary (Hyper.axis-high , Hyper.axis-low) = non-6
matrixSlotToNonary (Hyper.axis-high , Hyper.axis-mid) = non-7
matrixSlotToNonary (Hyper.axis-high , Hyper.axis-high) = non-8

nonaryToMatrixSlot : NonaryTruth → MatrixSlot
nonaryToMatrixSlot non-0 = Hyper.axis-low , Hyper.axis-low
nonaryToMatrixSlot non-1 = Hyper.axis-low , Hyper.axis-mid
nonaryToMatrixSlot non-2 = Hyper.axis-low , Hyper.axis-high
nonaryToMatrixSlot non-3 = Hyper.axis-mid , Hyper.axis-low
nonaryToMatrixSlot non-4 = Hyper.axis-mid , Hyper.axis-mid
nonaryToMatrixSlot non-5 = Hyper.axis-mid , Hyper.axis-high
nonaryToMatrixSlot non-6 = Hyper.axis-high , Hyper.axis-low
nonaryToMatrixSlot non-7 = Hyper.axis-high , Hyper.axis-mid
nonaryToMatrixSlot non-8 = Hyper.axis-high , Hyper.axis-high

matrixSlotRoundTrip : ∀ slot → nonaryToMatrixSlot (matrixSlotToNonary slot) ≡ slot
matrixSlotRoundTrip (Hyper.axis-low , Hyper.axis-low) = refl
matrixSlotRoundTrip (Hyper.axis-low , Hyper.axis-mid) = refl
matrixSlotRoundTrip (Hyper.axis-low , Hyper.axis-high) = refl
matrixSlotRoundTrip (Hyper.axis-mid , Hyper.axis-low) = refl
matrixSlotRoundTrip (Hyper.axis-mid , Hyper.axis-mid) = refl
matrixSlotRoundTrip (Hyper.axis-mid , Hyper.axis-high) = refl
matrixSlotRoundTrip (Hyper.axis-high , Hyper.axis-low) = refl
matrixSlotRoundTrip (Hyper.axis-high , Hyper.axis-mid) = refl
matrixSlotRoundTrip (Hyper.axis-high , Hyper.axis-high) = refl

nonarySlotRoundTrip : ∀ slot → matrixSlotToNonary (nonaryToMatrixSlot slot) ≡ slot
nonarySlotRoundTrip non-0 = refl
nonarySlotRoundTrip non-1 = refl
nonarySlotRoundTrip non-2 = refl
nonarySlotRoundTrip non-3 = refl
nonarySlotRoundTrip non-4 = refl
nonarySlotRoundTrip non-5 = refl
nonarySlotRoundTrip non-6 = refl
nonarySlotRoundTrip non-7 = refl
nonarySlotRoundTrip non-8 = refl

OperatorSheet : Set → Set
OperatorSheet Value = MatrixSlot → Value

LiftedOperatorSheet : Set → Set
LiftedOperatorSheet Value = MatrixSlot → LiftPolarity → Value

record CentreBlindOperatorSheet (Value : Set) : Set₁ where
  field
    liftedEntry : LiftedOperatorSheet Value
    centralLiftInvisible :
      ∀ slot → liftedEntry slot positive ≡ liftedEntry slot negative

------------------------------------------------------------------------
-- Abstract double-cover interface and the finite axis-lift adapter.
------------------------------------------------------------------------

record DoubleCoverInterface (Cover Base : Set) : Set₁ where
  field
    project : Cover → Base
    centralFlip : Cover → Cover
    projectionInvariant : ∀ x → project (centralFlip x) ≡ project x
    centralFlipInvolutive : ∀ x → centralFlip (centralFlip x) ≡ x

finiteAxisLiftDoubleCover : DoubleCoverInterface AxisLift SU2Axis
finiteAxisLiftDoubleCover = record
  { project = projectAxisLift
  ; centralFlip = flipAxisLift
  ; projectionInvariant = projectAxisLiftFlipInvariant
  ; centralFlipInvolutive = flipAxisLiftInvolutive
  }

------------------------------------------------------------------------
-- Cardinal hierarchy: 3, 6, 9 and the lifted sheet/voxel extensions.
------------------------------------------------------------------------

axisCarrierCount : Nat
axisCarrierCount = 3

axisLiftCarrierCount : Nat
axisLiftCarrierCount = 3 * 2

operatorSheetCount : Nat
operatorSheetCount = 3 * 3

liftedOperatorSheetCount : Nat
liftedOperatorSheetCount = 3 * 3 * 2

bracketVoxelCount : Nat
bracketVoxelCount = 3 * 3 * 3

liftedBracketVoxelCount : Nat
liftedBracketVoxelCount = 3 * 3 * 3 * 2

rank4HypervoxelCount : Nat
rank4HypervoxelCount = 3 * 3 * 3 * 3

liftedRank4HypervoxelCount : Nat
liftedRank4HypervoxelCount = 3 * 3 * 3 * 3 * 2

axisLiftCarrierCountIs6 : axisLiftCarrierCount ≡ 6
axisLiftCarrierCountIs6 = refl

operatorSheetCountIs9 : operatorSheetCount ≡ 9
operatorSheetCountIs9 = refl

liftedOperatorSheetCountIs18 : liftedOperatorSheetCount ≡ 18
liftedOperatorSheetCountIs18 = refl

bracketVoxelCountIs27 : bracketVoxelCount ≡ 27
bracketVoxelCountIs27 = refl

liftedBracketVoxelCountIs54 : liftedBracketVoxelCount ≡ 54
liftedBracketVoxelCountIs54 = refl

rank4HypervoxelCountIs81 : rank4HypervoxelCount ≡ 81
rank4HypervoxelCountIs81 = refl

liftedRank4HypervoxelCountIs162 : liftedRank4HypervoxelCount ≡ 162
liftedRank4HypervoxelCountIs162 = refl

------------------------------------------------------------------------
-- The right-Jacobian and Haar formulas are convention receipts.  They prevent
-- the sign and denominator powers from drifting across downstream estimates.
------------------------------------------------------------------------

data JacobianTrivialisation : Set where
  leftTrivialised : JacobianTrivialisation
  rightTrivialised : JacobianTrivialisation

data FormulaSign : Set where
  plusSign : FormulaSign
  minusSign : FormulaSign

record SO3RightJacobianConvention : Set where
  field
    trivialisation : JacobianTrivialisation
    identityCoefficient : String
    linearBracketSign : FormulaSign
    linearNumerator : String
    linearDenominatorPower : Nat
    quadraticBracketSign : FormulaSign
    quadraticNumerator : String
    quadraticDenominatorPower : Nat
    radiusSymbol : String

canonicalSO3RightJacobianConvention : SO3RightJacobianConvention
canonicalSO3RightJacobianConvention = record
  { trivialisation = rightTrivialised
  ; identityCoefficient = "1"
  ; linearBracketSign = minusSign
  ; linearNumerator = "1 - cos(r)"
  ; linearDenominatorPower = 2
  ; quadraticBracketSign = plusSign
  ; quadraticNumerator = "r - sin(r)"
  ; quadraticDenominatorPower = 3
  ; radiusSymbol = "r = ||theta||"
  }

record SU2HaarDensityConvention : Set where
  field
    densityFormula : String
    exponent : Nat
    chartRadiusRestricted : Bool
    globalInjectivityClaimed : Bool

canonicalSU2HaarDensityConvention : SU2HaarDensityConvention
canonicalSU2HaarDensityConvention = record
  { densityFormula = "(sin(r/2)/(r/2))^2"
  ; exponent = 2
  ; chartRadiusRestricted = true
  ; globalInjectivityClaimed = false
  }

record QuaternionPlaquetteRoute : Set where
  field
    exactQuaternionProductFirst : Bool
    genericBCHFallbackRetained : Bool
    compareRemainderConstants : Bool
    improvedConstantAlreadyProved : Bool
    routeDescription : String

canonicalQuaternionPlaquetteRoute : QuaternionPlaquetteRoute
canonicalQuaternionPlaquetteRoute = record
  { exactQuaternionProductFirst = true
  ; genericBCHFallbackRetained = true
  ; compareRemainderConstants = true
  ; improvedConstantAlreadyProved = false
  ; routeDescription =
      "Multiply the four SU(2) exponentials in quaternion coordinates, extract one resulting angle, Taylor-bound the cubic residual, and compare it with the generic BCH owner."
  }

------------------------------------------------------------------------
-- Local chart inversion is kept separate from global polynomial inversion.
------------------------------------------------------------------------

record ExponentialJacobianDiscipline : Set where
  field
    mapIsPolynomial : Bool
    globalInjectivityClaimed : Bool
    radiusRestrictedLocalInverse : Bool
    cutLocusTracked : Bool
    constantJacobianImpliesGlobalInverseUsed : Bool

canonicalExponentialJacobianDiscipline : ExponentialJacobianDiscipline
canonicalExponentialJacobianDiscipline = record
  { mapIsPolynomial = false
  ; globalInjectivityClaimed = false
  ; radiusRestrictedLocalInverse = true
  ; cutLocusTracked = true
  ; constantJacobianImpliesGlobalInverseUsed = false
  }

------------------------------------------------------------------------
-- Non-correspondence boundary.
------------------------------------------------------------------------

record SU2SO3369AuthorityBoundary : Set where
  field
    su2IsBase6Claimed : Bool
    so3IsBase3Claimed : Bool
    dimensionThreeMeansTernaryClaimed : Bool
    p7C6IdentifiedWithDoubleCoverClaimed : Bool
    nineSlotsAreTruthValuesClaimed : Bool
    polarityIsGroupActionOnlyWhenLawSupplied : Bool
    finiteIndexAdapterClaimed : Bool

canonicalSU2SO3369AuthorityBoundary : SU2SO3369AuthorityBoundary
canonicalSU2SO3369AuthorityBoundary = record
  { su2IsBase6Claimed = false
  ; so3IsBase3Claimed = false
  ; dimensionThreeMeansTernaryClaimed = false
  ; p7C6IdentifiedWithDoubleCoverClaimed = false
  ; nineSlotsAreTruthValuesClaimed = false
  ; polarityIsGroupActionOnlyWhenLawSupplied = true
  ; finiteIndexAdapterClaimed = true
  }

bridgeSummary : String
bridgeSummary =
  "The three-axis Lie-algebra carrier, its two-point central-lift fibre, and its 3x3 operator sheet are connected through explicit finite adapters; no identification of SU(2), SO(3), Base6 or NonaryTruth is asserted."
