module DASHI.Physics.Gravity.KKMinkowskiChernSimonsFiveDConsumerExact where

------------------------------------------------------------------------
-- KK x original Minkowski x CS SOURCE CROSSWALK 2026-10-24
--
-- THESE ARE PRIOR, EXISTING OWNERS (not new physical discoveries):
-- MinkowskiLimitReceipt: exact flat 3+1 signature/quadratic.
-- GRConcreteLeviCivita: flat 4D metric connection prerequisite.
-- KacMoodyLevelReceipt / FermionicLoopCSShiftReceipt:
-- candidate 2+1D CS/WZW affine levels and loop shifts.
-- BulkBoundarySU3Receipt: conditional 2+1D SU3 CS -> 3+1D bulk.
--
-- A FIVE-dimensional source needs a top five-form CS functional,
-- 5D parity-odd determinant, global spin CS, bare counterterms,
-- and selected SU3^3 x U1 matter. No silent transport of 3D k.
--
-- Executables in same PR check actual selected exterior products,
-- 5D T5 large-gauge winding, and the flat KK pressure variation.
-- This module certifies the finite TYPE/consumer distinctions only.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Base using (_+_; _*_)
import DASHI.Physics.Closure.MinkowskiLimitReceipt as Mink
import DASHI.Physics.Closure.GRConcreteLeviCivita as Levi
import DASHI.Physics.QFT.KacMoodyLevelReceipt as KM
import DASHI.Physics.QFT.FermionicLoopCSShiftReceipt as FCS
import DASHI.Physics.QFT.BulkBoundarySU3Receipt as Bulk
import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair

minkowskiFlatOwner : Mink.CarrierQuadraticIsMinkowski
minkowskiFlatOwner = Mink.minkowskiLimitReceipt

flatLeviCivitaOwner : Levi.GRConcreteLeviCivitaStatus
flatLeviCivitaOwner =
  Levi.selectedFlatMinkowskiLeviCivitaPrerequisiteClosed

threeDimensionalCSOwner : KM.LevelReading
threeDimensionalCSOwner =
  KM.p3Conductor3ChernSimonsLevel3Candidate

fermionShiftOwner : FCS.FermionicLoopCSShiftReceipt
fermionShiftOwner = FCS.canonicalFermionicLoopCSShiftReceipt

bulkBoundaryCSOwner : Bulk.BulkBoundarySU3Receipt
bulkBoundaryCSOwner = Bulk.canonicalBulkBoundarySU3Receipt

threeFormDegree : Nat
threeFormDegree = 1 + 2

fiveFormDegree : Nat
fiveFormDegree = 1 + 2 + 2

threeFormIsNotFiveForm : threeFormDegree ≡ fiveFormDegree → ⊥
threeFormIsNotFiveForm ()

minkowskiFourDimension : Nat
minkowskiFourDimension = 3 + 1

flatProductFifthDimension : Nat
flatProductFifthDimension = minkowskiFourDimension + 1

productSourceHasFiveCoordinates : flatProductFifthDimension ≡ 5
productSourceHasFiveCoordinates = refl

data CSActionConsumer : Set where
  boundaryThreeFormCS fiveDimensionalBulkCS : CSActionConsumer

commonKeywordObserver : CSActionConsumer → Bool
commonKeywordObserver boundaryThreeFormCS = true
commonKeywordObserver fiveDimensionalBulkCS = true

physicalActionFormDegree : CSActionConsumer → Nat
physicalActionFormDegree boundaryThreeFormCS = threeFormDegree
physicalActionFormDegree fiveDimensionalBulkCS = fiveFormDegree

physicalActionFromBareCSKeywordImpossible :
  Transport.ClaimTransport
    commonKeywordObserver physicalActionFormDegree → ⊥
physicalActionFromBareCSKeywordImpossible =
  Transport.claimNonTransportWitnessBlocksTransport
    (Descent.consumerNonDescentWitness
      boundaryThreeFormCS fiveDimensionalBulkCS
      refl threeFormIsNotFiveForm)

-- Prior GR receipt knows flat 3+1; the selected 5D product action
-- carries a separate internal S1 coordinate and stress T55.
data FlatPhysicalModel : Set where
  fourDimensionalMinkowskiDonor
  minkowskiTimesCompactCircleSource : FlatPhysicalModel

sameFlatGeometryKeyword : FlatPhysicalModel → Bool
sameFlatGeometryKeyword fourDimensionalMinkowskiDonor = true
sameFlatGeometryKeyword minkowskiTimesCompactCircleSource = true

sourceDimension : FlatPhysicalModel → Nat
sourceDimension fourDimensionalMinkowskiDonor = 4
sourceDimension minkowskiTimesCompactCircleSource = 5

fourNotFive : 4 ≡ 5 → ⊥
fourNotFive ()

flatMinkowskiKeywordCannotDetermineKKSource :
  Transport.ClaimNonTransportWitness
    sameFlatGeometryKeyword sourceDimension
flatMinkowskiKeywordCannotDetermineKKSource =
  Descent.consumerNonDescentWitness
    fourDimensionalMinkowskiDonor
    minkowskiTimesCompactCircleSource
    refl fourNotFive

-- Classical mixed five-form A ^ F ^ F is zero when F=0.
-- The actual exterior-algebra check is in source-owned Python.
-- Even a flat nonzero Wilson connection does not make F nonzero.
data FlatCSInput : Set where
  zeroCurvature nonzeroFlux : FlatCSInput

data ClassicalCSBackgroundValue : Set where
  classicalFiveCSZero
  selectedNonflatCSCanBeNonzero : ClassicalCSBackgroundValue

selectedCS5BackgroundValue : FlatCSInput → ClassicalCSBackgroundValue
selectedCS5BackgroundValue zeroCurvature = classicalFiveCSZero
selectedCS5BackgroundValue nonzeroFlux = selectedNonflatCSCanBeNonzero

classicalFlatCSIsZero :
  selectedCS5BackgroundValue zeroCurvature ≡ classicalFiveCSZero
classicalFlatCSIsZero = refl

-- At flat F=R=0, the classical topological CS source contributes
-- zero to the same action's T55. A nonzero Casimir defect D cannot
-- become D=0 by simply copying in an unrelated 3D CS level.
flatCSContributionToSelectedDefect : Nat
flatCSContributionToSelectedDefect = 0

flatClassicalCSCannotChangeNonzeroDefect :
  (D : Nat) →
  D + flatCSContributionToSelectedDefect ≡ D
flatClassicalCSCannotChangeNonzeroDefect D = refl

-- This selected five-form gauge calculation is NOT a certified
-- physical global CS quotient functional or a complete E6 action.
data SourceCertificationKind : Set where
  classicalFiveFormTest globalSpinCSQuantumFunctional : SourceCertificationKind

observedSelectedFlatTest : SourceCertificationKind
observedSelectedFlatTest = classicalFiveFormTest

data SourceMissing : Set where
  globalGaugeQuotient
  massiveFermionEtaRegulator
  physicalMatterAndCSBareLevels
  mixedGravitationalFiveForm
  fullInteractingE6Action
  physicalEinsteinSource : SourceMissing
