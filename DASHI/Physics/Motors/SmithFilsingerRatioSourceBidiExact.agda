module DASHI.Physics.Motors.SmithFilsingerRatioSourceBidiExact where

-- Source-faithful finite ratio and geometry discriminators.
-- PDF: Darrer/Kelly 'High-power devices of Don Smith' pp47-51, 80-82.
-- Filsinger golden plate belongs to his PROPOSED portable antenna;
-- Smith's L1:L2 wire lengths belong to the historical 1:4 coil variant.
-- A ratio/winding angle is not a measured eigenfrequency/phase/power.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

data Contradiction : Set where

data Origin : Set where
  smithSourceAsCompiled : Origin
  kellyDarrerEditorial : Origin
  filsingerPortableProposal : Origin
  syntheticPhysicsModel : Origin

data RatioClaim : Set where
  smithOneToFourWire : RatioClaim
  smithEqualSeventeenTurnBranches : RatioClaim
  smithTwoThirdTurnGeometricAngle : RatioClaim
  filsingerGoldenRectangle : RatioClaim
  syntheticFibonacciApproximants : RatioClaim

origin : RatioClaim → Origin
origin smithOneToFourWire = smithSourceAsCompiled
origin smithEqualSeventeenTurnBranches = kellyDarrerEditorial
origin smithTwoThirdTurnGeometricAngle = kellyDarrerEditorial
origin filsingerGoldenRectangle = filsingerPortableProposal
origin syntheticFibonacciApproximants = syntheticPhysicsModel

data RatioMeaning : Set where
  coilWireLengths : RatioMeaning
  twoSecondaryWindingCounts : RatioMeaning
  mechanicalAngularPosition : RatioMeaning
  planarAspectRatio : RatioMeaning
  rationalModalApproximation : RatioMeaning

meaning : RatioClaim → RatioMeaning
meaning smithOneToFourWire = coilWireLengths
meaning smithEqualSeventeenTurnBranches = twoSecondaryWindingCounts
meaning smithTwoThirdTurnGeometricAngle = mechanicalAngularPosition
meaning filsingerGoldenRectangle = planarAspectRatio
meaning syntheticFibonacciApproximants = rationalModalApproximation

-- Source-evidence based negative control: no implicit conversion of
-- Smith's 1:4 wire length into Filsinger's golden plate geometry.
smithWireNotFilsingerPlate :
  smithOneToFourWire ≡ filsingerGoldenRectangle → Contradiction
smithWireNotFilsingerPlate ()

geometricAngleNotAspectRatio :
  mechanicalAngularPosition ≡ planarAspectRatio → Contradiction
geometricAngleNotAspectRatio ()

-- Forward predictions are conditional on a selected physical carrier.
data TargetObservable : Set where
  resonantWireResponse : TargetObservable
  opposedBranchVoltage : TargetObservable
  mechanicalEndpointPosition : TargetObservable
  orthogonalModePhase : TargetObservable
  rationalLockingDetuning : TargetObservable

forwardTarget : RatioClaim → TargetObservable
forwardTarget smithOneToFourWire = resonantWireResponse
forwardTarget smithEqualSeventeenTurnBranches = opposedBranchVoltage
forwardTarget smithTwoThirdTurnGeometricAngle = mechanicalEndpointPosition
forwardTarget filsingerGoldenRectangle = orthogonalModePhase
forwardTarget syntheticFibonacciApproximants = rationalLockingDetuning

-- Reverse physical admission is source- and SAME-OBJECT-bound.
record ReverseFieldAdmission (c : RatioClaim) : Set₁ where
  field
    selectedConductorGeometry : Set
    selectedMaxwellFieldBoundary : Set
    measuredComplexPortResponse : Set
    measuredSourceAndLoadRealWork : Set
    geometryReceipt : selectedConductorGeometry
    fieldReceipt : selectedMaxwellFieldBoundary
    responseReceipt : measuredComplexPortResponse
    workReceipt : measuredSourceAndLoadRealWork

-- Synthetic finite rational bookkeeping, NOT a proof of irrational phi
-- or a source claim that Smith used Fibonacci geometry.
record RationalRatio : Set where
  constructor _over_
  field
    numerator : Nat
    denominator : Nat

threeOverTwo : RationalRatio
threeOverTwo = 3 over 2

fiveOverThree : RationalRatio
fiveOverThree = 5 over 3

eightOverFive : RationalRatio
eightOverFive = 8 over 5

thirteenOverEight : RationalRatio
thirteenOverEight = 13 over 8

twentyOneOverThirteen : RationalRatio
twentyOneOverThirteen = 21 over 13

sameRatioBookkeeping : RationalRatio.numerator thirteenOverEight ≡ 13
sameRatioBookkeeping = refl
