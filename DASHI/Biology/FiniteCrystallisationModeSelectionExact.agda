module DASHI.Biology.FiniteCrystallisationModeSelectionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Finite exact analogue of shell degeneracy, resonant six-mode stars, and
-- coefficient-dependent stripe/hexagon selection.
--
-- Source-facing precedents are recorded in the round-four source atlas:
-- Swift--Hohenberg for finite-wavenumber instability and Cross--Hohenberg for
-- amplitude-equation pattern competition.  This module imports only the
-- combinatorial mode-star and a finite reduced-potential comparison, not a
-- continuum PDE.

data Direction6 : Set where
  direction0 : Direction6
  direction1 : Direction6
  direction2 : Direction6
  direction3 : Direction6
  direction4 : Direction6
  direction5 : Direction6

rotate60 : Direction6 → Direction6
rotate60 direction0 = direction1
rotate60 direction1 = direction2
rotate60 direction2 = direction3
rotate60 direction3 = direction4
rotate60 direction4 = direction5
rotate60 direction5 = direction0

rotate120 : Direction6 → Direction6
rotate120 d = rotate60 (rotate60 d)

oppositeDirection : Direction6 → Direction6
oppositeDirection d = rotate60 (rotate60 (rotate60 d))

sixfoldReturn :
  (d : Direction6) →
  rotate60 (rotate60 (rotate60 (rotate60 (rotate60 (rotate60 d))))) ≡ d
sixfoldReturn direction0 = refl
sixfoldReturn direction1 = refl
sixfoldReturn direction2 = refl
sixfoldReturn direction3 = refl
sixfoldReturn direction4 = refl
sixfoldReturn direction5 = refl

oppositeIsInvolutive :
  (d : Direction6) → oppositeDirection (oppositeDirection d) ≡ d
oppositeIsInvolutive direction0 = refl
oppositeIsInvolutive direction1 = refl
oppositeIsInvolutive direction2 = refl
oppositeIsInvolutive direction3 = refl
oppositeIsInvolutive direction4 = refl
oppositeIsInvolutive direction5 = refl

------------------------------------------------------------------------
-- Three directions separated by 120 degrees generate the six-direction star
-- after adjoining their opposites.

record ResonantModeTriad : Set where
  constructor resonantModeTriad
  field
    firstMode : Direction6
    secondMode : Direction6
    thirdMode : Direction6
    secondIsFirstPlus120 : secondMode ≡ rotate120 firstMode
    thirdIsSecondPlus120 : thirdMode ≡ rotate120 secondMode
    closesAfterThird : rotate120 thirdMode ≡ firstMode

open ResonantModeTriad public

canonicalResonantTriad : ResonantModeTriad
canonicalResonantTriad =
  resonantModeTriad direction0 direction2 direction4 refl refl refl

canonicalOppositeTriad : ResonantModeTriad
canonicalOppositeTriad =
  resonantModeTriad direction3 direction5 direction1 refl refl refl

------------------------------------------------------------------------
-- Finite reduced amplitude potential.
--
-- Occupations are restricted here to zero/one amplitudes.  The quartic regime
-- charges one unit per occupied mode.  The resonant regime additionally
-- penalises an incomplete triad and rewards a closed triad.  The resulting
-- numbers are not fitted physical coefficients, but the branch ordering is
-- derived from one explicit formula rather than stored as a lookup table.

data PatternBranch : Set where
  stripeBranch : PatternBranch
  hexagonalBranch : PatternBranch

data CouplingRegime : Set where
  reflectionSymmetricQuarticRegime : CouplingRegime
  resonantTriadCoupledRegime : CouplingRegime

record ModeOccupation : Set where
  constructor modeOccupation
  field
    firstOccupied : Bool
    secondOccupied : Bool
    thirdOccupied : Bool

open ModeOccupation public

occupationFor : PatternBranch → ModeOccupation
occupationFor stripeBranch = modeOccupation true false false
occupationFor hexagonalBranch = modeOccupation true true true

boolToNat : Bool → Nat
boolToNat false = 0
boolToNat true = 1

andBool : Bool → Bool → Bool
andBool true true = true
andBool _ _ = false

allThreeOccupied : ModeOccupation → Bool
allThreeOccupied occupation =
  andBool
    (firstOccupied occupation)
    (andBool (secondOccupied occupation) (thirdOccupied occupation))

activeModeCount : ModeOccupation → Nat
activeModeCount occupation =
  boolToNat (firstOccupied occupation)
  + boolToNat (secondOccupied occupation)
  + boolToNat (thirdOccupied occupation)

missingTriadPenalty : CouplingRegime → ModeOccupation → Nat
missingTriadPenalty reflectionSymmetricQuarticRegime occupation = 0
missingTriadPenalty resonantTriadCoupledRegime occupation with allThreeOccupied occupation
... | true = 0
... | false = 2

closedTriadReward : CouplingRegime → ModeOccupation → Nat
closedTriadReward reflectionSymmetricQuarticRegime occupation = 0
closedTriadReward resonantTriadCoupledRegime occupation with allThreeOccupied occupation
... | true = 2
... | false = 0

reducedModeScore : CouplingRegime → ModeOccupation → Nat
reducedModeScore regime occupation =
  (activeModeCount occupation + missingTriadPenalty regime occupation)
  ∸
  closedTriadReward regime occupation

branchScore : CouplingRegime → PatternBranch → Nat
branchScore regime branch = reducedModeScore regime (occupationFor branch)

quarticStripeScoreIsOne :
  branchScore reflectionSymmetricQuarticRegime stripeBranch ≡ 1
quarticStripeScoreIsOne = refl

quarticHexagonScoreIsThree :
  branchScore reflectionSymmetricQuarticRegime hexagonalBranch ≡ 3
quarticHexagonScoreIsThree = refl

resonantStripeScoreIsThree :
  branchScore resonantTriadCoupledRegime stripeBranch ≡ 3
resonantStripeScoreIsThree = refl

resonantHexagonScoreIsOne :
  branchScore resonantTriadCoupledRegime hexagonalBranch ≡ 1
resonantHexagonScoreIsOne = refl

stripeWinsWithoutTriadCoupling :
  (branch : PatternBranch) →
  branchScore reflectionSymmetricQuarticRegime stripeBranch
  ≤
  branchScore reflectionSymmetricQuarticRegime branch
stripeWinsWithoutTriadCoupling stripeBranch = ≤-refl
stripeWinsWithoutTriadCoupling hexagonalBranch = s≤s z≤n

hexagonWinsWithTriadCoupling :
  (branch : PatternBranch) →
  branchScore resonantTriadCoupledRegime hexagonalBranch
  ≤
  branchScore resonantTriadCoupledRegime branch
hexagonWinsWithTriadCoupling stripeBranch = s≤s z≤n
hexagonWinsWithTriadCoupling hexagonalBranch = ≤-refl

------------------------------------------------------------------------
-- Periodic translation order and visible cell shape are separate labels.

data BravaisCarrier2D : Set where
  obliqueCarrier : BravaisCarrier2D
  rectangularCarrier : BravaisCarrier2D
  squareCarrier : BravaisCarrier2D
  triangularCarrier : BravaisCarrier2D

data VisibleCellDescription : Set where
  stripeCells : VisibleCellDescription
  squareCells : VisibleCellDescription
  triangularPeaks : VisibleCellDescription
  hexagonalCells : VisibleCellDescription

record CrystalDescription : Set where
  constructor crystalDescription
  field
    translationCarrier : BravaisCarrier2D
    visibleCells : VisibleCellDescription
    pointSymmetryOrder : Nat

open CrystalDescription public

canonicalHexagonalPattern : CrystalDescription
canonicalHexagonalPattern =
  crystalDescription triangularCarrier hexagonalCells 6

hexagonalCellsUseTriangularCarrier :
  translationCarrier canonicalHexagonalPattern ≡ triangularCarrier
hexagonalCellsUseTriangularCarrier = refl

record CrystallisationModeBoundary : Set where
  constructor crystallisationModeBoundary
  field
    isotropicShellUniquelySelectsHexagons : Bool
    isotropicShellUniquelySelectsHexagonsIsFalse :
      isotropicShellUniquelySelectsHexagons ≡ false

    quarticReflectionSymmetryAutomaticallyCreatesTriadCoupling : Bool
    quarticReflectionSymmetryAutomaticallyCreatesTriadCouplingIsFalse :
      quarticReflectionSymmetryAutomaticallyCreatesTriadCoupling ≡ false

    visibleHexagonsImplyHexagonalBravaisCarrier : Bool
    visibleHexagonsImplyHexagonalBravaisCarrierIsFalse :
      visibleHexagonsImplyHexagonalBravaisCarrier ≡ false

open CrystallisationModeBoundary public

canonicalCrystallisationModeBoundary : CrystallisationModeBoundary
canonicalCrystallisationModeBoundary =
  crystallisationModeBoundary false refl false refl false refl
