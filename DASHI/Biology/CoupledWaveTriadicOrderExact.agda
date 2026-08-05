module DASHI.Biology.CoupledWaveTriadicOrderExact where

open import DASHI.Core.Prelude
open import DASHI.Biology.TriadicKernelLiftQuotientExact

import DASHI.Biology.FiniteCrystallisationModeSelectionExact as Modes

------------------------------------------------------------------------
-- Finite coupled analogue of a continuous mode-amplitude sector and a
-- discrete nine-sheet internal sector.  The joint objective separates wave
-- selection, discrete compatibility, and residual defect.

record ThreeModeAmplitude : Set where
  constructor threeModeAmplitude
  field
    amplitudeOne : Nat
    amplitudeTwo : Nat
    amplitudeThree : Nat

open ThreeModeAmplitude public

stripeAmplitude : ThreeModeAmplitude
stripeAmplitude = threeModeAmplitude 2 0 0

hexagonalAmplitude : ThreeModeAmplitude
hexagonalAmplitude = threeModeAmplitude 1 1 1

amplitudeMass : ThreeModeAmplitude → Nat
amplitudeMass a = amplitudeOne a + amplitudeTwo a + amplitudeThree a

stripeMassIsTwo : amplitudeMass stripeAmplitude ≡ 2
stripeMassIsTwo = refl

hexagonalMassIsThree : amplitudeMass hexagonalAmplitude ≡ 3
hexagonalMassIsThree = refl

preferredBranchForOrbit : NineOrbit → Modes.PatternBranch
preferredBranchForOrbit zeroOrbit = Modes.stripeBranch
preferredBranchForOrbit firstAxisOrbit = Modes.stripeBranch
preferredBranchForOrbit secondAxisOrbit = Modes.stripeBranch
preferredBranchForOrbit equalSignOrbit = Modes.hexagonalBranch
preferredBranchForOrbit oppositeSignOrbit = Modes.hexagonalBranch

sameBranch : Modes.PatternBranch → Modes.PatternBranch → Bool
sameBranch Modes.stripeBranch Modes.stripeBranch = true
sameBranch Modes.hexagonalBranch Modes.hexagonalBranch = true
sameBranch _ _ = false

compatibilityPenalty : NineOrbit → Modes.PatternBranch → Nat
compatibilityPenalty orbit branch with sameBranch (preferredBranchForOrbit orbit) branch
... | true = 0
... | false = 2

record JointCandidate : Set where
  constructor jointCandidate
  field
    waveBranch : Modes.PatternBranch
    internalOrbit : NineOrbit
    residualDefect : Nat

open JointCandidate public

jointObjective : JointCandidate → Nat
jointObjective candidate =
  Modes.branchScore Modes.resonantTriadCoupledRegime (waveBranch candidate)
  + compatibilityPenalty (internalOrbit candidate) (waveBranch candidate)
  + residualDefect candidate

alignedHexagonalCandidate : JointCandidate
alignedHexagonalCandidate =
  jointCandidate Modes.hexagonalBranch equalSignOrbit 0

misalignedHexagonalCandidate : JointCandidate
misalignedHexagonalCandidate =
  jointCandidate Modes.hexagonalBranch firstAxisOrbit 1

alignedStripeCandidate : JointCandidate
alignedStripeCandidate =
  jointCandidate Modes.stripeBranch firstAxisOrbit 1

alignedHexagonalObjectiveIsOne :
  jointObjective alignedHexagonalCandidate ≡ 1
alignedHexagonalObjectiveIsOne = refl

misalignedHexagonalObjectiveIsFour :
  jointObjective misalignedHexagonalCandidate ≡ 4
misalignedHexagonalObjectiveIsFour = refl

alignedStripeObjectiveIsFour :
  jointObjective alignedStripeCandidate ≡ 4
alignedStripeObjectiveIsFour = refl

------------------------------------------------------------------------
-- Gibbsian code-length correspondence as an exact affine transform on the
-- finite energy score.  This is a conditional correspondence, not an identity
-- between every thermodynamic free energy and every MDL functional.

gibbsCodeLength : Nat → Nat
gibbsCodeLength energy = 2 * energy + 5

alignedHexagonalCodeLength :
  gibbsCodeLength (jointObjective alignedHexagonalCandidate) ≡ 7
alignedHexagonalCodeLength = refl

misalignedHexagonalCodeLength :
  gibbsCodeLength (jointObjective misalignedHexagonalCandidate) ≡ 13
misalignedHexagonalCodeLength = refl

record CoupledOrderBoundary : Set where
  constructor coupledOrderBoundary
  field
    discreteNineSheetIsDefinitionallyContinuousAmplitude : Bool
    discreteNineSheetIsDefinitionallyContinuousAmplitudeIsFalse :
      discreteNineSheetIsDefinitionallyContinuousAmplitude ≡ false

    freeEnergyEqualsEveryDescriptionLengthFunctional : Bool
    freeEnergyEqualsEveryDescriptionLengthFunctionalIsFalse :
      freeEnergyEqualsEveryDescriptionLengthFunctional ≡ false

    localObjectiveMinimumProvesPhysicalCrystal : Bool
    localObjectiveMinimumProvesPhysicalCrystalIsFalse :
      localObjectiveMinimumProvesPhysicalCrystal ≡ false

open CoupledOrderBoundary public

canonicalCoupledOrderBoundary : CoupledOrderBoundary
canonicalCoupledOrderBoundary =
  coupledOrderBoundary false refl false refl false refl
