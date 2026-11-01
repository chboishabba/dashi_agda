module DASHI.Biology.FiniteWaveShellGradientExact where

open import DASHI.Core.Prelude

import DASHI.Biology.FiniteCrystallisationModeSelectionExact as Modes

------------------------------------------------------------------------
-- Exact finite shell-selection analogue of the quadratic
-- |(Delta+k0^2) psi|^2 term.  The shell penalty is zero exactly at the selected
-- squared wavenumber.  This selects a degenerate shell class, not one lattice
-- branch inside that shell.

data WaveNumberClass : Set where
  zeroWaveNumber : WaveNumberClass
  selectedWaveNumber : WaveNumberClass
  highWaveNumber : WaveNumberClass

squaredWaveNumber : WaveNumberClass → Nat
squaredWaveNumber zeroWaveNumber = 0
squaredWaveNumber selectedWaveNumber = 1
squaredWaveNumber highWaveNumber = 4

selectedSquaredWaveNumber : Nat
selectedSquaredWaveNumber = 1

natDistance : Nat → Nat → Nat
natDistance x y = (x ∸ y) + (y ∸ x)

shellPenalty : WaveNumberClass → Nat
shellPenalty k =
  let d = natDistance (squaredWaveNumber k) selectedSquaredWaveNumber
  in d * d

zeroModePenaltyIsOne : shellPenalty zeroWaveNumber ≡ 1
zeroModePenaltyIsOne = refl

selectedModePenaltyIsZero : shellPenalty selectedWaveNumber ≡ 0
selectedModePenaltyIsZero = refl

highModePenaltyIsNine : shellPenalty highWaveNumber ≡ 9
highModePenaltyIsNine = refl

selectedShellMinimisesQuadraticPenalty :
  (k : WaveNumberClass) →
  shellPenalty selectedWaveNumber ≤ shellPenalty k
selectedShellMinimisesQuadraticPenalty zeroWaveNumber = z≤n
selectedShellMinimisesQuadraticPenalty selectedWaveNumber = z≤n
selectedShellMinimisesQuadraticPenalty highWaveNumber = z≤n

quadraticModeEnergy : WaveNumberClass → Nat → Nat
quadraticModeEnergy k amplitude = shellPenalty k * amplitude * amplitude

selectedShellHasZeroQuadraticEnergy :
  (amplitude : Nat) →
  quadraticModeEnergy selectedWaveNumber amplitude ≡ 0
selectedShellHasZeroQuadraticEnergy amplitude = refl

------------------------------------------------------------------------
-- The selected shell still contains competing nonlinear branches.  Reusing
-- the exact coefficient regimes from the mode module makes that separation
-- explicit.

shellAndBranchScore :
  WaveNumberClass → Modes.CouplingRegime → Modes.PatternBranch → Nat
shellAndBranchScore k regime branch =
  shellPenalty k + Modes.branchScore regime branch

sameShellDifferentBranchScores :
  shellAndBranchScore
    selectedWaveNumber
    Modes.reflectionSymmetricQuarticRegime
    Modes.stripeBranch
  ≡
  1
  ×
  shellAndBranchScore
    selectedWaveNumber
    Modes.reflectionSymmetricQuarticRegime
    Modes.hexagonalBranch
  ≡
  3
sameShellDifferentBranchScores = refl , refl

record WaveShellBoundary : Set where
  constructor waveShellBoundary
  field
    zeroShellPenaltySelectsUniqueDirection : Bool
    zeroShellPenaltySelectsUniqueDirectionIsFalse :
      zeroShellPenaltySelectsUniqueDirection ≡ false

    linearShellSelectionDeterminesNonlinearBranch : Bool
    linearShellSelectionDeterminesNonlinearBranchIsFalse :
      linearShellSelectionDeterminesNonlinearBranch ≡ false

    finitePenaltyIsContinuumVariationalDerivative : Bool
    finitePenaltyIsContinuumVariationalDerivativeIsFalse :
      finitePenaltyIsContinuumVariationalDerivative ≡ false

open WaveShellBoundary public

canonicalWaveShellBoundary : WaveShellBoundary
canonicalWaveShellBoundary =
  waveShellBoundary false refl false refl false refl
