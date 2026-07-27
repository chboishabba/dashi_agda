module DASHI.Physics.Closure.NSTriadKNPeriodicStokesModeDegeneracy where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_; ∣_∣)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Norm

------------------------------------------------------------------------
-- Concrete degeneracy of the first nonzero periodic Stokes shell.
--
-- The homogeneous periodic problem has no shear-selected leading direction.
-- Already the three positive coordinate modes are distinct and have the same
-- first-shell multiplier.  A coherence direction must therefore be selected
-- equivariantly/adaptively (or a whole eigenspace must be used).
------------------------------------------------------------------------

xMode yMode zMode : Z3.FourierMode
xMode = Z3.mode (+ 1) (+ 0) (+ 0)
yMode = Z3.mode (+ 0) (+ 1) (+ 0)
zMode = Z3.mode (+ 0) (+ 0) (+ 1)

stokesMultiplier : Z3.FourierMode → Nat
stokesMultiplier mode =
  ∣ Z3.kx mode ∣ * ∣ Z3.kx mode ∣
  + ∣ Z3.ky mode ∣ * ∣ Z3.ky mode ∣
  + ∣ Z3.kz mode ∣ * ∣ Z3.kz mode ∣

xModeFirstShell : Norm.infinityNorm xMode ≡ suc zero
xModeFirstShell = refl

yModeFirstShell : Norm.infinityNorm yMode ≡ suc zero
yModeFirstShell = refl

zModeFirstShell : Norm.infinityNorm zMode ≡ suc zero
zModeFirstShell = refl

xModeFirstStokesMultiplier : stokesMultiplier xMode ≡ suc zero
xModeFirstStokesMultiplier = refl

yModeFirstStokesMultiplier : stokesMultiplier yMode ≡ suc zero
yModeFirstStokesMultiplier = refl

zModeFirstStokesMultiplier : stokesMultiplier zMode ≡ suc zero
zModeFirstStokesMultiplier = refl

xMode≢yMode : xMode ≡ yMode → ⊥
xMode≢yMode ()

xMode≢zMode : xMode ≡ zMode → ⊥
xMode≢zMode ()

yMode≢zMode : yMode ≡ zMode → ⊥
yMode≢zMode ()

record FirstPeriodicShellDegeneracy : Set where
  constructor first-periodic-shell-degeneracy
  field
    first second third : Z3.FourierMode
    firstNorm : Norm.infinityNorm first ≡ suc zero
    secondNorm : Norm.infinityNorm second ≡ suc zero
    thirdNorm : Norm.infinityNorm third ≡ suc zero
    firstMultiplier : stokesMultiplier first ≡ suc zero
    secondMultiplier : stokesMultiplier second ≡ suc zero
    thirdMultiplier : stokesMultiplier third ≡ suc zero
    firstDistinctSecond : first ≡ second → ⊥
    firstDistinctThird : first ≡ third → ⊥
    secondDistinctThird : second ≡ third → ⊥

open FirstPeriodicShellDegeneracy public

firstPeriodicShellHasAtLeastThreeDirections :
  FirstPeriodicShellDegeneracy
firstPeriodicShellHasAtLeastThreeDirections =
  first-periodic-shell-degeneracy
    xMode yMode zMode
    xModeFirstShell yModeFirstShell zModeFirstShell
    xModeFirstStokesMultiplier
    yModeFirstStokesMultiplier
    zModeFirstStokesMultiplier
    xMode≢yMode xMode≢zMode yMode≢zMode

periodicFirstShellDegeneracyClosed : Bool
periodicFirstShellDegeneracyClosed = true

periodicFirstShellDegeneracyClosedIsTrue :
  periodicFirstShellDegeneracyClosed ≡ true
periodicFirstShellDegeneracyClosedIsTrue = refl

uniqueCoordinateLeadingModeExists : Bool
uniqueCoordinateLeadingModeExists = false

uniqueCoordinateLeadingModeExistsIsFalse :
  uniqueCoordinateLeadingModeExists ≡ false
uniqueCoordinateLeadingModeExistsIsFalse = refl
