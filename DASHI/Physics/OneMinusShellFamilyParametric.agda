module DASHI.Physics.OneMinusShellFamilyParametric where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Bool using (true)
open import Data.Nat.Base using (_*_; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.OneMinusShellFamily as OMSF
open import DASHI.Physics.ShellNeighborhoodClass as SNC
open import DASHI.Physics.OrbitProfileData as OPD

familyFormulaNeighborhood : Nat → SNC.ShellNeighborhoodClass
familyFormulaNeighborhood zero = SNC.unknownShellNeighborhood
familyFormulaNeighborhood (suc zero) = SNC.unknownShellNeighborhood
familyFormulaNeighborhood (suc (suc zero)) = SNC.oneMinusShellNeighborhood
familyFormulaNeighborhood (suc (suc (suc zero))) = SNC.oneMinusShellNeighborhood
familyFormulaNeighborhood (suc (suc (suc (suc m)))) =
  let b = 2 * (suc (suc (suc m)) ∸ 1)
  in SNC.classifyTriple (b * (b ∸ 2)) b 2

familyFormulaNeighborhood-theorem :
  ∀ m → familyFormulaNeighborhood (suc (suc m)) ≡ SNC.oneMinusShellNeighborhood
familyFormulaNeighborhood-theorem zero = refl
familyFormulaNeighborhood-theorem (suc zero) = refl
familyFormulaNeighborhood-theorem (suc (suc m)) =
  SNC.classifyTriple-oneMinus (2 * (suc (suc (suc m)) ∸ 1))

shiftMatchesParametricFamily :
  SNC.classifyShell1Neighborhood OPD.shell1_p3_q1
  ≡ SNC.oneMinusShellNeighborhood
shiftMatchesParametricFamily = refl
