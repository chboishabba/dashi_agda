module DASHI.Physics.SyntheticOneMinusShellRealization where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Base using (List)

open import DASHI.Physics.OneMinusShellFamily as OMSF
open import DASHI.Physics.OneMinusShellFamilyParametric as OMSFP
open import DASHI.Physics.ShellNeighborhoodClass as SNC
open import DASHI.Physics.OrbitProfileData as OPD

label : String
label = "synthetic-one-minus-shell-family"

shell1Profile : List Nat
shell1Profile = OMSF.familyFormulaShell1 4

-- Synthetic shell-side candidate:
-- shell 1 is theorem-sourced from the parametric one-minus family,
-- while shell 2 is currently fixed to the present 4D Lorentz-reference
-- profile as a synthetic target only. This is enough to make the candidate
-- "profile-aware" without pretending it is already an admissible realization.

shell2Profile : List Nat
shell2Profile = OPD.shell2_p3_q1

shellNeighborhood : SNC.ShellNeighborhoodClass
shellNeighborhood = SNC.classifyShell1Neighborhood shell1Profile

shellNeighborhood-theorem :
  shellNeighborhood ≡ SNC.oneMinusShellNeighborhood
shellNeighborhood-theorem = OMSFP.familyFormulaNeighborhood-theorem 2
