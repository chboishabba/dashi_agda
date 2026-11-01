module DASHI.Physics.OneMinusShellFamily where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_*_; _∸_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.ShellNeighborhoodClass as SNC

record OneMinusShell1Member : Set where
  field
    dimension : Nat
    shell1Top : List Nat

oneMinusShell1TopFromB : Nat → List Nat
oneMinusShell1TopFromB b = (b * (b ∸ 2)) ∷ b ∷ 2 ∷ []

formula≥4 : Nat → List Nat
formula≥4 m =
  let b = 2 * (m ∸ 1)
  in oneMinusShell1TopFromB b

familyFormulaShell1 : Nat → List Nat
familyFormulaShell1 zero = []
familyFormulaShell1 (suc zero) = []
familyFormulaShell1 (suc (suc zero)) = 2 ∷ 2 ∷ []
familyFormulaShell1 (suc (suc (suc zero))) = 8 ∷ 4 ∷ 2 ∷ []
familyFormulaShell1 m = formula≥4 m

member2 : OneMinusShell1Member
member2 = record { dimension = 2 ; shell1Top = 2 ∷ 2 ∷ [] }

member3 : OneMinusShell1Member
member3 = record { dimension = 3 ; shell1Top = OPD.shell1_p2_q1 }

member4 : OneMinusShell1Member
member4 = record { dimension = 4 ; shell1Top = OPD.shell1_p3_q1 }

member5 : OneMinusShell1Member
member5 = record { dimension = 5 ; shell1Top = 48 ∷ 8 ∷ 2 ∷ [] }

member6 : OneMinusShell1Member
member6 = record { dimension = 6 ; shell1Top = 80 ∷ 10 ∷ 2 ∷ [] }

member7 : OneMinusShell1Member
member7 = record { dimension = 7 ; shell1Top = 120 ∷ 12 ∷ 2 ∷ [] }

member8 : OneMinusShell1Member
member8 = record { dimension = 8 ; shell1Top = 168 ∷ 14 ∷ 2 ∷ [] }

member2-formula : OneMinusShell1Member.shell1Top member2 ≡ familyFormulaShell1 2
member2-formula = refl

member3-formula : OneMinusShell1Member.shell1Top member3 ≡ familyFormulaShell1 3
member3-formula = refl

member4-formula : OneMinusShell1Member.shell1Top member4 ≡ familyFormulaShell1 4
member4-formula = refl

member5-formula : OneMinusShell1Member.shell1Top member5 ≡ familyFormulaShell1 5
member5-formula = refl

member6-formula : OneMinusShell1Member.shell1Top member6 ≡ familyFormulaShell1 6
member6-formula = refl

member7-formula : OneMinusShell1Member.shell1Top member7 ≡ familyFormulaShell1 7
member7-formula = refl

member8-formula : OneMinusShell1Member.shell1Top member8 ≡ familyFormulaShell1 8
member8-formula = refl

member2-neighborhood :
  SNC.classifyShell1Neighborhood (OneMinusShell1Member.shell1Top member2)
  ≡ SNC.oneMinusShellNeighborhood
member2-neighborhood = refl

member3-neighborhood :
  SNC.classifyShell1Neighborhood (OneMinusShell1Member.shell1Top member3)
  ≡ SNC.oneMinusShellNeighborhood
member3-neighborhood = refl

member4-neighborhood :
  SNC.classifyShell1Neighborhood (OneMinusShell1Member.shell1Top member4)
  ≡ SNC.oneMinusShellNeighborhood
member4-neighborhood = refl

member5-neighborhood :
  SNC.classifyShell1Neighborhood (OneMinusShell1Member.shell1Top member5)
  ≡ SNC.oneMinusShellNeighborhood
member5-neighborhood = refl

member6-neighborhood :
  SNC.classifyShell1Neighborhood (OneMinusShell1Member.shell1Top member6)
  ≡ SNC.oneMinusShellNeighborhood
member6-neighborhood = refl

member7-neighborhood :
  SNC.classifyShell1Neighborhood (OneMinusShell1Member.shell1Top member7)
  ≡ SNC.oneMinusShellNeighborhood
member7-neighborhood = refl

member8-neighborhood :
  SNC.classifyShell1Neighborhood (OneMinusShell1Member.shell1Top member8)
  ≡ SNC.oneMinusShellNeighborhood
member8-neighborhood = refl
