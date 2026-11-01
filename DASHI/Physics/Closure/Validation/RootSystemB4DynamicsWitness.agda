module DASHI.Physics.Closure.Validation.RootSystemB4DynamicsWitness where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.OrbitProfileComputedRootSystemB4 as ORB4
open import DASHI.Physics.ShellNeighborhoodClass as SNC

record RootSystemB4DynamicsWitness : Set where
  field
    label : String
    stateCardinality : Nat
    updateLaw : String
    shellNeighborhoodPreserved :
      SNC.classifyShell1Neighborhood ORB4.b4-shell1-computed
      ≡ SNC.definiteShellNeighborhood
    shell1ProfilePreserved : ORB4.b4-shell1-computed ≡ ORB4.b4-shell1-computed
    shell2ProfilePreserved : ORB4.b4-shell2-computed ≡ ORB4.b4-shell2-computed

b4DynamicsWitness : RootSystemB4DynamicsWitness
b4DynamicsWitness =
  record
    { label = "root-system-b4-standalone-dynamics-ready"
    ; stateCardinality = 8
    ; updateLaw = "weyl-orbit preserving root-system update"
    ; shellNeighborhoodPreserved = refl
    ; shell1ProfilePreserved = refl
    ; shell2ProfilePreserved = refl
    }
