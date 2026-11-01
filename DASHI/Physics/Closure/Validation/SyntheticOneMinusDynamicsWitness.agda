module DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.ShellNeighborhoodClass as SNC
import DASHI.Physics.SyntheticOneMinusShellRealization as SOM

record SyntheticOneMinusDynamicsWitness : Set where
  field
    label : String
    stateCardinality : Nat
    updateLaw : String
    shellNeighborhoodPreserved :
      SOM.shellNeighborhood ≡ SNC.oneMinusShellNeighborhood
    shell1ProfilePreserved : SOM.shell1Profile ≡ OPD.shell1_p3_q1
    shell2ProfilePreserved : SOM.shell2Profile ≡ OPD.shell2_p3_q1

syntheticDynamicsWitness : SyntheticOneMinusDynamicsWitness
syntheticDynamicsWitness =
  record
    { label = "synthetic-one-minus-admissible-dynamics"
    ; stateCardinality = 2
    ; updateLaw = "two-state profile-preserving synthetic update"
    ; shellNeighborhoodPreserved = SOM.shellNeighborhood-theorem
    ; shell1ProfilePreserved = refl
    ; shell2ProfilePreserved = refl
    }
