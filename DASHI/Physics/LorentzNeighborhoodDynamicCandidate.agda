module DASHI.Physics.LorentzNeighborhoodDynamicCandidate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.ShellNeighborhoodClass as SNC
import DASHI.Physics.SyntheticOneMinusShellRealization as SOM
open import DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness as SODW

data DynamicCandidateStatus : Set where
  prototypeScaffoldOnly : DynamicCandidateStatus
  shellProfileBacked : DynamicCandidateStatus
  admissibleDynamicReady : DynamicCandidateStatus

record LorentzNeighborhoodDynamicCandidate : Set where
  field
    label : String
    stateCardinality : Nat
    updateLaw : String
    shellNeighborhood : SNC.ShellNeighborhoodClass
    hasIndependentDynamics : Bool
    hasShell2Structure : Bool
    hasOrientation : Bool
    hasSignature : Bool
    preservesShellNeighborhood : Bool
    preservesShellProfile : Bool
    status : DynamicCandidateStatus

prototype : LorentzNeighborhoodDynamicCandidate
prototype =
  record
    { label = "lorentz-neighborhood-dynamic-prototype"
    ; stateCardinality = 2
    ; updateLaw = "prototype-shell-toggle"
    ; shellNeighborhood = SOM.shellNeighborhood
    ; hasIndependentDynamics = false
    ; hasShell2Structure = true
    ; hasOrientation = false
    ; hasSignature = false
    ; preservesShellNeighborhood = false
    ; preservesShellProfile = false
    ; status = prototypeScaffoldOnly
    }

syntheticReady : LorentzNeighborhoodDynamicCandidate
syntheticReady =
  record
    { label = SODW.SyntheticOneMinusDynamicsWitness.label SODW.syntheticDynamicsWitness
    ; stateCardinality = SODW.SyntheticOneMinusDynamicsWitness.stateCardinality SODW.syntheticDynamicsWitness
    ; updateLaw = SODW.SyntheticOneMinusDynamicsWitness.updateLaw SODW.syntheticDynamicsWitness
    ; shellNeighborhood = SOM.shellNeighborhood
    ; hasIndependentDynamics = true
    ; hasShell2Structure = true
    ; hasOrientation = true
    ; hasSignature = true
    ; preservesShellNeighborhood = true
    ; preservesShellProfile = true
    ; status = admissibleDynamicReady
    }
