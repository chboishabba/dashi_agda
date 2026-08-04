module DASHI.Reasoning.SinthomeTypedStabilisation where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Source calibration: Jacques Lacan, The Seminar of Jacques Lacan, Book
-- XXIII, The Sinthome (1975-1976); Will Greenshields, Writing the Structures
-- of the Subject: Lacan and Topology, DOI 10.1007/978-3-319-47533-2.
--
-- Stabilisation is indexed by a path and residual.  Coherence restoration,
-- residual retention, memory preservation and non-equivalence to erasure are
-- proof fields rather than Boolean declarations.
------------------------------------------------------------------------

data StabilisationMode : Set where
  eraseMode suppressMode sinthomaticIntegrationMode : StabilisationMode

record StabilisationPath : Set where
  field
    pathSteps : List String
    sourceVersion : String
    targetVersion : String
    pathProvenance : List String
    pathReceipt : String

open StabilisationPath public

record AdmissibleSinthome
    (State : Set)
    (Coherent : State → Set)
    (ResidualPresent : Residual.ResidualLevel → State → Set)
    (MemoryPreserved : State → State → Set)
    (Equivalent : State → State → Set) : Set₁ where
  field
    before : State
    after : State
    erasureCandidate : State
    residual : Residual.ResidualLevel
    path : StabilisationPath
    coherenceAfter : Coherent after
    residualAfter : ResidualPresent residual after
    memoryFromBefore : MemoryPreserved before after
    notEquivalentToErasure : ¬ Equivalent after erasureCandidate
    mode : StabilisationMode
    modeIsSinthomatic : mode ≡ sinthomaticIntegrationMode
    stabilisationReceipt : String

open AdmissibleSinthome public

sinthomeRestoresCoherence :
  ∀ {State : Set}
    {Coherent : State → Set}
    {ResidualPresent : Residual.ResidualLevel → State → Set}
    {MemoryPreserved : State → State → Set}
    {Equivalent : State → State → Set} →
  (witness :
    AdmissibleSinthome
      State Coherent ResidualPresent MemoryPreserved Equivalent) →
  Coherent (after witness)
sinthomeRestoresCoherence witness = coherenceAfter witness

sinthomeRetainsResidual :
  ∀ {State : Set}
    {Coherent : State → Set}
    {ResidualPresent : Residual.ResidualLevel → State → Set}
    {MemoryPreserved : State → State → Set}
    {Equivalent : State → State → Set} →
  (witness :
    AdmissibleSinthome
      State Coherent ResidualPresent MemoryPreserved Equivalent) →
  ResidualPresent (residual witness) (after witness)
sinthomeRetainsResidual witness = residualAfter witness

sinthomePreservesMemory :
  ∀ {State : Set}
    {Coherent : State → Set}
    {ResidualPresent : Residual.ResidualLevel → State → Set}
    {MemoryPreserved : State → State → Set}
    {Equivalent : State → State → Set} →
  (witness :
    AdmissibleSinthome
      State Coherent ResidualPresent MemoryPreserved Equivalent) →
  MemoryPreserved (before witness) (after witness)
sinthomePreservesMemory witness = memoryFromBefore witness

sinthomeIsNotErasure :
  ∀ {State : Set}
    {Coherent : State → Set}
    {ResidualPresent : Residual.ResidualLevel → State → Set}
    {MemoryPreserved : State → State → Set}
    {Equivalent : State → State → Set} →
  (witness :
    AdmissibleSinthome
      State Coherent ResidualPresent MemoryPreserved Equivalent) →
  ¬ Equivalent (after witness) (erasureCandidate witness)
sinthomeIsNotErasure witness = notEquivalentToErasure witness

record MinimalSinthomeCandidate
    (State Transformation : Set) : Set₁ where
  field
    apply : Transformation → State → State
    cost : Transformation → Nat
    coherentAfter : Transformation → State → Set
    selected : Transformation
    selectedRestoresCoherence : (state : State) → coherentAfter selected state
    selectedMinimalAmong : Transformation → Set
    minimalityWitness :
      ∀ alternative →
      selectedMinimalAmong alternative →
      cost selected ≤ cost alternative
    minimalityScope : String

record SinthomeTypedAuthorityBoundary : Set where
  field
    pathIndexedStabilisationAvailable : Bool
    coherenceWitnessTyped : Bool
    residualRetentionWitnessTyped : Bool
    memoryPreservationWitnessTyped : Bool
    nonErasureWitnessTyped : Bool
    minimalityAutomaticallyAvailable : Bool
    clinicalCureClaimed : Bool
    boundaryNote : String

canonicalSinthomeTypedAuthorityBoundary :
  SinthomeTypedAuthorityBoundary
canonicalSinthomeTypedAuthorityBoundary = record
  { pathIndexedStabilisationAvailable = true
  ; coherenceWitnessTyped = true
  ; residualRetentionWitnessTyped = true
  ; memoryPreservationWitnessTyped = true
  ; nonErasureWitnessTyped = true
  ; minimalityAutomaticallyAvailable = false
  ; clinicalCureClaimed = false
  ; boundaryNote =
      "An admissible sinthome is a path-dependent, provenance-bearing reorganisation with typed coherence, residual, memory and non-erasure witnesses. Minimality needs an explicit cost model."
  }
