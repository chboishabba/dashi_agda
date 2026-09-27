{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyHamiltonianTransportAuthorityExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologyExact as QM
import DASHI.Quantum.QuantumMereologyOperatorLocalityAuthorityExact as Locality
import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- SYMMETRIC HAMILTONIAN-CANDIDATE TRANSPORT AUTHORITY
--
-- Concrete tensor coordinates and symmetry preservation are theorem-owned by
-- the Lean/mathlib side. Agda carries only explicit authority sockets.
------------------------------------------------------------------------

record SymmetricHamiltonianCandidateAuthority
    (W : QM.BareQuantumWorld)
    (T : QM.TensorProductStructure W) : Set₁ where
  field
    operatorLocalityAuthority :
      Locality.OperatorLocalityAuthority W T

    GlobalSymmetryAuthority : Set
    globalSymmetryAuthority :
      GlobalSymmetryAuthority

    LeftSymmetryAuthority : Set
    leftSymmetryAuthority :
      LeftSymmetryAuthority

    RightSymmetryAuthority : Set
    rightSymmetryAuthority :
      RightSymmetryAuthority

    InteractionSymmetryAuthority : Set
    interactionSymmetryAuthority :
      InteractionSymmetryAuthority

    PullbackSymmetryTransportAuthority : Set
    pullbackSymmetryTransportAuthority :
      PullbackSymmetryTransportAuthority

open SymmetricHamiltonianCandidateAuthority public

record HamiltonianTransportPromotionBoundary : Set where
  field
    symmetryAuthorityCreatesMeasuredHamiltonian : Bool
    symmetryAuthorityCreatesMeasuredHamiltonianIsFalse :
      symmetryAuthorityCreatesMeasuredHamiltonian ≡ false

    symmetryAuthoritySelectsPreferredTPS : Bool
    symmetryAuthoritySelectsPreferredTPSIsFalse :
      symmetryAuthoritySelectsPreferredTPS ≡ false

    symmetryAuthorityCreatesQuasiclassicalDynamics : Bool
    symmetryAuthorityCreatesQuasiclassicalDynamicsIsFalse :
      symmetryAuthorityCreatesQuasiclassicalDynamics ≡ false

canonicalHamiltonianTransportPromotionBoundary :
  HamiltonianTransportPromotionBoundary
canonicalHamiltonianTransportPromotionBoundary = record
  { symmetryAuthorityCreatesMeasuredHamiltonian = false
  ; symmetryAuthorityCreatesMeasuredHamiltonianIsFalse = refl
  ; symmetryAuthoritySelectsPreferredTPS = false
  ; symmetryAuthoritySelectsPreferredTPSIsFalse = refl
  ; symmetryAuthorityCreatesQuasiclassicalDynamics = false
  ; symmetryAuthorityCreatesQuasiclassicalDynamicsIsFalse = refl
  }

leanHamiltonianTransportSourceWrittenReceipt : Sources.AttributionReceipt
leanHamiltonianTransportSourceWrittenReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyHamiltonianTransport"
    "Source-written Lean owner specialising mathlib symmetric-operator conjugation to the declared inner-product TPS. This is source lineage only until exact-head Lean kernel/build evidence exists."

agdaHamiltonianTransportAuthorityReceipt : Sources.AttributionReceipt
agdaHamiltonianTransportAuthorityReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Agda exposes symmetry and coordinate-transport authority sockets layered over operator locality; it makes no empirical Hamiltonian or preferred-TPS claim."
