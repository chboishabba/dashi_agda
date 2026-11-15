module DASHI.Physics.Chemistry.AtomicPeriodicTable369HamiltonianCarrierAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Same-carrier Hamiltonian audit.
--
-- The repository has several legitimate Hamiltonian/energy producers around
-- the atomic lane.  This file records their roles without importing sibling
-- draft branches as theorem authority and without collapsing different bases.
------------------------------------------------------------------------

record HamiltonianCarrierReceipt : Set where
  constructor hamiltonianCarrierReceipt
  field
    owner : String
    carrier : String
    role : String
    sameCarrierAsSelectedAtomicPTriplet : Bool
    sameCarrierAsSelectedAtomicManyBodyExteriorLift : Bool

open HamiltonianCarrierReceipt public

liBeMinimalBasisSCFReceipt : HamiltonianCarrierReceipt
liBeMinimalBasisSCFReceipt =
  hamiltonianCarrierReceipt
    "AtomicPeriodicTable369LiBeMinimalBasisHFExecutionExact / scripts/atomic_li_be_sto3g_scf.py"
    "same-centre STO-3G 1s/2s Gaussian orbital basis for Li/Be"
    "repository-owned self-consistent Fock/HF execution; basis parameters externally attributed"
    false
    false

ammoniaHamiltonianReceipt : HamiltonianCarrierReceipt
ammoniaHamiltonianReceipt =
  hamiltonianCarrierReceipt
    "sibling PR #1162: AmmoniaHamiltonianWavefunctionExact"
    "NH3 molecular electronic/nuclear symbolic Hamiltonian carrier"
    "source-bounded molecular Hamiltonian expression; sibling draft authority only until reconciled"
    false
    false

coTaHamiltonianReceipt : HamiltonianCarrierReceipt
coTaHamiltonianReceipt =
  hamiltonianCarrierReceipt
    "sibling PR #1115: sourced four-site kagome donor / future CoTa4Se8 Wannier carrier"
    "Y1,Y2,Y3,Y4 material orbital/site basis; future literal material Wannier basis"
    "condensed-matter donor/material Hamiltonian lane"
    false
    false

hydrogenicPTripletReceipt : HamiltonianCarrierReceipt
hydrogenicPTripletReceipt =
  hamiltonianCarrierReceipt
    "AtomicPeriodicTable369HamiltonianC3IntertwinerExact"
    "selected n=2,l=1 magnetic triplet"
    "restricted hydrogenic central-Coulomb spectral action; degenerate in m"
    true
    true

record HamiltonianCarrierAuditBoundary : Set where
  constructor hamiltonianCarrierAuditBoundary
  field
    surroundingHamiltoniansExist : Bool
    liBeSCFIsNontrivialPhysicalExecution : Bool
    ammoniaHamiltonianExistsOnSibling : Bool
    materialHamiltonianExistsOnSibling : Bool
    selectedPTripletRestrictedHamiltonianExists : Bool

    surroundingHamiltonianNameImpliesSameCarrier : Bool
    liBeSOnlyBasisPaysPTripletInteraction : Bool
    molecularHamiltonianPaysAtomicPTripletInteraction : Bool
    materialHamiltonianPaysAtomicPTripletInteraction : Bool
    actualInteractingPTripletHamiltonianStillRequired : Bool

open HamiltonianCarrierAuditBoundary public

canonicalHamiltonianCarrierAuditBoundary : HamiltonianCarrierAuditBoundary
canonicalHamiltonianCarrierAuditBoundary =
  hamiltonianCarrierAuditBoundary
    true true true true true
    false false false false true

surroundingHamiltonianNameImpliesSameCarrierIsFalse :
  surroundingHamiltonianNameImpliesSameCarrier canonicalHamiltonianCarrierAuditBoundary
  ≡ false
surroundingHamiltonianNameImpliesSameCarrierIsFalse = refl

actualInteractingPTripletHamiltonianStillRequiredIsTrue :
  actualInteractingPTripletHamiltonianStillRequired canonicalHamiltonianCarrierAuditBoundary
  ≡ true
actualInteractingPTripletHamiltonianStillRequiredIsTrue = refl
