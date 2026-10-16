module DASHI.Physics.Chemistry.AtomicPeriodicTable369HamiltonianC3IntertwinerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as G
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as C3
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ExteriorC3RepresentationExact as Exterior

------------------------------------------------------------------------
-- 1. Same-carrier spectral Hamiltonian interface.
--
-- We do not encode a Hamiltonian as an identity map.  A basis state is sent to
-- an explicit eigenvalue label together with its output basis state.  This is
-- sufficient to state exact commutation on a selected eigenbasis while keeping
-- amplitudes/scalars abstract.
------------------------------------------------------------------------

record SpectralHamiltonianAction (State : Set) : Set₁ where
  field
    Energy : Set
    apply : State -> Energy × State

open SpectralHamiltonianAction public

record C3SpectralHamiltonianIntertwiner
  {State : Set}
  (H : SpectralHamiltonianAction State)
  (step : State -> State)
  : Set where
  field
    commutes :
      (x : State) ->
      apply H (step x)
      ≡
      let result = apply H x
      in (proj₁ result , step (proj₂ result))

------------------------------------------------------------------------
-- 2. Concrete hydrogenic n=2,l=1 restricted shell.
--
-- The conventional central Coulomb Hamiltonian is degenerate in m for fixed
-- n,l.  The analytic hydrogenic execution in the parent tranche is sourced to
-- NIST DLMF for this role.  We encode only that restricted spectral fact here:
-- one n=2,p energy label on all three magnetic states.
------------------------------------------------------------------------

data HydrogenicPTripletEnergy : Set where
  n2pHydrogenicEnergy : HydrogenicPTripletEnergy

hydrogenicPTripletHamiltonian : SpectralHamiltonianAction C3.MagneticState
hydrogenicPTripletHamiltonian =
  record
    { Energy = HydrogenicPTripletEnergy
    ; apply = λ m -> (n2pHydrogenicEnergy , m)
    }

hydrogenicPTripletChargeIntertwiner :
  C3SpectralHamiltonianIntertwiner
    hydrogenicPTripletHamiltonian
    C3.chargePositiveStep
hydrogenicPTripletChargeIntertwiner =
  record
    { commutes = λ
        { C3.mNegOne -> refl
        ; C3.mZero -> refl
        ; C3.mPosOne -> refl
        }
    }

------------------------------------------------------------------------
-- 3. Exterior-basis noninteracting shell lifts.
--
-- These are exact spectral lifts of the same degenerate one-particle shell.
-- They are NOT the electron-electron Coulomb Hamiltonian.
------------------------------------------------------------------------

data Wedge2ShellEnergy : Set where
  twoN2pShellEnergy : Wedge2ShellEnergy

data Wedge3ShellEnergy : Set where
  threeN2pShellEnergy : Wedge3ShellEnergy

wedge2ShellHamiltonian : SpectralHamiltonianAction Exterior.SignedWedge2
wedge2ShellHamiltonian =
  record
    { Energy = Wedge2ShellEnergy
    ; apply = λ x -> (twoN2pShellEnergy , x)
    }

wedge2ShellChargeIntertwiner :
  C3SpectralHamiltonianIntertwiner
    wedge2ShellHamiltonian
    Exterior.wedge2PositiveStep
wedge2ShellChargeIntertwiner =
  record
    { commutes = λ
        { (Exterior.signedWedge2 Exterior.positiveWedge Exterior.wedgeNegZero) -> refl
        ; (Exterior.signedWedge2 Exterior.negativeWedge Exterior.wedgeNegZero) -> refl
        ; (Exterior.signedWedge2 Exterior.positiveWedge Exterior.wedgeNegPos) -> refl
        ; (Exterior.signedWedge2 Exterior.negativeWedge Exterior.wedgeNegPos) -> refl
        ; (Exterior.signedWedge2 Exterior.positiveWedge Exterior.wedgeZeroPos) -> refl
        ; (Exterior.signedWedge2 Exterior.negativeWedge Exterior.wedgeZeroPos) -> refl
        }
    }

wedge3ShellHamiltonian : SpectralHamiltonianAction Exterior.Wedge3Basis
wedge3ShellHamiltonian =
  record
    { Energy = Wedge3ShellEnergy
    ; apply = λ x -> (threeN2pShellEnergy , x)
    }

wedge3ShellChargeIntertwiner :
  C3SpectralHamiltonianIntertwiner
    wedge3ShellHamiltonian
    Exterior.wedge3PositiveStep
wedge3ShellChargeIntertwiner =
  record
    { commutes = λ { Exterior.wedgeNegZeroPos -> refl } }

------------------------------------------------------------------------
-- 4. Existing atomic generator already owns the interacting-energy consumer.
--
-- The surrounding atomic formalism does not lack an interacting-Hamiltonian
-- *slot*: `AtomicGenerator.interactingEnergy` is already the canonical
-- same-object energy consumer.  What was missing was the symmetry attachment.
-- This record states the exact remaining theorem without replacing that owner.
------------------------------------------------------------------------

record AtomicGeneratorC3InteractingEnergyAttachment
  (A : G.AtomicIndex)
  (Gen : G.AtomicGenerator)
  : Set₁ where
  open G.AtomicGenerator Gen
  field
    manyBodyC3Action : ManyElectronState -> ManyElectronState
    actionOrderThree :
      (psi : ManyElectronState) ->
      manyBodyC3Action (manyBodyC3Action (manyBodyC3Action psi)) ≡ psi
    interactingEnergyInvariant :
      (psi : ManyElectronState) ->
      interactingEnergy A (manyBodyC3Action psi)
      ≡ interactingEnergy A psi

------------------------------------------------------------------------
-- 5. Attribution and promotion boundary.
------------------------------------------------------------------------

record HamiltonianC3Boundary : Set where
  constructor hamiltonianC3Boundary
  field
    hydrogenicPTripletRestrictedSpectralActionPaid : Bool
    hydrogenicPTripletChargeCommutationPaid : Bool
    wedge2NoninteractingShellCommutationPaid : Bool
    wedge3ClosedShellCommutationPaid : Bool
    existingAtomicInteractingEnergyConsumerReused : Bool

    electronElectronCoulombInteractionPaidOnPTriplet : Bool
    liBeSCFIdentifiedWithPTripletCarrier : Bool
    ammoniaHamiltonianImportedAsAtomicPTripletHamiltonian : Bool
    materialHamiltonianImportedAsAtomicPTripletHamiltonian : Bool
    actualAtomicGeneratorInteractingAttachmentInhabited : Bool
    fullAtom369IdentityPaid : Bool

open HamiltonianC3Boundary public

canonicalHamiltonianC3Boundary : HamiltonianC3Boundary
canonicalHamiltonianC3Boundary =
  hamiltonianC3Boundary
    true true true true true
    false false false false false false

liBeSCFIdentifiedWithPTripletCarrierIsFalse :
  liBeSCFIdentifiedWithPTripletCarrier canonicalHamiltonianC3Boundary ≡ false
liBeSCFIdentifiedWithPTripletCarrierIsFalse = refl

actualInteractingAttachmentStillOpen :
  actualAtomicGeneratorInteractingAttachmentInhabited canonicalHamiltonianC3Boundary
  ≡ false
actualInteractingAttachmentStillOpen = refl
