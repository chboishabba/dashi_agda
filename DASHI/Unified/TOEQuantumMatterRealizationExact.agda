module DASHI.Unified.TOEQuantumMatterRealizationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Unified.TOESectorRealizationExact
import DASHI.Unified.TOE369C3RealizationGraphExact as C3
import DASHI.Unified.CrossScaleMatterPhysics as CrossScale
import DASHI.Unified.TOEConcreteInhabitantsExact as Inhabitants

record QuantumMatterPayment : Set where
  field
    finiteTPSAtlasPaid : Bool
    gTPSStructurePaid : Bool
    selectedSubsystemObserverPaid : Bool
    nh3C3HamiltonianSourcePaid : Bool
    matbgC3HamiltonianSourcePaid : Bool
    exactAtomicP2CoulombC3Inhabited : Bool
    crossScaleMatterCarrierPaid : Bool

    samePhysicalTPSPaid : Bool
    universalToTPSDynamicsPaid : Bool
    atomicContinuumSameObjectWeldPaid : Bool
    nh3HamiltonianIntertwinerPaid : Bool
    matbgHamiltonianIntertwinerPaid : Bool
    thermodynamicLimitPaid : Bool
    empiricalPhaseTransitionPaid : Bool
    sourceReceipt : String

currentQuantumMatterPayment : QuantumMatterPayment
currentQuantumMatterPayment =
  record
    { finiteTPSAtlasPaid = true
    ; gTPSStructurePaid = true
    ; selectedSubsystemObserverPaid = true
    ; nh3C3HamiltonianSourcePaid = true
    ; matbgC3HamiltonianSourcePaid = true
    ; exactAtomicP2CoulombC3Inhabited = true
    ; crossScaleMatterCarrierPaid = true
    ; samePhysicalTPSPaid = false
    ; universalToTPSDynamicsPaid = false
    ; atomicContinuumSameObjectWeldPaid = false
    ; nh3HamiltonianIntertwinerPaid = false
    ; matbgHamiltonianIntertwinerPaid = false
    ; thermodynamicLimitPaid = false
    ; empiricalPhaseTransitionPaid = false
    ; sourceReceipt =
        "Consumes current finite/g-TPS quantum-mereology structure, NH3 and MATBG Hamiltonian lanes, and now an actual finite interacting matter inhabitant: the selected hydrogenic common-spin 2p^2 carrier with V_ee=(21/128) I_3 and exact C3 commutation from Agda PR #1194, recut natively in the TOE branch. The live promotion is not Hamiltonian existence anymore; it is the same-object universal-to-physical TPS/Hamiltonian weld, continuum projection, calibration and experiment."
    }

crossScaleMatterSurface : CrossScale.CrossScaleMatterPhysicsSurface
crossScaleMatterSurface = CrossScale.canonicalCrossScaleMatterPhysicsSurface

quantumMatterGrade : ValidationGrade
quantumMatterGrade = sharedCarrier

quantumMatterObligations : List RealizationObligation
quantumMatterObligations =
  representationActionAgreement
  ∷ dynamicsEquivariance
  ∷ actionHamiltonianAgreement
  ∷ scaleCalibrationAgreement
  ∷ empiricalSameObjectAttachment
  ∷ heldOutPredictionReceipt
  ∷ []

record QuantumMatterRealization : Set where
  field
    matbgOrientationCandidate : C3.C3Edge
    selectedAtomicHamiltonianInhabitant : Inhabitants.AtomicP2HamiltonianInhabitant
    payments : QuantumMatterPayment
    attainedGrade : ValidationGrade
    unpaid : List RealizationObligation
    samePhysicalHamiltonianPromoted : Bool
    samePhysicalHamiltonianPromotedIsFalse : samePhysicalHamiltonianPromoted ≡ false
    reading : String

canonicalQuantumMatterRealization : QuantumMatterRealization
canonicalQuantumMatterRealization =
  record
    { matbgOrientationCandidate = C3.universalToMATBGCandidate
    ; selectedAtomicHamiltonianInhabitant = Inhabitants.canonicalAtomicP2HamiltonianInhabitant
    ; payments = currentQuantumMatterPayment
    ; attainedGrade = quantumMatterGrade
    ; unpaid = quantumMatterObligations
    ; samePhysicalHamiltonianPromoted = false
    ; samePhysicalHamiltonianPromotedIsFalse = refl
    ; reading =
        "HAM candidate: quantum subsystem structure and concrete matter Hamiltonians are sector readouts of one universal state/refinement/orientation object. This is no longer merely existential: the TOE branch contains an actual three-state interacting 2p^2 Coulomb Hamiltonian inhabitant whose C3 commutation is proved by construction. The decisive remaining bridge is to identify the universal physical state/TPS and continuum action with that selected matter carrier, then repeat the weld for NH3/MATBG and test calibrated predictions."
    }
