module DASHI.Unified.TOEQuantumMatterRealizationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Unified.TOESectorRealizationExact
import DASHI.Unified.TOE369C3RealizationGraphExact as C3
import DASHI.Unified.CrossScaleMatterPhysics as CrossScale
import DASHI.Unified.TOEConcreteInhabitantsExact as Inhabitants
import DASHI.Unified.TOEQuantumInhabitantsExact as QuantumInhabitants

record QuantumMatterPayment : Set where
  field
    finiteTPSAtlasPaid : Bool
    gTPSStructurePaid : Bool
    finiteGTPSProjectorInhabited : Bool
    finiteGTPSUnitaryMetricInhabited : Bool
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
    minimizerPullbackPaid : Bool
    thermodynamicLimitPaid : Bool
    empiricalPhaseTransitionPaid : Bool
    sourceReceipt : String

currentQuantumMatterPayment : QuantumMatterPayment
currentQuantumMatterPayment =
  record
    { finiteTPSAtlasPaid = true
    ; gTPSStructurePaid = true
    ; finiteGTPSProjectorInhabited = true
    ; finiteGTPSUnitaryMetricInhabited = true
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
    ; minimizerPullbackPaid = false
    ; thermodynamicLimitPaid = false
    ; empiricalPhaseTransitionPaid = false
    ; sourceReceipt =
        "The finite quantum-mereology mathematics is now concretely inhabited at imported-formal-source scope: Lean PR #76 constructs canonical finite Hilbert-Schmidt projectors for every source g-TPS and reconstructs the finite unitary-family metric element. The matter side is also concretely inhabited natively by the selected hydrogenic common-spin 2p^2 carrier with V_ee=(21/128) I_3 and exact C3 commutation. The live TOE payment is therefore the same-object physical source-gTPS + Hamiltonian attachment, universal dynamics transport, continuum projection, minimizer/Hamiltonian-parameter pullback, calibration and experiment."
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
    finiteGTPSProjectorFormalInhabitant : Inhabitants.FormalInhabitantReceipt
    finiteGTPSMetricFormalInhabitant : Inhabitants.FormalInhabitantReceipt
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
    ; finiteGTPSProjectorFormalInhabitant = QuantumInhabitants.lean76GTPSProjectionInhabitant
    ; finiteGTPSMetricFormalInhabitant = QuantumInhabitants.lean76GTPSMetricInhabitant
    ; payments = currentQuantumMatterPayment
    ; attainedGrade = quantumMatterGrade
    ; unpaid = quantumMatterObligations
    ; samePhysicalHamiltonianPromoted = false
    ; samePhysicalHamiltonianPromotedIsFalse = refl
    ; reading =
        "HAM candidate: quantum subsystem structure and concrete matter Hamiltonians are sector readouts of one universal state/refinement/orientation object. The selected finite mathematics is no longer existential: the TOE carries a concrete interacting 2p^2 Coulomb Hamiltonian inhabitant, plus imported formal inhabitants for canonical finite g-TPS projectors and the source unitary-family metric formula. What remains is the physically decisive same-object weld tying the selected source algebra/TPS and Hamiltonian to the universal state/action, followed by continuum/thermodynamic transport and held-out measurement."
    }
