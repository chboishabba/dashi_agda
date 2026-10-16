module DASHI.Unified.TOEQuantumMatterRealizationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Unified.TOESectorRealizationExact
import DASHI.Unified.TOE369C3RealizationGraphExact as C3
import DASHI.Unified.CrossScaleMatterPhysics as CrossScale

record QuantumMatterPayment : Set where
  field
    finiteTPSAtlasPaid : Bool
    gTPSStructurePaid : Bool
    selectedSubsystemObserverPaid : Bool
    nh3C3HamiltonianSourcePaid : Bool
    matbgC3HamiltonianSourcePaid : Bool
    crossScaleMatterCarrierPaid : Bool

    samePhysicalTPSPaid : Bool
    universalToTPSDynamicsPaid : Bool
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
    ; crossScaleMatterCarrierPaid = true
    ; samePhysicalTPSPaid = false
    ; universalToTPSDynamicsPaid = false
    ; nh3HamiltonianIntertwinerPaid = false
    ; matbgHamiltonianIntertwinerPaid = false
    ; thermodynamicLimitPaid = false
    ; empiricalPhaseTransitionPaid = false
    ; sourceReceipt =
        "Consumes current finite/g-TPS quantum-mereology structure, NH3 source-backed Hamiltonian/state C3 lane, MATBG three-harmonic C3 Hamiltonian lane and the existing cross-scale matter carrier. The live TOE payment is same-object physical TPS/Hamiltonian attachment plus dynamics and experimental continuation."
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
    ; payments = currentQuantumMatterPayment
    ; attainedGrade = quantumMatterGrade
    ; unpaid = quantumMatterObligations
    ; samePhysicalHamiltonianPromoted = false
    ; samePhysicalHamiltonianPromotedIsFalse = refl
    ; reading =
        "HAM candidate: quantum subsystem structure and concrete NH3/MATBG matter Hamiltonians are sector readouts of one universal state/refinement/orientation object. Existing TPS and source-backed C3/Hamiltonian structure keeps the hypothesis live; the decisive promotion is a same-object subsystem algebra plus Hamiltonian/dynamics intertwiner and physical calibration, not another shared C3 label."
    }
