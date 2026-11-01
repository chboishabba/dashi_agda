module DASHI.Physics.Closure.ClaySprintFortyFourResidueSemanticsAuditReceipt where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintFortyThreeNS3DTruthBridgeRepairReceipt
  as Repair

------------------------------------------------------------------------
-- Sprint 44 residue semantics audit.
--
-- This is the falsification-frontier receipt requested after the repaired 3D
-- truth lane.  It records candidate Rplus definitions, adjusted bridge
-- constants, pass/fail surfaces, and governance.  It intentionally does not
-- inhabit any Clay promotion.

Shell : Set
Shell = Nat

Time : Set
Time = Nat

Scalar : Set
Scalar = String

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

record ClaySprintFortyFourResidueSemanticsAuditReceipt : Set₁ where
  field
    -- candidate residues
    RplusStrict :
      Shell → Time → Scalar

    RplusStrain :
      Shell → Time → Scalar

    RplusStretchSign :
      Shell → Time → Scalar

    RplusPressureRelaxed :
      Shell → Time → Scalar

    RplusNoPressure :
      Shell → Time → Scalar

    -- bridge constants
    adjustedBridgeStrict :
      Shell → Time → Scalar

    adjustedBridgeStrain :
      Shell → Time → Scalar

    adjustedBridgeStretchSign :
      Shell → Time → Scalar

    adjustedBridgePressureRelaxed :
      Shell → Time → Scalar

    adjustedBridgeNoPressure :
      Shell → Time → Scalar

    -- pass/fail surfaces
    strictBridgeBounded :
      Set

    strainBridgeBounded :
      Set

    stretchSignBridgeBounded :
      Set

    pressureRelaxedBridgeBounded :
      Set

    noPressureBridgeBounded :
      Set

    -- interpretation
    strictFailsButStrainPasses :
      Set

    allResiduesFail :
      Set

    pressureDowngradeTooAggressive :
      Set

    -- governance
    noClayPromotionFromDiagnostics :
      clayNavierStokesPromoted ≡ false

data ResidueAuditCandidate : Set where
  RplusStrictCandidate :
    ResidueAuditCandidate
  RplusStrainCandidate :
    ResidueAuditCandidate
  RplusStretchSignCandidate :
    ResidueAuditCandidate
  RplusPressureRelaxedCandidate :
    ResidueAuditCandidate
  RplusNoPressureCandidate :
    ResidueAuditCandidate

canonicalResidueAuditCandidates :
  List ResidueAuditCandidate
canonicalResidueAuditCandidates =
  RplusStrictCandidate
  ∷ RplusStrainCandidate
  ∷ RplusStretchSignCandidate
  ∷ RplusPressureRelaxedCandidate
  ∷ RplusNoPressureCandidate
  ∷ []

data ResidueAuditOpenGate : Set where
  gateProofAuthoritativeRplus :
    ResidueAuditOpenGate
  gateAdjustedBridgeBoundedAcrossTheta :
    ResidueAuditOpenGate
  gateBudgetBeatsHalf :
    ResidueAuditOpenGate
  gateActualTernaryLineage :
    ResidueAuditOpenGate
  gateStretchAbsorption :
    ResidueAuditOpenGate
  gateNoFiniteTimeBlowup :
    ResidueAuditOpenGate

canonicalResidueAuditOpenGates :
  List ResidueAuditOpenGate
canonicalResidueAuditOpenGates =
  gateProofAuthoritativeRplus
  ∷ gateAdjustedBridgeBoundedAcrossTheta
  ∷ gateBudgetBeatsHalf
  ∷ gateActualTernaryLineage
  ∷ gateStretchAbsorption
  ∷ gateNoFiniteTimeBlowup
  ∷ []

data ClaySprintFortyFourResidueAuditPromotion : Set where

residueAuditPromotionImpossibleHere :
  ClaySprintFortyFourResidueAuditPromotion →
  ⊥
residueAuditPromotionImpossibleHere ()

candidateCount : Nat
candidateCount = 5

openGateCount : Nat
openGateCount = 6

wideAuditTableFormula : String
wideAuditTableFormula =
  "ns_residue_semantics_wide.csv emits Q_K, Conc_K, five Rplus definitions, five C definitions, and zeroR_positiveQ flags for theta in 0,0.25,0.5,1"

falsificationFrontierSummary : String
falsificationFrontierSummary =
  "If every proof-defensible Rplus fails the bridge, the DASHI NS bridge route is falsified under tested semantics"

uses3DRepairEvidence :
  Repair.ClaySprintFortyThreeNS3DRepairStatus →
  Bool
uses3DRepairEvidence
  Repair.claySprintFortyThreeNS3DRepairRecorded_noPromotion =
  false

candidateCountCheck : candidateCount ≡ 5
candidateCountCheck = refl

openGateCountCheck : openGateCount ≡ 6
openGateCountCheck = refl
