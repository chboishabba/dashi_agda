module DASHI.Physics.Closure.TSFVActionPhaseWeightSeparationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.ActionPhaseLiftBoundaryExact as PhaseLift
import DASHI.Physics.Foundations.HistoryWeightFiltrationExact as Filtration
import DASHI.Physics.Closure.TSFVLocalActionCandidateAuditExact as V3Action
import DASHI.Physics.Closure.TSFVPairActionCandidateAuditExact as PairAction

------------------------------------------------------------------------
-- Cross-pollination boundary: action candidates, quantum phase, Gibbs weight,
-- and MDL prior remain distinct typed structures even when each ultimately
-- carries numerical data on histories.
------------------------------------------------------------------------

data StructuralQuantityRole : Set where
  actionCandidateRole : StructuralQuantityRole
  quantumPhaseRole : StructuralQuantityRole
  gibbsWeightRole : StructuralQuantityRole
  mdlPriorRole : StructuralQuantityRole

actionAndPhaseRolesDistinct :
  actionCandidateRole ≡ quantumPhaseRole → ⊥
actionAndPhaseRolesDistinct ()

phaseAndGibbsRolesDistinct :
  quantumPhaseRole ≡ gibbsWeightRole → ⊥
phaseAndGibbsRolesDistinct ()

gibbsAndMDLRolesDistinct :
  gibbsWeightRole ≡ mdlPriorRole → ⊥
gibbsAndMDLRolesDistinct ()

record TSFVActionPhaseWeightSeparation : Set₁ where
  field
    actionPhaseBoundary : PhaseLift.ActionPhaseLiftBoundary
    historyWeightBoundary : Filtration.HistoryWeightFiltrationBoundary

    v3ActionAudit : V3Action.TSFVLocalActionCandidateAudit
    pairActionBoundary : PairAction.PairActionCandidateBoundary

    actionToPhaseCalibrationSupplied : Bool
    actionToPhaseCalibrationSuppliedIsFalse :
      actionToPhaseCalibrationSupplied ≡ false

    actionCandidateIsGibbsWeight : Bool
    actionCandidateIsGibbsWeightIsFalse :
      actionCandidateIsGibbsWeight ≡ false

    actionCandidateIsMDLPrior : Bool
    actionCandidateIsMDLPriorIsFalse :
      actionCandidateIsMDLPrior ≡ false

    separationReading : String

open TSFVActionPhaseWeightSeparation public

canonicalTSFVActionPhaseWeightSeparation : TSFVActionPhaseWeightSeparation
canonicalTSFVActionPhaseWeightSeparation =
  record
    { actionPhaseBoundary = PhaseLift.canonicalActionPhaseLiftBoundary
    ; historyWeightBoundary = Filtration.canonicalHistoryWeightFiltrationBoundary
    ; v3ActionAudit = V3Action.canonicalTSFVLocalActionCandidateAudit
    ; pairActionBoundary = PairAction.canonicalPairActionCandidateBoundary
    ; actionToPhaseCalibrationSupplied = false
    ; actionToPhaseCalibrationSuppliedIsFalse = refl
    ; actionCandidateIsGibbsWeight = false
    ; actionCandidateIsGibbsWeightIsFalse = refl
    ; actionCandidateIsMDLPrior = false
    ; actionCandidateIsMDLPriorIsFalse = refl
    ; separationReading =
        "TSFV now has audited structural action candidates, but no S/hbar calibration. Existing DASHI history filtration keeps quantum phase, Gibbs weight and MDL prior separately typed, so numerical carriers cannot be identified by analogy alone."
    }
