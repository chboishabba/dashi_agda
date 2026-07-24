module DASHI.Cognition.PNF.PNFIRExecutionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using ([]; _∷_)

import DASHI.Cognition.PNF.CandidateInvalidation as Invalidation
import DASHI.Cognition.PNF.OperationalIR as IR
import DASHI.Cognition.PNF.OperationalIRExecution as Execution
import DASHI.Cognition.PNF.FibreLearningDynamics as FibreLearning
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.PNFIRLearningRegression as Fixture
import DASHI.Geometry.QuinticThreefoldCandidate as Quintic

invalidJurisdictionReceipt : Invalidation.PNFInvalidationReceipt
invalidJurisdictionReceipt =
  Invalidation.invalidateCandidate
    Fixture.candidate
    (Invalidation.wrongJurisdiction ∷ [])
    "candidate jurisdiction does not match the operational frame"

invalidatedCandidateState :
  Invalidation.invalidatedCandidate invalidJurisdictionReceipt
    ≡ Invalidation.invalidatedCandidate invalidJurisdictionReceipt
invalidatedCandidateState = refl

tenantPermissionRule : Execution.IRRule
tenantPermissionRule =
  Execution.irRule
    "tenant-permission-rule"
    (λ input → IR.validationState input ≡ IR.operationallyValid)
    (λ _ → "tenant may arrange repair when the stated condition is satisfied")

executionReceipt : IR.IRExecutionReceipt
executionReceipt =
  Execution.executeOperationalIR
    tenantPermissionRule
    Fixture.legalIR
    refl
    refl
    "execution-receipt-1"

executionOutcomeIsExecuted :
  IR.outcome executionReceipt ≡ IR.executed
executionOutcomeIsExecuted = refl

oldTransition : Learning.WeightedTransition
oldTransition =
  Learning.weightedTransition "observe" "avoid" 1 "old-transition"

newTransition : Learning.WeightedTransition
newTransition =
  Learning.weightedTransition "observe" "avoid" 2 "reinforced-transition"

withinFibreUpdate : FibreLearning.FibreLearningUpdate
withinFibreUpdate =
  FibreLearning.reweightWithinFibre
    Fixture.memory
    "public-observe"
    (oldTransition ∷ [])
    (newTransition ∷ [])

withinFibrePublicCategoryStable :
  FibreLearning.publicLabelAfter withinFibreUpdate
    ≡ FibreLearning.publicLabelBefore withinFibreUpdate
withinFibrePublicCategoryStable = refl

withinFibreRememberedPNFStable :
  FibreLearning.rememberedPNFPreserved withinFibreUpdate
    ≡ FibreLearning.rememberedPNFPreserved withinFibreUpdate
withinFibreRememberedPNFStable = refl

selectedQuinticHasComplexDimensionThree :
  Quintic.hypersurfaceComplexDimension Quintic.quinticThreefoldCandidate ≡ 3
selectedQuinticHasComplexDimensionThree = refl
