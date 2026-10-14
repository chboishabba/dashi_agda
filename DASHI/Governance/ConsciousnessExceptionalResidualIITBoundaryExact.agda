module DASHI.Governance.ConsciousnessExceptionalResidualIITBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Governance.ConsciousnessExceptionalSelectedTPSProtocolExact as Selected
import DASHI.Physics.Closure.E6HyperformH3ResidualReopeningMetricExact as Residual

------------------------------------------------------------------------
-- EXCEPTIONAL RESIDUAL / IIT EMPIRICAL BOUNDARY
--
-- Cross-branch design donor: PR #1148 separates graph cuts, stalk/restriction
-- cuts, global-section cuts and IIT-4 phi semantics, and requires biological
-- interpretation to pay the same consumer-relative adequacy obligations as the
-- rest of the brain stack.
--
-- The exceptional H3 lane now has a concrete local information hierarchy:
--
--   27-state H3
--      -> 9-state coarse/radical quotient
--      +  3-valued residual phase coordinate
--      -> exact reopening of all 27 states.
--
-- That gives a falsifiable neural protocol: on one predeclared selected
-- subsystem/TPS and fixed acquisition pipeline, compare a coarse exceptional
-- feature against the joined coarse+residual feature on held-out consumers.
-- The residual may improve prediction or distinguish a collision, but neither
-- improvement nor structural integration is definitionally IIT phi or
-- phenomenal consciousness.
------------------------------------------------------------------------

iitDesignDonorPR : String
iitDesignDonorPR = "chboishabba/dashi_agda#1148"

record ExceptionalResidualNeuralComparison : Set₁ where
  field
    RawNeuralState : Set
    SelectedSubsystem : Set
    CoarseExceptionalFeature : Set
    ResidualExceptionalFeature : Set
    JoinedExceptionalFeature : Set
    ConsumerOutcome : Set

    selectedSubsystem : SelectedSubsystem
    coarseFeature : RawNeuralState → CoarseExceptionalFeature
    residualFeature : RawNeuralState → ResidualExceptionalFeature
    joinedFeature : RawNeuralState → JoinedExceptionalFeature
    consumer : RawNeuralState → ConsumerOutcome

    sameSelectedSubsystemReceipt : Set
    fixedAcquisitionPipelineReceipt : Set
    coarseFactorisationOrNonDescentReceipt : Set
    joinedFactorisationReceipt : Set
    heldOutComparisonReceipt : Set
    nuisanceMatchedBaselineReceipt : Set
    IITPartitionSemanticsReceipt : Set
    competingTheoryReceipt : Set
open ExceptionalResidualNeuralComparison public

record ExceptionalResidualIITBoundary : Set where
  constructor exceptional-residual-iit-boundary
  field
    localExceptionalResidualReopensCoarseObserver : Bool
    sameSelectedSubsystemRequired : Bool
    acquisitionPipelineMustRemainFixed : Bool
    coarseVsJoinedHeldOutComparisonWellTyped : Bool
    consumerDistinguishingCollisionCreatesRefinementDemand : Bool
    exceptionalResidualAutomaticallyEqualsIITPhi : Bool
    nondegenerateExceptionalMetricAutomaticallyEqualsIITComplex : Bool
    predictiveImprovementAutomaticallyImpliesConsciousness : Bool
    IITPhiAutomaticallyDecodesPhenomenalContent : Bool
    actualSameSubjectExceptionalNeuralReceiptPaid : Bool
    interpretation : String
open ExceptionalResidualIITBoundary public

canonicalExceptionalResidualIITBoundary : ExceptionalResidualIITBoundary
canonicalExceptionalResidualIITBoundary =
  exceptional-residual-iit-boundary
    true true true true true
    false false false false false
    "The H3 residual coordinate is an exact local reopening variable for a coarse exceptional observer and therefore supplies a principled feature-refinement hypothesis. A neural/IIT test must keep the selected subsystem, acquisition pipeline and consumer fixed and compare coarse versus joined features on held-out data. No identification with IIT phi, an IIT complex, phenomenal content or consciousness is created by structural nondegeneracy or predictive gain."

selectedTPSBoundary : Selected.SelectedTPSNeuralBoundary
selectedTPSBoundary = Selected.canonicalSelectedTPSNeuralBoundary

residualReceipt : Residual.H3ResidualReopeningLocalReceipt
residualReceipt = Residual.canonicalH3ResidualReopeningLocalReceipt

data ExceptionalResidualCreatesIITPhi : Set where

data HeldOutGainCreatesConsciousnessMechanism : Set where

residualDoesNotCreateIITPhi : ExceptionalResidualCreatesIITPhi → {A : Set} → A
residualDoesNotCreateIITPhi ()

heldOutGainDoesNotCreateConsciousness : HeldOutGainCreatesConsciousnessMechanism → {A : Set} → A
heldOutGainDoesNotCreateConsciousness ()
