module DASHI.Governance.ConsciousnessExceptionalSelectedTPSProtocolExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Governance.ConsciousnessBrainITExceptionalNeuralFrontierExact as BrainIT

------------------------------------------------------------------------
-- SELECTED-TPS / SUBSYSTEM PROTOCOL FOR EXCEPTIONAL NEURAL TESTS
--
-- Cross-branch donor: PR #1128 QuantumMereologyMaxCutExact.
-- Its theorem shape is:
--
--   supplied selection receipt -> SAME selected TPS -> pair-relation geometry
--
-- with an explicit consumer collision theorem: if the selection criterion
-- identifies two candidate decompositions that a geometry-sensitive consumer
-- distinguishes, the criterion is insufficient and every adequate refinement
-- must separate the witnessed pair.
--
-- Neural consequence: an exceptional/topological feature map must be declared
-- on a fixed selected subsystem decomposition.  Choosing a different latent or
-- decoder coordinate system after seeing the outcome cannot count as a test of
-- the same geometry.
------------------------------------------------------------------------

quantumMereologyDonorPR : String
quantumMereologyDonorPR = "chboishabba/dashi_agda#1128"

record ExceptionalNeuralSelectedTPSProtocol : Set₁ where
  field
    RawNeuralState : Set
    CandidateDecomposition : Set
    SelectionSurface : Set
    ExceptionalFeature : Set
    Outcome : Set

    observeSelection : CandidateDecomposition → SelectionSurface
    selected : CandidateDecomposition
    featureOnSelected : RawNeuralState → ExceptionalFeature
    heldOutOutcome : RawNeuralState → Outcome

    selectionRulePredeclaredReceipt : Set
    selectedSubsystemIdentityReceipt : Set
    scannerAndPreprocessingFixedReceipt : Set
    exceptionalFeaturePredeclaredReceipt : Set
    nuisanceMatchedBaselineReceipt : Set
    heldOutPredictionReceipt : Set
    competingModelReceipt : Set
    geometrySensitiveCollisionAuditReceipt : Set
open ExceptionalNeuralSelectedTPSProtocol public

record SelectedTPSNeuralBoundary : Set where
  constructor selected-tps-neural-boundary
  field
    quantumMereologyDonorPinned : Bool
    sameSelectedSubsystemRequired : Bool
    postHocDecoderCoordinatesCanPayExceptionalGeometry : Bool
    clusterLabelsAloneCanPaySubsystemIdentity : Bool
    geometryCriterionCollisionRequiresRefinement : Bool
    propofolAndBrainITRemainComplementaryDonors : Bool
    rawExceptionalNeuralRealizationPaid : Bool
    consciousnessMechanismPaid : Bool
    boundary : String
open SelectedTPSNeuralBoundary public

canonicalSelectedTPSNeuralBoundary : SelectedTPSNeuralBoundary
canonicalSelectedTPSNeuralBoundary =
  selected-tps-neural-boundary
    true true false false true true false false
    "Future exceptional-neural tests must predeclare the subsystem/TPS selection and compute exceptional/topological features on that same selected decomposition. Brain-IT learned cluster labels are observation coordinates, not by themselves a subsystem identity; propofol supplies a state intervention but not neural exceptional structure. Geometry-sensitive selection collisions require refinement rather than post-hoc coordinate switching."

data PostHocCoordinatesCreateExceptionalGeometry : Set where

postHocCoordinatesDoNotCreateExceptionalGeometry :
  PostHocCoordinatesCreateExceptionalGeometry → {A : Set} → A
postHocCoordinatesDoNotCreateExceptionalGeometry ()
