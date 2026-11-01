module Ontology.Brain.DrosophilaHemibrainExternalRunReceipt where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Non-promoting external numeric receipt for the sibling dashiBRAIN
-- hemibrain runs.  This module records provenance and checksums only; it
-- does not import the runtime, re-run the Python analysis, or promote the
-- Brain lane to a local closure theorem.

data BrainReceiptKind : Set where
  externalNumeric theoremThin nonPromoting : BrainReceiptKind

data BrainRunScale : Set where
  singleScale coarseGrain : BrainRunScale

record HemibrainArtifactChecksum : Set where
  constructor artifactChecksum
  field
    artifactPath : String
    sha256 : String

baselineCurveChecksum : HemibrainArtifactChecksum
baselineCurveChecksum =
  artifactChecksum
    "outputs/defect_curve_20260120-142843.csv"
    "e24a19f7fb01fe423b669971e3bab45612a74637773df7b5787063601215e9f6"

baselineStateChecksum : HemibrainArtifactChecksum
baselineStateChecksum =
  artifactChecksum
    "outputs/defect_curve_20260120-142843_state.csv"
    "12fb1e74a6e717f1ef339301a66f1aea5a7afbf0c6aa9fa9fc7550af30dd4301"

baselineDefectNodesChecksum : HemibrainArtifactChecksum
baselineDefectNodesChecksum =
  artifactChecksum
    "outputs/defect_curve_20260120-142843_defect_nodes.csv"
    "ceadc69cd41a7107b5ceca5de4d810d739dc7d3e9b3db803e8bc65f490f575bc"

baselineGeometrySummaryChecksum : HemibrainArtifactChecksum
baselineGeometrySummaryChecksum =
  artifactChecksum
    "outputs/sprint3_default_geometry_summary.json"
    "15742e907ba54d63b9a902141d2ac98c808805687311556a2344d883d5b6ab83"

coarseRandomBlocksChecksum : HemibrainArtifactChecksum
coarseRandomBlocksChecksum =
  artifactChecksum
    "outputs/defect_curve_coarse_random_blocks_20260120-150400.csv"
    "0b5bf6f15c810f66335f9a44c34ffaca77566ed945bf41995055640de982d2a9"

coarseDegreeBinnedChecksum : HemibrainArtifactChecksum
coarseDegreeBinnedChecksum =
  artifactChecksum
    "outputs/defect_curve_coarse_degree_binned_20260120-151536.csv"
    "0b5bf6f15c810f66335f9a44c34ffaca77566ed945bf41995055640de982d2a9"

coarseROIChecksum : HemibrainArtifactChecksum
coarseROIChecksum =
  artifactChecksum
    "outputs/defect_roi_20260120-153259.csv"
    "0b5bf6f15c810f66335f9a44c34ffaca77566ed945bf41995055640de982d2a9"

coarseRadiusR1Checksum : HemibrainArtifactChecksum
coarseRadiusR1Checksum =
  artifactChecksum
    "outputs/defect_radius_r1_20260120-153948.csv"
    "0b5bf6f15c810f66335f9a44c34ffaca77566ed945bf41995055640de982d2a9"

coarseRadiusR2Checksum : HemibrainArtifactChecksum
coarseRadiusR2Checksum =
  artifactChecksum
    "outputs/defect_radius_r2_20260120-154023.csv"
    "0b5bf6f15c810f66335f9a44c34ffaca77566ed945bf41995055640de982d2a9"

selectedHemibrainChecksums : List HemibrainArtifactChecksum
selectedHemibrainChecksums =
  baselineCurveChecksum
  ∷ baselineStateChecksum
  ∷ baselineDefectNodesChecksum
  ∷ baselineGeometrySummaryChecksum
  ∷ coarseRandomBlocksChecksum
  ∷ coarseDegreeBinnedChecksum
  ∷ coarseROIChecksum
  ∷ coarseRadiusR1Checksum
  ∷ coarseRadiusR2Checksum
  ∷ []

record DrosophilaHemibrainExternalRunReceipt : Set₁ where
  field
    sourceRepo : String
    sourceDocs : List String
    selectedArtifacts : List HemibrainArtifactChecksum
    kind : BrainReceiptKind
    runScale : BrainRunScale
    promotesBrainLane : Bool
    promotesPhysicsLane : Bool
    nonClaimBoundary : List String

drosophilaHemibrainExternalRunReceipt :
  DrosophilaHemibrainExternalRunReceipt
drosophilaHemibrainExternalRunReceipt =
  record
    { sourceRepo = "../dashiBRAIN"
    ; sourceDocs =
        "README.md"
        ∷ "docs/formal_axioms.md"
        ∷ "docs/gauge_choices.md"
        ∷ "docs/sprint-03.md"
        ∷ "docs/sprint-04.md"
        ∷ "CHANGELOG.md"
        ∷ []
    ; selectedArtifacts = selectedHemibrainChecksums
    ; kind = nonPromoting
    ; runScale = singleScale
    ; promotesBrainLane = false
    ; promotesPhysicsLane = false
    ; nonClaimBoundary =
        "External numeric sibling-repo evidence only"
        ∷ "No local dashi_agda Brain closure theorem is claimed"
        ∷ "No biological component interpretation is claimed"
        ∷ "No physics-lane or empirical-adequacy promotion is claimed"
        ∷ "Multiscale persistence remains obstructed by the selected coarse curves"
        ∷ []
    }

externalReceiptDoesNotPromoteBrain :
  DrosophilaHemibrainExternalRunReceipt.promotesBrainLane
    drosophilaHemibrainExternalRunReceipt
  ≡
  false
externalReceiptDoesNotPromoteBrain = refl

externalReceiptDoesNotPromotePhysics :
  DrosophilaHemibrainExternalRunReceipt.promotesPhysicsLane
    drosophilaHemibrainExternalRunReceipt
  ≡
  false
externalReceiptDoesNotPromotePhysics = refl
