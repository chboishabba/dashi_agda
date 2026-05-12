module Ontology.Brain.BrainKernelClosureReceipt where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import Ontology.Brain.DrosophilaHemibrainExternalRunReceipt using
  (HemibrainArtifactChecksum; baselineCurveChecksum; baselineStateChecksum;
   baselineDefectNodesChecksum; baselineGeometrySummaryChecksum)

------------------------------------------------------------------------
-- Theorem-thin closure receipt for the selected baseline hemibrain run.
-- The positive claim is deliberately single-scale and external-numeric:
-- the recorded curve reaches defect zero.  This is not a local proof that
-- arbitrary BrainState values close, nor a multiscale persistence theorem.

record BrainKernelClosureReceipt : Set₁ where
  field
    curveArtifact : HemibrainArtifactChecksum
    stateArtifact : HemibrainArtifactChecksum
    defectNodesArtifact : HemibrainArtifactChecksum
    geometrySummaryArtifact : HemibrainArtifactChecksum
    graphNodes : Nat
    graphEdges : Nat
    finalPositiveNodes : Nat
    finalNeutralNodes : Nat
    finalNegativeNodes : Nat
    positiveComponentCount : Nat
    defectTrace : List Nat
    finalDefect : Nat
    singleScaleOnly : Bool
    promotesBrainLane : Bool
    nonClaimBoundary : List String

brainKernelClosureReceipt : BrainKernelClosureReceipt
brainKernelClosureReceipt =
  record
    { curveArtifact = baselineCurveChecksum
    ; stateArtifact = baselineStateChecksum
    ; defectNodesArtifact = baselineDefectNodesChecksum
    ; geometrySummaryArtifact = baselineGeometrySummaryChecksum
    ; graphNodes = 179907
    ; graphEdges = 7084254
    ; finalPositiveNodes = 137901
    ; finalNeutralNodes = 42006
    ; finalNegativeNodes = 0
    ; positiveComponentCount = 8
    ; defectTrace = 633 ∷ 42 ∷ 2 ∷ 0 ∷ []
    ; finalDefect = 0
    ; singleScaleOnly = true
    ; promotesBrainLane = false
    ; nonClaimBoundary =
        "Closure receipt is the selected external numeric curve only"
        ∷ "It records defect zero at the baseline run scale"
        ∷ "It does not prove closure for arbitrary local BrainState carriers"
        ∷ "It does not assert multiscale latent-structure persistence"
        ∷ "It does not promote the Brain lane or physics lane"
        ∷ []
    }

baselineFinalDefectZero :
  BrainKernelClosureReceipt.finalDefect brainKernelClosureReceipt ≡ zero
baselineFinalDefectZero = refl

baselineClosureIsSingleScaleOnly :
  BrainKernelClosureReceipt.singleScaleOnly brainKernelClosureReceipt ≡ true
baselineClosureIsSingleScaleOnly = refl

baselineClosureDoesNotPromote :
  BrainKernelClosureReceipt.promotesBrainLane brainKernelClosureReceipt ≡ false
baselineClosureDoesNotPromote = refl
