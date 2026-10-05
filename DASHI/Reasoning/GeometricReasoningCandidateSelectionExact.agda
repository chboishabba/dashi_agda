module DASHI.Reasoning.GeometricReasoningCandidateSelectionExact where

------------------------------------------------------------------------
-- GEOMETRIC REASONING CANDIDATE / MODEL-SELECTION SURFACE
--
-- DASHI CONTRIBUTION
--
-- This owner deliberately treats E8, Monster 3A/3B/3C, and an unstructured
-- baseline as competing candidate geometries.  A successful fit is evidence
-- for that declared experiment only; it does not identify a physical or
-- mathematical mechanism without an explicit recognition/realisation witness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 1. Candidate family.
------------------------------------------------------------------------

data GeometricReasoningCandidate : Set where
  unstructuredBaseline : GeometricReasoningCandidate
  lilaE8RootPrior : GeometricReasoningCandidate
  monster3ALocalGeometry : GeometricReasoningCandidate
  monster3BHeisenbergGeometry : GeometricReasoningCandidate
  monster3CLocalGeometry : GeometricReasoningCandidate
  genericFiniteActionGeometry : GeometricReasoningCandidate

candidateName : GeometricReasoningCandidate → String
candidateName unstructuredBaseline = "unstructured-baseline"
candidateName lilaE8RootPrior = "lila-e8-root-prior"
candidateName monster3ALocalGeometry = "monster-3a-local"
candidateName monster3BHeisenbergGeometry = "monster-3b-heisenberg"
candidateName monster3CLocalGeometry = "monster-3c-local"
candidateName genericFiniteActionGeometry = "generic-finite-action"

------------------------------------------------------------------------
-- 2. Generic action candidate.
------------------------------------------------------------------------

record ActionCandidate (G Z : Set) : Set₁ where
  constructor action-candidate
  field
    identity : G
    compose : G → G → G
    act : G → Z → Z
    identityLaw : (z : Z) → act identity z ≡ z
    compositionLaw :
      (g h : G) →
      (z : Z) →
      act (compose g h) z ≡ act g (act h z)
    constructionJustification : String

open ActionCandidate public

record InterventionActionFit
    {I G X Z : Set}
    (candidate : ActionCandidate G Z)
    (encode : X → Z)
    (intervene : I → X → X) : Set₁ where
  constructor intervention-action-fit
  field
    labelAction : I → G
    fits :
      (i : I) →
      (x : X) →
      encode (intervene i x)
      ≡ act candidate (labelAction i) (encode x)
    fitJustification : String

open InterventionActionFit public

------------------------------------------------------------------------
-- 3. Composition is an independent diagnostic.
------------------------------------------------------------------------

record InterventionCompositionFit
    {I G X Z : Set}
    (candidate : ActionCandidate G Z)
    (fit : InterventionActionFit candidate (λ x → x) (λ _ x → x)) : Set₁ where
  constructor intervention-composition-fit
  field
    composeIntervention : I → I → I
    labelComposition :
      (i j : I) →
      labelAction fit (composeIntervention i j)
      ≡ compose candidate (labelAction fit i) (labelAction fit j)

-- The specialized record above is intentionally not the main public fitting
-- API; it exists only to make the composition criterion independently typed.
-- Concrete experiment owners normally carry their own encoder/intervention.

record CompositionReceipt (I G : Set) : Set₁ where
  constructor composition-receipt
  field
    composeIntervention : I → I → I
    composeAction : G → G → G
    fittedAction : I → G
    compositionAgrees :
      (i j : I) →
      fittedAction (composeIntervention i j)
      ≡ composeAction (fittedAction i) (fittedAction j)
    provenance : String

open CompositionReceipt public

------------------------------------------------------------------------
-- 4. Nuisance invariance and layer trace schema.
------------------------------------------------------------------------

record NuisanceInvarianceReceipt (N X Z : Set) : Set₁ where
  constructor nuisance-invariance-receipt
  field
    encode : X → Z
    nuisance : N → X → X
    invariant :
      (n : N) →
      (x : X) →
      encode (nuisance n x) ≡ encode x
    provenance : String

record GeometricReasoningLayerTrace : Set₁ where
  constructor geometric-reasoning-layer-trace
  field
    LayerId : Set
    InterventionId : Set
    CandidateId : Set
    MetricValue : Set

    layer : LayerId
    intervention : InterventionId
    candidate : CandidateId

    pairAccuracy : MetricValue
    displacementAlignment : MetricValue
    rootEntropyOrOccupancy : MetricValue
    quantizationError : MetricValue
    actionFitError : MetricValue
    compositionDefect : MetricValue
    cocycleDefect : MetricValue
    nuisanceResponse : MetricValue
    dashiDeltaAdmissibility : Bool
    traceProvenance : String

------------------------------------------------------------------------
-- 5. Proposed action-compression quality metric surface.
--
-- This is explicitly a DASHI proposal, not a Sophontic definition and not a
-- source claim.  A concrete numerical owner may instantiate the score algebra.
------------------------------------------------------------------------

record ActionCompressionQualityDefinition : Set₁ where
  constructor action-compression-quality-definition
  field
    Score : Set
    semanticInformation : Score
    compositionFidelity : Score
    actionComplexity : Score
    residualComplexity : Score
    combine : Score → Score → Score
    penalize : Score → Score → Score
    quality : Score
    qualityDefinition :
      quality ≡
      penalize
        (combine semanticInformation compositionFidelity)
        (combine actionComplexity residualComplexity)
    proposedByDASHINotAttributedToExternalSource : Bool
    proposalFlagIsTrue :
      proposedByDASHINotAttributedToExternalSource ≡ true

open ActionCompressionQualityDefinition public

------------------------------------------------------------------------
-- 6. Model-selection receipts keep candidate comparison separate from truth.
------------------------------------------------------------------------

record CandidateEvaluationReceipt : Set₁ where
  constructor candidate-evaluation-receipt
  field
    candidate : GeometricReasoningCandidate
    Evaluation : Set
    fitScore : Evaluation
    compositionScore : Evaluation
    nuisanceScore : Evaluation
    residualCost : Evaluation
    datasetOrPairSet : String
    evaluationProtocol : String

record CandidateComparisonReceipt : Set₁ where
  constructor candidate-comparison-receipt
  field
    left right : CandidateEvaluationReceipt
    Comparison : Set
    compare : CandidateEvaluationReceipt → CandidateEvaluationReceipt → Comparison
    result : Comparison
    heldOut : Bool
    provenance : String

------------------------------------------------------------------------
-- 7. Fail-closed boundaries.
------------------------------------------------------------------------

data FitSelectsMechanismPermission : Set where
data LowestResidualImpliesTrueOntologyPermission : Set where
data TernaryCarrierImpliesMonsterClassPermission : Set where

fitCannotAutoSelectMechanism : FitSelectsMechanismPermission → ⊥
fitCannotAutoSelectMechanism ()

residualCannotAutoCreateOntology :
  LowestResidualImpliesTrueOntologyPermission → ⊥
residualCannotAutoCreateOntology ()

ternaryCannotAutoSelectMonsterClass :
  TernaryCarrierImpliesMonsterClassPermission → ⊥
ternaryCannotAutoSelectMonsterClass ()

successfulFitAutomaticallySelectsMechanism : Bool
successfulFitAutomaticallySelectsMechanism = false

record GeometricReasoningCandidateSelectionBoundary : Set where
  constructor geometric-reasoning-candidate-selection-boundary
  field
    baselineCandidateTyped : Bool
    e8CandidateTyped : Bool
    monster3A3B3CDistinct : Bool
    genericActionLawTyped : Bool
    compositionDiagnosticTyped : Bool
    nuisanceInvarianceTyped : Bool
    layerTraceTyped : Bool
    actionCompressionQualityMarkedAsDASHIProposal : Bool
    successfulFitCreatesMechanism : Bool
    lowResidualCreatesOntology : Bool

canonicalGeometricReasoningCandidateSelectionBoundary :
  GeometricReasoningCandidateSelectionBoundary
canonicalGeometricReasoningCandidateSelectionBoundary =
  geometric-reasoning-candidate-selection-boundary
    true true true true true true true true false false
