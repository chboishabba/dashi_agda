module DASHI.Cognition.PNF.X369HyperformalFabricScopeExact where

-- Full Base369 hyperfabric versus the X369 six-slot consumer chart.
-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- The six-slot representation is a typed projection, NOT the whole fabric.
-- Kernel checking is deferred. No identification of unlike native dynamics.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Cognition.PNF.X369ConcreteSixVectorExact as Six
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future

FullState : Set
FullState = Fabric.TernaryHyperformalPoint

Interaction : Set
Interaction = Fabric.Ternary27Point

Appraisal : Set
Appraisal = Fabric.AppraisalFibrePoint

projectInteraction : FullState → Interaction
projectInteraction = Fabric.projectInteractionVoxel

projectAppraisal : FullState → Appraisal
projectAppraisal = Fabric.projectAppraisalFibre

reopen : Interaction → Appraisal → FullState
reopen = Fabric.rebuildOverInteraction

-- Exact BIDI is interaction + BOTH appraisal voxels, not interaction alone.
fullReopen : (x : FullState) →
  reopen (projectInteraction x) (projectAppraisal x) ≡ x
fullReopen (Fabric.ternaryHyperformalPoint i a b) = refl

interactionReopen : (i : Interaction) (a : Appraisal) →
  projectInteraction (reopen i a) ≡ i
interactionReopen = Fabric.projectionRebuildInteraction

appraisalReopen : (i : Interaction) (a : Appraisal) →
  projectAppraisal (reopen i a) ≡ a
appraisalReopen = Fabric.projectionRebuildFibre

-- The signed six-coordinate carrier is deliberately external. No natural
-- six-slot chart or zero-appraisal embedding is inferred from 3^9 counts.
module SixConsumer {Value Input Output : Set}
  (flip : Value → Value)
  (flipInvolutive : (v : Value) → flip (flip v) ≡ v)
  (fineStep : Input → FullState → FullState)
  (fineObserve : Input → FullState → Output)
  (chart : FullState → Six.Six Value)
  (semanticStep : Input → Six.Six Value → Six.Six Value)
  (semanticObserve : Input → Six.Six Value → Output)
  (transitionWeld : (u : Input) (x : FullState) →
    chart (fineStep u x) ≡ semanticStep u (chart x))
  (observationWeld : (u : Input) (x : FullState) →
    fineObserve u x ≡ semanticObserve u (chart x)) where

  -- One-step transport and observation MUST be source-owned inputs.
  -- Under precisely those hypotheses, arbitrary future words factor.
  trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans refl q = q

  sym : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
  sym refl = refl

  outputStable : (u : Input) (x y : FullState) →
    chart x ≡ chart y → fineObserve u x ≡ fineObserve u y
  outputStable u x y eq =
    trans (observationWeld u x)
      (trans (Future.cong (semanticObserve u) eq)
        (sym (observationWeld u y)))

  transitionStable : (u : Input) (x y : FullState) →
    chart x ≡ chart y → chart (fineStep u x) ≡ chart (fineStep u y)
  transitionStable u x y eq =
    trans (transitionWeld u x)
      (trans (Future.cong (semanticStep u) eq)
        (sym (transitionWeld u y)))

  fullFabricConsumerDescent : (inputs : List Input) (x y : FullState) →
    chart x ≡ chart y →
    Future.trace fineStep fineObserve inputs x ≡
    Future.trace fineStep fineObserve inputs y
  fullFabricConsumerDescent inputs x y same =
    Future.inputIndexedTraceDescent fineStep fineObserve chart
      outputStable transitionStable inputs x y same

  -- No unconditional claim about learned MoE / native time evolution.

-- The source's other layers are separately typed:
-- GovernedIndexedResidualCubeExact: 6 faces, 12 edges, 8 vertices.
-- IndexedCubeHyperfibreExact: literal reversible paths and 6/9 resolutions.
-- HistoryTimeIndexedConsumerFibreExact: independently varying history,
-- physical time, consumer version and live fibre.
-- SelfIndexingHyperfabricTetrationExact: fixed-base self-indexing tower.
