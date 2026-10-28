module DASHI.Reasoning.LILAForwardOnlyDustAdapterExact where

-- Consumer adapter, not a competing refinement theorem or Dust algorithm.
-- The Dust algorithmic source remains Dahal/Mandal/Gulbahar/Vegesna.
-- Existing LILA geometric reasoning remains owned by #1094/#1095.
-- No claim that the abstract optimiser is implemented on GPUs.

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Core.ObserverRefinementLatticeExact
  using (Observer; Refines; pairObserver; pairRefinesLeft)
import DASHI.Reasoning.DustNoiseAlgorithmExact as Dust

record ForwardOnlyLILAConsumer
    (A : Dust.ScalarOps)
    (State Coarse Semantic Parameter Probe Token Layer : Set) : Set₁ where
  open Dust.ScalarOps A
  field
    originalObserver : Observer State Coarse
    semanticObserver : Observer State Semantic
    -- Literal reuse of the existing refinement owner.
    semanticAugmentationRefines :
      Refines originalObserver (pairObserver originalObserver semanticObserver)
    objective : Parameter → State → S
    pairedSemanticLoss : Parameter → State → State → S
    -- Forward-only means the algorithm may query losses on concrete
    -- parameter values without requiring a reverse derivative.
    propose : Parameter → Probe → Parameter
    lossAtProbe : Parameter → Probe → State → S
    lossAtProbeLaw :
      (p : Parameter) (q : Probe) (x : State) →
      lossAtProbe p q x ≡ objective (propose p q) x
    dustTrace : Dust.ForwardOnlyTrace A Token Layer Probe
    -- Whether the objective was actually measured under a matched
    -- LILA intervention is an empirical receipt, not a theorem.
    objectiveAndProbeCalibrated : Bool
    testedHeldOut : Bool
    sourceAttribution : String

open ForwardOnlyLILAConsumer

canonicalRefinement :
  {A : Dust.ScalarOps}
  {State Coarse Semantic Parameter Probe Token Layer : Set}
  (c : ForwardOnlyLILAConsumer A State Coarse Semantic Parameter Probe Token Layer) →
  Refines (originalObserver c)
    (pairObserver (originalObserver c) (semanticObserver c))
canonicalRefinement c =
  pairRefinesLeft (originalObserver c) (semanticObserver c)

-- This proves only that the adapter evaluates the defined objective
-- at the proposed point. Gradient unbiasedness, decrease, convergence,
-- runtime, and generalisation each require separate certificates.
forwardProbeEvaluatesLILA :
  {A : Dust.ScalarOps}
  {State Coarse Semantic Parameter Probe Token Layer : Set}
  (c : ForwardOnlyLILAConsumer A State Coarse Semantic Parameter Probe Token Layer) →
  (p : Parameter) (q : Probe) (x : State) →
  lossAtProbe c p q x ≡ objective c (propose c p q) x
forwardProbeEvaluatesLILA c p q x = lossAtProbeLaw c p q x
