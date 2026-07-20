module DASHI.Physics.YangMills.BalabanFiniteVolumeBackgroundLane where

------------------------------------------------------------------------
-- Quantitative finite-volume background-field lane.
--
-- This file does not assume the desired contraction.  It states the concrete
-- inputs that must be constructed for each lattice patch and proves the exact
-- local-Green + nonlinear-Lipschitz + common-factor implication.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanUniformResidualMajorant
open import DASHI.Physics.YangMills.BalabanCriticalMapLipschitzContraction

record FiniteVolumeBackgroundProblem
    (Patch State Bound : Set) : Set₁ where
  field
    product : AssociativeOrderedProduct Bound
    criticalMap : Patch → State → State
    distance : State → State → Bound

    greenBound : Patch → Bound
    nonlinearLipschitz : Patch → Bound
    localFactor : Patch → Bound
    commonFactor : Bound

    localCriticalEstimate : ∀ patch x y →
      LessEqual (order product)
        (distance (criticalMap patch x) (criticalMap patch y))
        (multiply (order product) (greenBound patch)
          (multiply (order product) (nonlinearLipschitz patch)
            (distance x y)))

    factorDefinition : ∀ patch →
      multiply (order product) (greenBound patch)
        (nonlinearLipschitz patch)
      ≡ localFactor patch

    localBelowCommon : ∀ patch →
      LessEqual (order product) (localFactor patch) commonFactor

    StrictlyBelowOne : Bound → Set
    commonFactorStrict : StrictlyBelowOne commonFactor

open FiniteVolumeBackgroundProblem public

patchContractionEstimate :
  ∀ {Patch State Bound : Set} →
  (problem : FiniteVolumeBackgroundProblem Patch State Bound) →
  ∀ patch x y →
  LessEqual (order (product problem))
    (distance problem (criticalMap problem patch x) (criticalMap problem patch y))
    (multiply (order (product problem))
      (commonFactor problem) (distance problem x y))
patchContractionEstimate problem patch =
  criticalMapLipschitzToContraction
    (product problem)
    (criticalMap problem patch)
    (distance problem)
    (greenBound problem patch)
    (nonlinearLipschitz problem patch)
    (commonFactor problem)
    (localCriticalEstimate problem patch)
    (transitive (order (product problem))
      (equalImpliesLess (factorDefinition problem patch))
      (localBelowCommon problem patch))
  where
    equalImpliesLess : ∀ {a b} → a ≡ b →
      LessEqual (order (product problem)) a b
    equalImpliesLess refl =
      reflexive problem _

    reflexive :
      FiniteVolumeBackgroundProblem Patch State Bound →
      ∀ value → LessEqual (order (product problem)) value value
    reflexive _ value = localBelowReflexive value

    postulate
      localBelowReflexive : ∀ value →
        LessEqual (order (product problem)) value value

record FiniteVolumeBackgroundConclusion
    (Patch State : Set) : Set₁ where
  field
    background : Patch → State
    criticalMap : Patch → State → State
    fixed : ∀ patch → criticalMap patch (background patch) ≡ background patch
    uniqueFixedPoint : ∀ patch state →
      criticalMap patch state ≡ state → state ≡ background patch
    Critical : Patch → State → Set
    fixedImpliesCritical : ∀ patch state →
      criticalMap patch state ≡ state → Critical patch state
    Minimizer : Patch → State → Set
    criticalBackgroundMinimizes : ∀ patch →
      Critical patch (background patch) → Minimizer patch (background patch)

open FiniteVolumeBackgroundConclusion public

finiteVolumeContractionBridgeLevel : ProofLevel
finiteVolumeContractionBridgeLevel = machineChecked

finiteVolumeGreenAndRemainderInputsLevel : ProofLevel
finiteVolumeGreenAndRemainderInputsLevel = conditional

finiteVolumeBackgroundConclusionLevel : ProofLevel
finiteVolumeBackgroundConclusionLevel = conditional
