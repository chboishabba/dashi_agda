module DASHI.Cognition.VisualCompressionAttractors where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Shared geometric / topological visual generator vocabulary
------------------------------------------------------------------------

data VisualGenerator : Set where
  latticeGenerator   : VisualGenerator
  tunnelGenerator    : VisualGenerator
  spiralGenerator    : VisualGenerator
  webGenerator       : VisualGenerator
  checkerGenerator   : VisualGenerator
  orientationGenerator : VisualGenerator

record GeneratorComplexity : Set where
  constructor generatorComplexity
  field
    symmetryCodeLength : Nat
    deformationCodeLength : Nat
    semanticBindingCost : Nat

record VisualFieldState : Set where
  constructor visualFieldState
  field
    highLevelConstraintStrength : Nat
    localGain                   : Nat
    orientationCoupling         : Nat
    stackBindingDepth           : Nat

record CompressionAttractor : Set where
  constructor compressionAttractor
  field
    generator        : VisualGenerator
    complexity       : GeneratorComplexity
    stableUnderLocalFieldDynamics : Bool
    sharedAcrossObserversCandidate : Bool

------------------------------------------------------------------------
-- Functional interpretation
------------------------------------------------------------------------

record VisualCompressionMechanism : Set where
  constructor visualCompressionMechanism
  field
    highLevelConstraintsRelaxed : Bool
    localSymmetryModesRemain    : Bool
    lowCodeGeneratorsSelected   : Bool
    semanticContentRequired     : Bool

canonicalPsychedelicCompressionMechanism : VisualCompressionMechanism
canonicalPsychedelicCompressionMechanism =
  visualCompressionMechanism true true true false

geometricGeneratorDoesNotRequireSemanticContent :
  VisualCompressionMechanism.semanticContentRequired
    canonicalPsychedelicCompressionMechanism ≡ false
geometricGeneratorDoesNotRequireSemanticContent = refl

------------------------------------------------------------------------
-- Representative low-description-length attractors
------------------------------------------------------------------------

canonicalLatticeAttractor : CompressionAttractor
canonicalLatticeAttractor =
  compressionAttractor
    latticeGenerator
    (generatorComplexity 1 1 0)
    true
    true

canonicalSpiralAttractor : CompressionAttractor
canonicalSpiralAttractor =
  compressionAttractor
    spiralGenerator
    (generatorComplexity 1 2 0)
    true
    true

canonicalTunnelAttractor : CompressionAttractor
canonicalTunnelAttractor =
  compressionAttractor
    tunnelGenerator
    (generatorComplexity 2 2 0)
    true
    true

------------------------------------------------------------------------
-- Topological/categorical reading
------------------------------------------------------------------------

record GeneratorMorphism : Set where
  constructor generatorMorphism
  field
    sourceGenerator : VisualGenerator
    targetGenerator : VisualGenerator
    deformationTag  : String

identityGeneratorMorphism : VisualGenerator → GeneratorMorphism
identityGeneratorMorphism generator =
  generatorMorphism generator generator "identity"

record VisualGeneratorCategoryBoundary : Set where
  constructor visualGeneratorCategoryBoundary
  field
    objectsAreGeneratorClasses   : Bool
    morphismsAreDeformations     : Bool
    compositionCandidateOnly     : Bool
    neurobiologicalCauseProven   : Bool
    psychedelicUniversalityProven : Bool

canonicalVisualGeneratorCategoryBoundary : VisualGeneratorCategoryBoundary
canonicalVisualGeneratorCategoryBoundary =
  visualGeneratorCategoryBoundary true true true false false

neurobiologicalCauseNotPromoted :
  VisualGeneratorCategoryBoundary.neurobiologicalCauseProven
    canonicalVisualGeneratorCategoryBoundary ≡ false
neurobiologicalCauseNotPromoted = refl

psychedelicUniversalityNotPromoted :
  VisualGeneratorCategoryBoundary.psychedelicUniversalityProven
    canonicalVisualGeneratorCategoryBoundary ≡ false
psychedelicUniversalityNotPromoted = refl
