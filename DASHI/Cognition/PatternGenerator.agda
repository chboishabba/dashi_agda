{-# OPTIONS --safe #-}
module DASHI.Cognition.PatternGenerator where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Functional geometric / topological pattern generation.
--
-- A pattern is produced by a parameterised flow and then compressed into a
-- percept.  Nothing requires literal storage of the final image.

record FunctionalPatternGenerator : Set₁ where
  field
    Parameter : Set
    Topology : Set
    Symmetry : Set
    Field : Set
    Percept : Set

    flow :
      Parameter →
      Topology →
      Symmetry →
      Nat →
      Field →
      Field

    compress :
      Field →
      Percept

open FunctionalPatternGenerator public

generatedPercept :
  (generator : FunctionalPatternGenerator) →
  Parameter generator →
  Topology generator →
  Symmetry generator →
  Nat →
  Field generator →
  Percept generator
generatedPercept generator parameter topology symmetry time seed =
  compress generator
    (flow generator parameter topology symmetry time seed)

------------------------------------------------------------------------
-- Finite exact witness family for recurring visual motifs.

data Gain : Set where
  lowGain highGain : Gain

data VisualTopology : Set where
  planar cylindrical radial : VisualTopology

data VisualSymmetry : Set where
  translational hexagonal rotational tunnelSymmetry : VisualSymmetry

data Motif : Set where
  blankMotif stripeMotif latticeMotif spiralMotif tunnelMotif : Motif

highGainPattern :
  VisualTopology →
  VisualSymmetry →
  Motif
highGainPattern planar translational = stripeMotif
highGainPattern planar hexagonal = latticeMotif
highGainPattern planar rotational = spiralMotif
highGainPattern planar tunnelSymmetry = tunnelMotif
highGainPattern cylindrical translational = stripeMotif
highGainPattern cylindrical hexagonal = latticeMotif
highGainPattern cylindrical rotational = spiralMotif
highGainPattern cylindrical tunnelSymmetry = tunnelMotif
highGainPattern radial translational = stripeMotif
highGainPattern radial hexagonal = latticeMotif
highGainPattern radial rotational = spiralMotif
highGainPattern radial tunnelSymmetry = tunnelMotif

visualFlow :
  Gain →
  VisualTopology →
  VisualSymmetry →
  Nat →
  Motif →
  Motif
visualFlow lowGain topology symmetry time seed =
  seed
visualFlow highGain topology symmetry zero seed =
  seed
visualFlow highGain topology symmetry (suc time) seed =
  highGainPattern topology symmetry

visualPatternGenerator : FunctionalPatternGenerator
visualPatternGenerator =
  record
    { Parameter = Gain
    ; Topology = VisualTopology
    ; Symmetry = VisualSymmetry
    ; Field = Motif
    ; Percept = Motif
    ; flow = visualFlow
    ; compress = λ motif → motif
    }

stripe-generated :
  generatedPercept
    visualPatternGenerator
    highGain
    planar
    translational
    1
    blankMotif
  ≡ stripeMotif
stripe-generated = refl

lattice-generated :
  generatedPercept
    visualPatternGenerator
    highGain
    planar
    hexagonal
    1
    blankMotif
  ≡ latticeMotif
lattice-generated = refl

spiral-generated :
  generatedPercept
    visualPatternGenerator
    highGain
    radial
    rotational
    1
    blankMotif
  ≡ spiralMotif
spiral-generated = refl

tunnel-generated :
  generatedPercept
    visualPatternGenerator
    highGain
    cylindrical
    tunnelSymmetry
    1
    blankMotif
  ≡ tunnelMotif
tunnel-generated = refl

record PatternGeneratorReceipt : Set where
  constructor pattern-generator-receipt
  field
    flowBasedGenerationChecked : Bool
    symmetryAndTopologyExplicit : Bool
    literalImagesStoredAsExplanation : Bool
    literalImagesStoredAsExplanationIsFalse :
      literalImagesStoredAsExplanation ≡ false

patternGeneratorReceipt : PatternGeneratorReceipt
patternGeneratorReceipt =
  pattern-generator-receipt true true false refl
