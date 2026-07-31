module DASHI.Physics.YangMills.BalabanClayGate4PrimaryBibliographyChainExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary bibliography normalization.
--
-- The metadata below follows Bałaban's own bibliography chain as reproduced in
-- the four-dimensional RG paper, with DOI metadata normalized against the
-- corresponding Communications in Mathematical Physics records.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
------------------------------------------------------------------------

Not : Set → Set
Not proposition = proposition → ⊥

data BalabanPrimaryPaperId : Set where
  propagatorsI : BalabanPrimaryPaperId
  propagatorsII : BalabanPrimaryPaperId
  averagingOperations : BalabanPrimaryPaperId
  backgroundFieldPropagators : BalabanPrimaryPaperId
  regularGaugeConfigurations : BalabanPrimaryPaperId
  ultravioletStabilityThreeDimensions : BalabanPrimaryPaperId
  variationalProblemBackgroundFields : BalabanPrimaryPaperId
  fourDimensionalRGPartI : BalabanPrimaryPaperId

record PrimaryPaper : Set where
  constructor primaryPaper
  field
    paperId : BalabanPrimaryPaperId
    title author journal doi : String
    volume firstPage lastPage year : Nat

open PrimaryPaper public

propagatorsIPaper : PrimaryPaper
propagatorsIPaper = primaryPaper
  propagatorsI
  "Propagators and Renormalization Transformations for Lattice Gauge Theories. I"
  "Tadeusz Balaban"
  "Communications in Mathematical Physics"
  "10.1007/BF01215753"
  95 17 40 1984

propagatorsIIPaper : PrimaryPaper
propagatorsIIPaper = primaryPaper
  propagatorsII
  "Propagators and Renormalization Transformations for Lattice Gauge Theories. II"
  "Tadeusz Balaban"
  "Communications in Mathematical Physics"
  "10.1007/BF01240221"
  96 223 250 1984

averagingOperationsPaper : PrimaryPaper
averagingOperationsPaper = primaryPaper
  averagingOperations
  "Averaging Operations for Lattice Gauge Theories"
  "Tadeusz Balaban"
  "Communications in Mathematical Physics"
  "10.1007/BF01211042"
  98 17 51 1985

backgroundFieldPropagatorsPaper : PrimaryPaper
backgroundFieldPropagatorsPaper = primaryPaper
  backgroundFieldPropagators
  "Propagators for Lattice Gauge Theories in a Background Field"
  "Tadeusz Balaban"
  "Communications in Mathematical Physics"
  "10.1007/BF01240355"
  99 389 434 1985

regularGaugeConfigurationsPaper : PrimaryPaper
regularGaugeConfigurationsPaper = primaryPaper
  regularGaugeConfigurations
  "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing Conditions"
  "Tadeusz Balaban"
  "Communications in Mathematical Physics"
  "10.1007/BF01466594"
  99 75 102 1985

ultravioletStabilityThreeDimensionsPaper : PrimaryPaper
ultravioletStabilityThreeDimensionsPaper = primaryPaper
  ultravioletStabilityThreeDimensions
  "Ultraviolet Stability of Three-Dimensional Lattice Pure Gauge Field Theories"
  "Tadeusz Balaban"
  "Communications in Mathematical Physics"
  "10.1007/BF01229380"
  102 255 275 1985

variationalProblemBackgroundFieldsPaper : PrimaryPaper
variationalProblemBackgroundFieldsPaper = primaryPaper
  variationalProblemBackgroundFields
  "The Variational Problem and Background Fields in Renormalization Group Method for Lattice Gauge Theories"
  "Tadeusz Balaban"
  "Communications in Mathematical Physics"
  "10.1007/BF01229381"
  102 277 309 1985

fourDimensionalRGPartIPaper : PrimaryPaper
fourDimensionalRGPartIPaper = primaryPaper
  fourDimensionalRGPartI
  "Renormalization Group Approach to Lattice Gauge Field Theories. I. Generation of Effective Actions in a Small Field Approximation and a Coupling Constant Renormalization in Four Dimensions"
  "Tadeusz Balaban"
  "Communications in Mathematical Physics"
  "10.1007/BF01215223"
  109 249 301 1987

normalizedPrimaryChain : List PrimaryPaper
normalizedPrimaryChain =
  propagatorsIPaper ∷
  propagatorsIIPaper ∷
  averagingOperationsPaper ∷
  backgroundFieldPropagatorsPaper ∷
  regularGaugeConfigurationsPaper ∷
  ultravioletStabilityThreeDimensionsPaper ∷
  variationalProblemBackgroundFieldsPaper ∷
  fourDimensionalRGPartIPaper ∷ []

cmp102ThreeDimensionalPaperNotVariationalPaper :
  Not (ultravioletStabilityThreeDimensions ≡ variationalProblemBackgroundFields)
cmp102ThreeDimensionalPaperNotVariationalPaper ()

cmp102VariationalPaperNotThreeDimensionalPaper :
  Not (variationalProblemBackgroundFields ≡ ultravioletStabilityThreeDimensions)
cmp102VariationalPaperNotThreeDimensionalPaper ()

primaryBibliographyMetadataLevel : ProofLevel
primaryBibliographyMetadataLevel = standardImported

cmp102AdjacentPaperSeparationLevel : ProofLevel
cmp102AdjacentPaperSeparationLevel = machineChecked

physicalConstantToPrimaryPaperAttributionInputsLevel : ProofLevel
physicalConstantToPrimaryPaperAttributionInputsLevel = conditional
