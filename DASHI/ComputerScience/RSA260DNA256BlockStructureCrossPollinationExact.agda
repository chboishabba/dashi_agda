module DASHI.ComputerScience.RSA260DNA256BlockStructureCrossPollinationExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import Ontology.DNA.Supervoxel4Adic as DNA
import Ontology.DNA.CriticallySampledDNA4Transform as DNATransform
import DASHI.Physics.Closure.DNAClifford256StructuralCoincidenceReceipt as DNA256Receipt
import DASHI.ComputerScience.RSA260BlockWiedemannGF2PackedOracleExact as RSA

------------------------------------------------------------------------
-- DNA-256 / RSA WIDTH-256 CROSS-POLLINATION
--
-- The useful commonality is structural only:
--   DNA256 = Vec DNA64 4
--   RSA packed GF(2) width-256 carrier = 4 x uint64_t
-- and the DNA lane already has a count-preserving 256-symbol analysis/synthesis
-- discipline.  The alphabets/algebras are different and no biology-to-RSA
-- semantic identification is made.
------------------------------------------------------------------------

record Structural256CrossPollination : Set₁ where
  constructor structural-256-cross-pollination
  field
    dnaNestedCarrier : Set
    dnaFlatCarrier : Set
    dnaWidth : Nat
    dnaOuterBlocks : Nat
    dnaInnerWidth : Nat
    rsaLogicalWidth : Nat
    rsaPhysicalWords : Nat
    rsaWordWidth : Nat
    sameLogicalWidth256 : Bool
    sameFourBySixtyFourBlockShape : Bool
    sameAlphabet : Bool
    sameAlgebra : Bool
    biologyImpliesGF2 : Bool
    structuralAnalogyReusable : Bool
open Structural256CrossPollination public

canonicalStructural256CrossPollination : Structural256CrossPollination
canonicalStructural256CrossPollination = structural-256-cross-pollination
  DNA.DNA256
  DNA.FlatDNA256
  256 4 64
  256 4 64
  true true
  false false false
  true

------------------------------------------------------------------------
-- Reuse the DNA critical-sampling discipline as an engineering pattern:
-- preserve total coordinate count, keep block structure explicit, and require
-- an inverse/reconstruction receipt before calling a representation equivalent.
------------------------------------------------------------------------

record ReconstructionDiscipline : Set where
  constructor reconstruction-discipline
  field
    sourceCoordinateCount : Nat
    transformedCoordinateCount : Nat
    countsPreserved : Bool
    exactLocalReconstructionOwned : Bool
    rsaBlockPartitionPreserves256Coordinates : Bool
    rsaPackedDotAlreadyExecuted : Bool
    rsaSparseMatVecExecuted : Bool
    rsaKrylovExecuted : Bool
open ReconstructionDiscipline public

canonicalReconstructionDiscipline : ReconstructionDiscipline
canonicalReconstructionDiscipline = reconstruction-discipline
  DNATransform.sourceSymbols DNATransform.criticalSamplingReceipt
  DNATransform.coefficientSymbols DNATransform.criticalSamplingReceipt
  true true
  true true
  false false

priorRSAOracle : RSA.PackedGF2ExecutionReceipt
priorRSAOracle = RSA.rsa260PackedGF2Execution

priorDNA256Receipt : DNA256Receipt.DNAClifford256StructuralCoincidenceReceipt
priorDNA256Receipt = DNA256Receipt.canonicalDNAClifford256StructuralCoincidenceReceipt

------------------------------------------------------------------------
-- Roadmap consequence.
------------------------------------------------------------------------

record DNA256RSA260RoadmapBoundary : Set where
  constructor dna256-rsa260-roadmap-boundary
  field
    dna256CarrierLocated : Bool
    dnaFourBySixtyFourHierarchyLocated : Bool
    dnaCriticalSampling256Located : Bool
    rsaFourBySixtyFourPackedCarrierExecuted : Bool
    structuralBlockPartitionReusableForRSAOracle : Bool
    dnaTransformIsGF2Transform : Bool
    dnaBasesAreGF2Bits : Bool
    rsaMatrixRecoveredFromDNA : Bool
    nextSparseMatVecShouldPreserveFourBySixtyFourPartition : Bool
open DNA256RSA260RoadmapBoundary public

currentDNA256RSA260RoadmapBoundary : DNA256RSA260RoadmapBoundary
currentDNA256RSA260RoadmapBoundary = dna256-rsa260-roadmap-boundary
  true true true true true
  false false false
  true

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data Same256ImpliesSameCarrier : Set where
data FourBySixtyFourShapeImpliesSameAlgebra : Set where
data DNACriticalTransformImpliesGF2BlockWiedemannTransform : Set where
data BiologyCarrierImpliesRSAData : Set where
data StructuralAnalogyImpliesExecutionReceipt : Set where

sameWidthDoesNotIdentifyCarrier : Same256ImpliesSameCarrier → ⊥
sameWidthDoesNotIdentifyCarrier ()

sameBlockShapeDoesNotIdentifyAlgebra : FourBySixtyFourShapeImpliesSameAlgebra → ⊥
sameBlockShapeDoesNotIdentifyAlgebra ()

dnaTransformDoesNotBecomeBlockWiedemann :
  DNACriticalTransformImpliesGF2BlockWiedemannTransform → ⊥
dnaTransformDoesNotBecomeBlockWiedemann ()

biologyDoesNotManufactureRSAData : BiologyCarrierImpliesRSAData → ⊥
biologyDoesNotManufactureRSAData ()

analogyDoesNotCreateRuntimeReceipt : StructuralAnalogyImpliesExecutionReceipt → ⊥
analogyDoesNotCreateRuntimeReceipt ()
