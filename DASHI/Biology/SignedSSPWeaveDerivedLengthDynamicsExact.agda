module DASHI.Biology.SignedSSPWeaveDerivedLengthDynamicsExact where

------------------------------------------------------------------------
-- GENERIC LENGTH DYNAMICS DERIVED FROM THE EXISTING WEAVE LANGUAGE
--
-- The rich signed summary carries four Nat-valued complexity fields.  Three
-- are already mechanically determined by the existing instruction/effect
-- semantics:
--
--   * programLength     = source instruction count;
--   * executionLength   = accumulated concrete work cost;
--   * normalFormLength  = source normal-form instruction count.
--
-- The execution cost is not fitted to the two examples: buildSixByNineFibre
-- literally constructs 54 sites in WeaveEffect, token/refinement instructions
-- are one concrete step, and removeInvariantMode changes an already-built
-- carrier without adding sites.  This reproduces both canonical 53 receipts.
-- Residual-witness length remains semantic metadata and is NOT invented here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Biology.SignedSSPWeaveRichMetadataCompilerExact as Rich

instructionExecutionCost : Signed.WeaveInstruction → Nat
instructionExecutionCost Signed.buildSixByNineFibre = 54
instructionExecutionCost Signed.removeInvariantMode = 0
instructionExecutionCost (Signed.introducePrime prime) = 1
instructionExecutionCost (Signed.introduceInversePrime prime) = 1
instructionExecutionCost Signed.introduceInvariantUnit = 1
instructionExecutionCost Signed.refineAt369 = 1

programExecutionCost : List Signed.WeaveInstruction → Nat
programExecutionCost [] = 0
programExecutionCost (instruction ∷ rest) =
  instructionExecutionCost instruction + programExecutionCost rest

programNormalFormLength : List Signed.WeaveInstruction → Nat
programNormalFormLength = Signed.listCount

canonicalVirtualExecutionCostIsThree :
  programExecutionCost Signed.canonicalVirtualFiftyThreeProgram ≡ 3
canonicalVirtualExecutionCostIsThree = refl

canonicalGeometryExecutionCostIsFiftyFour :
  programExecutionCost Signed.canonicalGeometricFiftyThreeProgram ≡ 54
canonicalGeometryExecutionCostIsFiftyFour = refl

canonicalVirtualNormalFormLengthIsThree :
  programNormalFormLength Signed.canonicalVirtualFiftyThreeProgram ≡ 3
canonicalVirtualNormalFormLengthIsThree = refl

canonicalGeometryNormalFormLengthIsTwo :
  programNormalFormLength Signed.canonicalGeometricFiftyThreeProgram ≡ 2
canonicalGeometryNormalFormLengthIsTwo = refl

------------------------------------------------------------------------
-- Only address/residual/residual-witness dynamics remain as inputs.
------------------------------------------------------------------------

record ResidualMetadataDynamics : Set₁ where
  field
    initialAddress : List Signed.WeaveInstruction → Signed.SSP.Address 3
    stepAddress :
      Signed.WeaveInstruction → Signed.SSP.Address 3 → Signed.SSP.Address 3

    initialResidual :
      List Signed.WeaveInstruction → Signed.Zero.ApproachDirection
    stepResidual :
      Signed.WeaveInstruction →
      Signed.Zero.ApproachDirection →
      Signed.Zero.ApproachDirection

    initialResidualWitnessLength : List Signed.WeaveInstruction → Nat
    stepResidualWitnessLength : Signed.WeaveInstruction → Nat → Nat

open ResidualMetadataDynamics public

compileRichMetadataDynamics :
  ResidualMetadataDynamics → Rich.RichMetadataDynamics
compileRichMetadataDynamics residual =
  record
    { Rich.initialMetadata = λ program →
        Rich.rich-execution-metadata
          (initialAddress residual program)
          (initialResidual residual program)
          (Signed.listCount program)
          0
          (programNormalFormLength program)
          (initialResidualWitnessLength residual program)
    ; Rich.stepMetadata = λ instruction metadata →
        Rich.rich-execution-metadata
          (stepAddress residual instruction (Rich.address369 metadata))
          (stepResidual residual instruction (Rich.zeroApproachResidual metadata))
          (Rich.programLength metadata)
          (Rich.executionLength metadata + instructionExecutionCost instruction)
          (Rich.normalFormLength metadata)
          (stepResidualWitnessLength residual instruction
            (Rich.residualWitnessLength metadata))
    }

record DerivedLengthDynamicsBoundary : Set where
  constructor derived-length-dynamics-boundary
  field
    programLengthDerivedFromInstructionList : Bool
    executionLengthDerivedFromInstructionSemantics : Bool
    normalFormLengthDerivedFromInstructionList : Bool
    canonicalVirtualLengthsRecovered : Bool
    canonicalGeometryLengthsRecovered : Bool
    addressDynamicsStillExternal : Bool
    zeroResidualDynamicsStillExternal : Bool
    residualWitnessLengthStillExternal : Bool

canonicalDerivedLengthDynamicsBoundary : DerivedLengthDynamicsBoundary
canonicalDerivedLengthDynamicsBoundary =
  derived-length-dynamics-boundary
    true true true true true
    true true true
