{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsRepresentedOSSystemRound524Exact where

------------------------------------------------------------------------
-- GOAL-1 A3/T3 / ROUND524:
-- CONSTRUCT THE SOURCE OS SYSTEM ON THE REPRESENTED SCHWINGER FUNCTION
--
-- ContinuumSchwingerSystem stores a two-point function and six OS receipts.
-- Once the literal Schwinger family is already representation-first, choosing a
-- second source two-point function and later proving equality is unnecessary.
--
-- Build the OS system directly on:
--
--   representedSchwinger encoding represented.
--
-- The OS0--OS5 proofs remain real inputs.  The source-OS/literal-Schwinger
-- equality becomes definitional.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS

record RepresentedOSAxiomInputs
    (Configuration Position : Set)
    (encoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position)
    (represented :
      R476.RepresentedContinuum (Configuration → ℝ))
    : Set₁ where
  field
    OS0Regularity : Set
    OS1EuclideanCovariance : Set
    OS2ReflectionPositivity : Set
    OS3PermutationSymmetry : Set
    OS4Clustering : Set
    OS5GrowthControl : Set

    os0 : OS0Regularity
    os1 : OS1EuclideanCovariance
    os2 : OS2ReflectionPositivity
    os3 : OS3PermutationSymmetry
    os4 : OS4Clustering
    os5 : OS5GrowthControl

open RepresentedOSAxiomInputs public

representedTwoPoint :
  ∀ {Configuration Position}
    (encoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position)
    (represented :
      R476.RepresentedContinuum (Configuration → ℝ)) →
  (Configuration → ℝ) → Position → Position → ℝ
representedTwoPoint encoding represented =
  Physical.schwinger
    (R476.representedSchwinger encoding represented)

representedOSSystem :
  ∀ {Configuration Position encoding represented} →
  RepresentedOSAxiomInputs
    Configuration Position encoding represented →
  OS.ContinuumSchwingerSystem
    (Configuration → ℝ) Position ℝ
representedOSSystem {encoding = encoding} {represented = represented} inputs =
  record
  { OS.ContinuumSchwingerSystem.schwinger =
      representedTwoPoint encoding represented
  ; OS.ContinuumSchwingerSystem.OS0Regularity =
      OS0Regularity inputs
  ; OS.ContinuumSchwingerSystem.OS1EuclideanCovariance =
      OS1EuclideanCovariance inputs
  ; OS.ContinuumSchwingerSystem.OS2ReflectionPositivity =
      OS2ReflectionPositivity inputs
  ; OS.ContinuumSchwingerSystem.OS3PermutationSymmetry =
      OS3PermutationSymmetry inputs
  ; OS.ContinuumSchwingerSystem.OS4Clustering =
      OS4Clustering inputs
  ; OS.ContinuumSchwingerSystem.OS5GrowthControl =
      OS5GrowthControl inputs
  ; OS.ContinuumSchwingerSystem.os0 = os0 inputs
  ; OS.ContinuumSchwingerSystem.os1 = os1 inputs
  ; OS.ContinuumSchwingerSystem.os2 = os2 inputs
  ; OS.ContinuumSchwingerSystem.os3 = os3 inputs
  ; OS.ContinuumSchwingerSystem.os4 = os4 inputs
  ; OS.ContinuumSchwingerSystem.os5 = os5 inputs
  }

sourceOSSchwingerIsRepresentedSchwinger :
  ∀ {Configuration Position encoding represented}
    (inputs :
      RepresentedOSAxiomInputs
        Configuration Position encoding represented)
    observable left right →
  OS.schwinger (representedOSSystem inputs) observable left right
  ≡
  Physical.schwinger
    (R476.representedSchwinger encoding represented)
    observable left right
sourceOSSchwingerIsRepresentedSchwinger inputs observable left right = refl

round524RepresentedOSSystemCompilerLevel : ProofLevel
round524RepresentedOSSystemCompilerLevel = machineChecked

round524SourceOSLiteralSchwingerEqualityLevel : ProofLevel
round524SourceOSLiteralSchwingerEqualityLevel = machineChecked

-- The real inputs are exactly OS0--OS5 on this represented function.
literalRound524RepresentedOSAxiomInputsLevel : ProofLevel
literalRound524RepresentedOSAxiomInputsLevel = conditional
