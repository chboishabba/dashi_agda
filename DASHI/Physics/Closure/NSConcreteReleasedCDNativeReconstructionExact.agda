module DASHI.Physics.Closure.NSConcreteReleasedCDNativeReconstructionExact where

------------------------------------------------------------------------
-- CONCRETE RELEASED C/D -> NATIVE AGDA LITERAL C/D
--
-- This owner removes the last INTERNAL adapter between the released-comparator
-- witness shape and the hardened terminal run target.
--
-- Starting from one FeffermanAnalyticKernel K, NSConcreteFeffermanSemanticsExact
-- fixes the Navier--Stokes equation, divergence, periodicity, initial trace,
-- decay and bounded-energy predicates.  A NATIVE Agda witness of the released
-- comparator theorem on exactly those predicates is compiled here directly to
--
--   LiteralC K / LiteralD K
--       -> ConcreteLiteralCDKernelBridge K
--       -> ConcreteLiteralNSRunTarget K.
--
-- There is intentionally no SHA/provenance/foreign-proof escape hatch.  The
-- only still-external obligation is proof production for the released
-- candidate construction itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSConcreteFeffermanSemanticsExact as Concrete
import DASHI.Physics.Closure.NSConcreteLiteralClayABCDRunTargetExact as Run
import DASHI.Physics.Closure.NSOpenAI2026ReleasedComparatorCanonicalWitnessExact as Witness

ConcreteReleasedComparatorCWitness :
  Concrete.FeffermanAnalyticKernel →
  BishopReal.ℝ →
  Set₁
ConcreteReleasedComparatorCWitness K viscosity =
  Witness.ReleasedComparatorCWitness
    (Run.concreteSemantics K) viscosity

ConcreteReleasedComparatorDWitness :
  Concrete.FeffermanAnalyticKernel →
  BishopReal.ℝ →
  Set₁
ConcreteReleasedComparatorDWitness K viscosity =
  Witness.ReleasedComparatorDWitness
    (Run.concreteSemantics K) viscosity

ConcreteReleasedComparatorCTheorem :
  Concrete.FeffermanAnalyticKernel →
  Set₁
ConcreteReleasedComparatorCTheorem K =
  (viscosity : BishopReal.ℝ) →
  Canonical.PositiveReal (Run.concreteSemantics K) viscosity →
  ConcreteReleasedComparatorCWitness K viscosity

ConcreteReleasedComparatorDTheorem :
  Concrete.FeffermanAnalyticKernel →
  Set₁
ConcreteReleasedComparatorDTheorem K =
  (viscosity : BishopReal.ℝ) →
  Canonical.PositiveReal (Run.concreteSemantics K) viscosity →
  ConcreteReleasedComparatorDWitness K viscosity

nativeReleasedComparatorCToLiteralC :
  ∀ {K} →
  ConcreteReleasedComparatorCTheorem K →
  Run.LiteralC K
nativeReleasedComparatorCToLiteralC {K} theorem =
  Witness.releasedComparatorCToLiteralStatement
    (Run.concreteSemantics K) theorem

nativeReleasedComparatorDToLiteralD :
  ∀ {K} →
  ConcreteReleasedComparatorDTheorem K →
  Run.LiteralD K
nativeReleasedComparatorDToLiteralD {K} theorem =
  Witness.releasedComparatorDToLiteralStatement
    (Run.concreteSemantics K) theorem

nativeReleasedComparatorCToRunTarget :
  ∀ {K} →
  ConcreteReleasedComparatorCTheorem K →
  Run.ConcreteLiteralNSRunTarget K
nativeReleasedComparatorCToRunTarget theorem =
  Run.runTargetFromC
    (nativeReleasedComparatorCToLiteralC theorem)

nativeReleasedComparatorDToRunTarget :
  ∀ {K} →
  ConcreteReleasedComparatorDTheorem K →
  Run.ConcreteLiteralNSRunTarget K
nativeReleasedComparatorDToRunTarget theorem =
  Run.runTargetFromD
    (nativeReleasedComparatorDToLiteralD theorem)

record ConcreteReleasedComparatorCDTheorems
    (K : Concrete.FeffermanAnalyticKernel) : Set₂ where
  field
    theoremC : ConcreteReleasedComparatorCTheorem K
    theoremD : ConcreteReleasedComparatorDTheorem K

open ConcreteReleasedComparatorCDTheorems public

nativeReleasedComparatorCDToKernelBridge :
  ∀ {K} →
  ConcreteReleasedComparatorCDTheorems K →
  Run.ConcreteLiteralCDKernelBridge K
nativeReleasedComparatorCDToKernelBridge proofs = record
  { Run.proofC =
      nativeReleasedComparatorCToLiteralC
        (ConcreteReleasedComparatorCDTheorems.theoremC proofs)
  ; Run.proofD =
      nativeReleasedComparatorDToLiteralD
        (ConcreteReleasedComparatorCDTheorems.theoremD proofs)
  }

nativeReleasedComparatorCDToRunTargetViaC :
  ∀ {K} →
  ConcreteReleasedComparatorCDTheorems K →
  Run.ConcreteLiteralNSRunTarget K
nativeReleasedComparatorCDToRunTargetViaC proofs =
  Run.runTargetFromCDKernelBridgeC
    (nativeReleasedComparatorCDToKernelBridge proofs)

nativeReleasedComparatorCDToRunTargetViaD :
  ∀ {K} →
  ConcreteReleasedComparatorCDTheorems K →
  Run.ConcreteLiteralNSRunTarget K
nativeReleasedComparatorCDToRunTargetViaD proofs =
  Run.runTargetFromCDKernelBridgeD
    (nativeReleasedComparatorCDToKernelBridge proofs)

------------------------------------------------------------------------
-- Trust-boundary audit.
------------------------------------------------------------------------

genericCanonicalSemanticsRemainAtTerminalCDBridge : Bool
genericCanonicalSemanticsRemainAtTerminalCDBridge = false

nativeComparatorWitnessCompilesDirectlyToLiteralC : Bool
nativeComparatorWitnessCompilesDirectlyToLiteralC = true

nativeComparatorWitnessCompilesDirectlyToLiteralD : Bool
nativeComparatorWitnessCompilesDirectlyToLiteralD = true

nativeComparatorWitnessCompilesDirectlyToRunTarget : Bool
nativeComparatorWitnessCompilesDirectlyToRunTarget = true

foreignReceiptCountsAsNativeComparatorWitness : Bool
foreignReceiptCountsAsNativeComparatorWitness = false

releasedCandidateConstructionReprovedHere : Bool
releasedCandidateConstructionReprovedHere = false

genericCanonicalSemanticsRemainAtTerminalCDBridgeIsFalse :
  genericCanonicalSemanticsRemainAtTerminalCDBridge ≡ false
genericCanonicalSemanticsRemainAtTerminalCDBridgeIsFalse = refl

nativeComparatorWitnessCompilesDirectlyToLiteralCIsTrue :
  nativeComparatorWitnessCompilesDirectlyToLiteralC ≡ true
nativeComparatorWitnessCompilesDirectlyToLiteralCIsTrue = refl

nativeComparatorWitnessCompilesDirectlyToLiteralDIsTrue :
  nativeComparatorWitnessCompilesDirectlyToLiteralD ≡ true
nativeComparatorWitnessCompilesDirectlyToLiteralDIsTrue = refl

nativeComparatorWitnessCompilesDirectlyToRunTargetIsTrue :
  nativeComparatorWitnessCompilesDirectlyToRunTarget ≡ true
nativeComparatorWitnessCompilesDirectlyToRunTargetIsTrue = refl

foreignReceiptCountsAsNativeComparatorWitnessIsFalse :
  foreignReceiptCountsAsNativeComparatorWitness ≡ false
foreignReceiptCountsAsNativeComparatorWitnessIsFalse = refl
