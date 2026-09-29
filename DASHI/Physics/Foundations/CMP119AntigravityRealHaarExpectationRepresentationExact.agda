{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealHaarExpectationRepresentationExact where

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _-ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

------------------------------------------------------------------------
-- AG-S1 / FINITE CMP119 EXPECTATION -> REAL PHYSICAL HAAR EXPECTATION
--
-- Both sides already live in the repository's real scalar carrier.  The
-- missing theorem is quadrature/measure representation, not rational->real
-- embedding.
------------------------------------------------------------------------

record RealHaarExpectationRepresentation
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError) : Set₁ where
  field
    finiteCMP119Expectation : Nat → ℝ
    physicalHaarExpectation : ℝ
    representationError : Nat → ℝ

    finiteApproximatesPhysical :
      ∀ cutoff →
      absℝ
        (physicalHaarExpectation
          -ℝ finiteCMP119Expectation cutoff)
      ≤ℝ representationError cutoff

    representationErrorVanishes :
      Seq.Vanishes sequenceLimit representationError

open RealHaarExpectationRepresentation public

physicalHaarExpectationIsFiniteCMP119Limit :
  ∀ {sequenceLimit}
    (bridge : RealHaarExpectationRepresentation sequenceLimit) →
  Seq.limit sequenceLimit (finiteCMP119Expectation bridge)
  ≡ physicalHaarExpectation bridge
physicalHaarExpectationIsFiniteCMP119Limit
    {sequenceLimit = sequenceLimit} bridge =
  Seq.limitFromVanishingError sequenceLimit
    (finiteCMP119Expectation bridge)
    (physicalHaarExpectation bridge)
    (representationError bridge)
    (finiteApproximatesPhysical bridge)
    (representationErrorVanishes bridge)

realHaarExpectationRepresentationCompilerLevel : ProofLevel
realHaarExpectationRepresentationCompilerLevel = machineChecked

literalCMP119RealHaarExpectationRepresentationLevel : ProofLevel
literalCMP119RealHaarExpectationRepresentationLevel = conditional
