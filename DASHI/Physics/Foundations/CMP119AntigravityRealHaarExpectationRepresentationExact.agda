{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealHaarExpectationRepresentationExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _-ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

------------------------------------------------------------------------
-- AG-S1 / LITERAL CMP119 EXPECTATION -> REAL PHYSICAL HAAR EXPECTATION
--
-- The finite CMP119 source expectation and the continuous SU(2)^E Haar
-- expectation are not the same carrier.  The correct bridge is a convergent
-- representation theorem, not a definitional equality.
------------------------------------------------------------------------

record RealHaarExpectationRepresentation
    (embedding : Embed.OrderedRationalRealEmbedding)
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError) : Set₁ where
  field
    finiteCMP119Expectation : Nat → ℚ
    physicalHaarExpectation : ℝ
    representationError : Nat → ℝ

    finiteApproximatesPhysical :
      ∀ cutoff →
      absℝ
        (physicalHaarExpectation
          -ℝ Embed.embed embedding (finiteCMP119Expectation cutoff))
      ≤ℝ representationError cutoff

    representationErrorVanishes :
      Seq.Vanishes sequenceLimit representationError

open RealHaarExpectationRepresentation public

embeddedFiniteExpectation :
  ∀ {embedding sequenceLimit} →
  RealHaarExpectationRepresentation embedding sequenceLimit →
  Nat → ℝ
embeddedFiniteExpectation {embedding = embedding} bridge cutoff =
  Embed.embed embedding (finiteCMP119Expectation bridge cutoff)

physicalHaarExpectationIsFiniteCMP119Limit :
  ∀ {embedding sequenceLimit}
    (bridge : RealHaarExpectationRepresentation embedding sequenceLimit) →
  Seq.limit sequenceLimit (embeddedFiniteExpectation bridge)
  ≡ physicalHaarExpectation bridge
physicalHaarExpectationIsFiniteCMP119Limit
    {embedding = embedding} {sequenceLimit = sequenceLimit} bridge =
  Seq.limitFromVanishingError sequenceLimit
    (embeddedFiniteExpectation bridge)
    (physicalHaarExpectation bridge)
    (representationError bridge)
    (finiteApproximatesPhysical bridge)
    (representationErrorVanishes bridge)

realHaarExpectationRepresentationCompilerLevel : ProofLevel
realHaarExpectationRepresentationCompilerLevel = machineChecked

-- Physical payment: construct this representation on the literal CMP119
-- cylinder/quadrature family and the SAME product/constrained Haar measure.
literalCMP119RealHaarExpectationRepresentationLevel : ProofLevel
literalCMP119RealHaarExpectationRepresentationLevel = conditional
