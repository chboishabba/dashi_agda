module DASHI.Analysis.RiemannHermitianExcessDetectabilityAssemblyExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Exact terminal composition for the retained-Hermitian-excess route.
--
-- Once analytic work has produced
--
--   * a normalized retained global Hermitian excess,
--   * an arithmetic error budget containing that excess,
--   * one target off-line pair inside the retained excess, and
--   * a strict gap placing that pair above the arithmetic error floor,
--
-- the contradiction is completely algebraic.  This module packages those
-- four facts into the existing `RiemannHermitianDetectabilityGapExact`
-- theorem, so the endgame no longer requires prose-level composition.
--
-- No analytic zeta theorem is asserted here.  In particular, the module does
-- not produce the retained excess, the prime-side error estimate, localization,
-- or the strict detectability gap.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Data.Empty using (⊥)

open import DASHI.Analysis.RiemannHermitianDetectabilityGapExact
  using
    ( ExcessErrorLedger
    ; excessErrorLedger
    ; HypotheticalOffLineWitness
    ; hypotheticalOffLineWitness
    ; DetectabilityGap
    ; detectabilityGap
    ; detectableOffLinePairContradictsGlobalErrorBound
    )

record HermitianExcessDetectabilityAssembly : Set where
  constructor hermitianExcessDetectabilityAssembly
  field
    retainedNormalizedExcess : Nat
    arithmeticErrorBudget : Nat
    arithmeticErrorSlack : Nat
    targetPairDefect : Nat
    otherRetainedDefect : Nat
    detectabilityGapPredecessor : Nat

    retainedWithinArithmeticError :
      retainedNormalizedExcess + arithmeticErrorSlack
        ≡ arithmeticErrorBudget

    targetPairInsideRetainedExcess :
      targetPairDefect + otherRetainedDefect
        ≡ retainedNormalizedExcess

    targetPairBeatsArithmeticError :
      arithmeticErrorBudget + suc detectabilityGapPredecessor
        ≡ targetPairDefect

open HermitianExcessDetectabilityAssembly public

toExcessErrorLedger :
  HermitianExcessDetectabilityAssembly → ExcessErrorLedger
toExcessErrorLedger a =
  excessErrorLedger
    (retainedNormalizedExcess a)
    (arithmeticErrorBudget a)
    (arithmeticErrorSlack a)
    (retainedWithinArithmeticError a)

toOffLineWitness :
  (a : HermitianExcessDetectabilityAssembly) →
  HypotheticalOffLineWitness (toExcessErrorLedger a)
toOffLineWitness a =
  hypotheticalOffLineWitness
    (targetPairDefect a)
    (otherRetainedDefect a)
    (targetPairInsideRetainedExcess a)

toDetectabilityGap :
  (a : HermitianExcessDetectabilityAssembly) →
  DetectabilityGap (toExcessErrorLedger a) (toOffLineWitness a)
toDetectabilityGap a =
  detectabilityGap
    (detectabilityGapPredecessor a)
    (targetPairBeatsArithmeticError a)

hermitianExcessDetectabilityContradiction :
  HermitianExcessDetectabilityAssembly → ⊥
hermitianExcessDetectabilityContradiction a =
  detectableOffLinePairContradictsGlobalErrorBound
    (toExcessErrorLedger a)
    (toOffLineWitness a)
    (toDetectabilityGap a)

------------------------------------------------------------------------
-- Source-facing producer surface.
--
-- This is the direct socket for the analytic route:
--
--   complex Poisson/cosh
--     -> finite retention
--     -> mixed-channel domination
--     -> normalized prime-side excess
--     -> localized/amplified pair beats error
--     -> this assembly
--     -> contradiction.
------------------------------------------------------------------------

record HermitianExcessDetectabilityProducer : Set₁ where
  field
    ZeroOrbit : Set
    offLine : ZeroOrbit → Set
    assemblyForOffLine :
      (rho : ZeroOrbit) →
      offLine rho →
      HermitianExcessDetectabilityAssembly

producerExcludesOffLine :
  (p : HermitianExcessDetectabilityProducer) →
  (rho : HermitianExcessDetectabilityProducer.ZeroOrbit p) →
  HermitianExcessDetectabilityProducer.offLine p rho →
  ⊥
producerExcludesOffLine p rho h =
  hermitianExcessDetectabilityContradiction
    (HermitianExcessDetectabilityProducer.assemblyForOffLine p rho h)

record HermitianExcessDetectabilityBoundary : Set where
  field
    normalizedExcessErrorLedgerComposed : Bool
    targetPairEmbeddingComposed : Bool
    strictDetectabilityGapComposed : Bool
    contradictionTheoremClosed : Bool
    offLineProducerExclusionClosed : Bool
    zetaRetainedExcessProducerConstructedHere : Bool
    zetaNormalizedPrimeErrorProducerConstructedHere : Bool
    zetaDetectabilityGapConstructedHere : Bool
    riemannHypothesisProvedHere : Bool

hermitianExcessDetectabilityBoundary : HermitianExcessDetectabilityBoundary
hermitianExcessDetectabilityBoundary = record
  { normalizedExcessErrorLedgerComposed = true
  ; targetPairEmbeddingComposed = true
  ; strictDetectabilityGapComposed = true
  ; contradictionTheoremClosed = true
  ; offLineProducerExclusionClosed = true
  ; zetaRetainedExcessProducerConstructedHere = false
  ; zetaNormalizedPrimeErrorProducerConstructedHere = false
  ; zetaDetectabilityGapConstructedHere = false
  ; riemannHypothesisProvedHere = false
  }
