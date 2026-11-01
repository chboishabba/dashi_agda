{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPublishedWilsonRPRound461Exact where

------------------------------------------------------------------------
-- GOAL-1 A2 / ROUND461: USE PUBLISHED WILSON REFLECTION POSITIVITY DIRECTLY.
--
-- Osterwalder--Seiler / Menotti--Pelissetto already prove reflection
-- positivity for the Wilson lattice action.  For a human Clay proof there is
-- no requirement to reconstruct their Peter--Weyl square expansion inside
-- DASHI.  The least-privilege physical payment is a SAME-OBJECT application:
--
--   literal finite CMP119/Wilson reflected Gram test
--     = published positive-time gauge-invariant Wilson observable,
--
-- with the published nonnegative scalar interpreted as the literal real order.
--
-- The older StandaloneCMP119WilsonSquare remains a constructive audit/fallback.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayOSWilsonReflectionPositivityExact as Published
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PublishedWilsonRPApplication
    (Configuration : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    (algebra : OS2.CylinderOSAlgebra (Configuration → ℝ))
    : Set₂ where
  field
    published :
      Published.WilsonReflectionPositivityData
        (Configuration → ℝ) ℝ

    -- The source theorem's scalar positivity is literally the real order used
    -- by the CMP119 finite expectation.
    publishedNonnegativeIsRealNonnegative :
      ∀ value →
      Published.Nonnegative published value →
      0ℝ ≤ℝ value

    -- Each finite reflected Gram family is represented by the one
    -- gauge-invariant positive-time observable to which the published theorem
    -- applies.  This is the real A2 same-object payment.
    publishedObservable :
      ∀ cutoff →
      Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ →
      Configuration → ℝ

    publishedObservableGaugeInvariant :
      ∀ cutoff testFamily →
      Published.GaugeInvariant published
        (publishedObservable cutoff testFamily)

    publishedObservablePositiveTime :
      ∀ cutoff testFamily →
      Published.PositiveTimeObservable published
        (publishedObservable cutoff testFamily)

    reflectedGramIsPublishedExpectation :
      ∀ cutoff testFamily →
      Gram.physicalReflectedGramQuadraticForm
        (OS2.operations algebra)
        (λ observable →
          Limit.finiteExpectation family cutoff observable)
        testFamily
      ≡
      Published.reflectedProductExpectation published
        (publishedObservable cutoff testFamily)

open PublishedWilsonRPApplication public

finiteReflectionPositiveFromPublishedWilson :
  ∀ {Configuration sequenceLimit limitLaws quotient division family algebra}
    (application :
      PublishedWilsonRPApplication
        Configuration
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family algebra)
    cutoff testFamily →
  0ℝ ≤ℝ
    Gram.physicalReflectedGramQuadraticForm
      (OS2.operations algebra)
      (λ observable →
        Limit.finiteExpectation family cutoff observable)
      testFamily
finiteReflectionPositiveFromPublishedWilson application cutoff testFamily
  rewrite reflectedGramIsPublishedExpectation application cutoff testFamily =
  publishedNonnegativeIsRealNonnegative application _
    (Published.wilsonPositivityAtAnySeparationParity
      (published application)
      Published.evenSitePlane
      (publishedObservable application cutoff testFamily)
      (publishedObservableGaugeInvariant application cutoff testFamily)
      (publishedObservablePositiveTime application cutoff testFamily))

round461PublishedWilsonRPAuthorityLevel : ProofLevel
round461PublishedWilsonRPAuthorityLevel =
  Published.wilsonSitePlaneReflectionPositivityLevel

round461PublishedWilsonToFiniteOS2CompilerLevel : ProofLevel
round461PublishedWilsonToFiniteOS2CompilerLevel = machineChecked

-- A2 is therefore a same-object source attachment, not a new RP proof.
literalRound461PublishedWilsonSameObjectApplicationLevel : ProofLevel
literalRound461PublishedWilsonSameObjectApplicationLevel = conditional
