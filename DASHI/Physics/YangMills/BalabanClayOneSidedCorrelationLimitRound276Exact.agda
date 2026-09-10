{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayOneSidedCorrelationLimitRound276Exact where

------------------------------------------------------------------------
-- ROUND276 / NS + RH SNOWBALL INTO CANONICAL YM-B1
--
-- NS: a closed-order limit bridge is compiler mathematics once the exact
--     approximants and their limit are the SAME object.
-- RH: a one-sided upper certificate is enough when the consumer only asks for
--     an upper bound; exact value reconstruction is unnecessary.
-- Gödel/code lanes: same-semantics transport must itself be proof-bearing.
--
-- Apply those three lessons directly to the canonical Yang--Mills B consumer.
-- We do NOT require finite correlations to equal the continuum correlation at
-- each cutoff.  We require the exact finite correlation sequence to converge to
-- the exact `ReconstructedClusteringSpectrum.connectedCorrelation` value, and
-- we preserve one common upper envelope through an order-closed limit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

------------------------------------------------------------------------
-- Generic one-sided limit compiler.
------------------------------------------------------------------------

record UpperClosedConvergence (Scalar : Set) : Set₁ where
  field
    Converges : (Nat → Scalar) → Scalar → Set
    LessEqual : Scalar → Scalar → Set

    upperClosedUnderLimit :
      (sequence : Nat → Scalar) (target upper : Scalar) →
      Converges sequence target →
      (∀ cutoff → LessEqual (sequence cutoff) upper) →
      LessEqual target upper

open UpperClosedConvergence public

uniformUpperSurvivesLimit :
  ∀ {Scalar}
    (orderLimit : UpperClosedConvergence Scalar)
    (sequence : Nat → Scalar) (target upper : Scalar) →
  Converges orderLimit sequence target →
  (∀ cutoff → LessEqual orderLimit (sequence cutoff) upper) →
  LessEqual orderLimit target upper
uniformUpperSurvivesLimit orderLimit sequence target upper =
  upperClosedUnderLimit orderLimit sequence target upper

------------------------------------------------------------------------
-- SAME-SPECTRUM finite/cutoff correlation sequence.
--
-- The target of convergence is definitionally the exact correlation consumed
-- by the spectral mass-gap theorem.  This prevents a neighbouring finite/RG
-- spatial correlation from paying B1 merely because it has a similar formula.
------------------------------------------------------------------------

record SameSpectrumFiniteCorrelationUpper
    {Observable Energy Bound : Set}
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound)
    : Set₁ where
  field
    orderLimit : UpperClosedConvergence Bound

    -- Exact selected finite/cutoff correlation approximation for the SAME
    -- observable/time coordinates used by the spectral consumer.
    finiteConnectedCorrelation :
      Nat → Observable → Nat → Bound

    -- Same-object convergence: no opaque "continuum limit exists" flag.
    finiteConvergesToSpectrumCorrelation : ∀ observable time →
      Converges orderLimit
        (λ cutoff → finiteConnectedCorrelation cutoff observable time)
        (Gap.connectedCorrelation spectrum observable time)

    -- Only the one-sided theorem actually required downstream.
    finiteUniformClusteringUpper : ∀ cutoff observable time →
      LessEqual orderLimit
        (finiteConnectedCorrelation cutoff observable time)
        (Gap.clusteringEnvelope spectrum observable time)

    -- The order proposition used to close the limit is literally the spectral
    -- consumer's order at the same two endpoints.
    orderIsSpectrumOrder : ∀ left right →
      LessEqual orderLimit left right ≡ Gap.LessEqual spectrum left right

open SameSpectrumFiniteCorrelationUpper public

continuumClusteringUpperPointwise :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound}
    (payment : SameSpectrumFiniteCorrelationUpper spectrum)
    observable time →
  Gap.LessEqual spectrum
    (Gap.connectedCorrelation spectrum observable time)
    (Gap.clusteringEnvelope spectrum observable time)
continuumClusteringUpperPointwise {spectrum = spectrum} payment observable time =
  let
    genericUpper :
      LessEqual (orderLimit payment)
        (Gap.connectedCorrelation spectrum observable time)
        (Gap.clusteringEnvelope spectrum observable time)
    genericUpper =
      uniformUpperSurvivesLimit
        (orderLimit payment)
        (λ cutoff → finiteConnectedCorrelation payment cutoff observable time)
        (Gap.connectedCorrelation spectrum observable time)
        (Gap.clusteringEnvelope spectrum observable time)
        (finiteConvergesToSpectrumCorrelation payment observable time)
        (λ cutoff → finiteUniformClusteringUpper payment cutoff observable time)
  in
  subst
    (λ proposition → proposition)
    (orderIsSpectrumOrder payment
      (Gap.connectedCorrelation spectrum observable time)
      (Gap.clusteringEnvelope spectrum observable time))
    genericUpper

compileFiniteUniformUpperToSpectrumClustering :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  SameSpectrumFiniteCorrelationUpper spectrum →
  Gap.ClusteringUpperBound spectrum
compileFiniteUniformUpperToSpectrumClustering payment =
  continuumClusteringUpperPointwise payment

------------------------------------------------------------------------
-- Proof-search boundary.
------------------------------------------------------------------------

record Round276Boundary : Set where
  constructor round276-boundary
  field
    exactFiniteEqualsContinuumRequired : Bool
    exactFiniteEqualsContinuumRequiredIsFalse :
      exactFiniteEqualsContinuumRequired ≡ false

    fullT5ClosureRequiredForB1 : Bool
    fullT5ClosureRequiredForB1IsFalse :
      fullT5ClosureRequiredForB1 ≡ false

    fullUnifiedNormRequiredForB1 : Bool
    fullUnifiedNormRequiredForB1IsFalse :
      fullUnifiedNormRequiredForB1 ≡ false

    sameSpectrumCorrelationConvergenceRequired : Bool
    sameSpectrumCorrelationConvergenceRequiredIsTrue :
      sameSpectrumCorrelationConvergenceRequired ≡ true

    finiteUniformOneSidedUpperRequiredOnThisRoute : Bool
    finiteUniformOneSidedUpperRequiredOnThisRouteIsTrue :
      finiteUniformOneSidedUpperRequiredOnThisRoute ≡ true

canonicalRound276Boundary : Round276Boundary
canonicalRound276Boundary =
  round276-boundary false refl false refl false refl true refl true refl

round276OneSidedLimitCompilerLevel : ProofLevel
round276OneSidedLimitCompilerLevel = machineChecked

-- For the physical real/spectral carrier this is standard ordered-limit
-- mathematics, but the exact concrete instance must still be supplied.
round276ConcreteUpperClosedLimitAuthorityLevel : ProofLevel
round276ConcreteUpperClosedLimitAuthorityLevel = standardImported

-- These are the actual YM producer coordinates on this route.
round276SameSpectrumCorrelationConvergenceLevel : ProofLevel
round276SameSpectrumCorrelationConvergenceLevel = conditional

round276FiniteUniformCorrelationUpperLevel : ProofLevel
round276FiniteUniformCorrelationUpperLevel = conditional
