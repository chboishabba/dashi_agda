module DASHI.Physics.Closure.NSTriadKNLuoWeakNonAlignmentCircularityExact where

------------------------------------------------------------------------
-- PRIMARY AUDIT TARGET
--
-- Ryusho Nemoto,
-- "Global Regularity of the Three-Dimensional Navier-Stokes Equations via
-- a Coupled Energy and Stability Framework".
-- PhilArchive record: NEMGRO. DOI: none located.
-- Status: manuscript/preprint and audit target only.
--
-- DASHI CONTRIBUTION
--
-- The manuscript first uses weak non-alignment to derive a dissipative
-- inequality and later uses that dissipative inequality to assert automatic
-- weak non-alignment.  The two implications alone do not construct either
-- endpoint.
--
-- This is checked constructively by the empty countermodel:
--
--   A = empty,
--   B = empty.
--
-- Both maps A -> B and B -> A exist by empty elimination, while neither A nor
-- B is inhabited.  Therefore a dependency cycle is not a producer.  One of
-- the two directions must be established independently from the PDE.
--
-- The module also separates a long-time averaged statement from a finite-time
-- continuation statement: a map from the former to the latter is an explicit
-- additional field, not a consequence of naming both predicates.
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

record MutualImplication {A B : Set} : Set where
  constructor mutualImplication
  field
    forward : A → B
    backward : B → A

open MutualImplication public

emptyCycle : MutualImplication {A = ⊥} {B = ⊥}
emptyCycle = mutualImplication (λ ()) (λ ())

emptyCycleDoesNotProduceLeft :
  MutualImplication {A = ⊥} {B = ⊥} → ⊥ → ⊥
emptyCycleDoesNotProduceLeft cycle impossible = impossible

emptyCycleDoesNotProduceRight :
  MutualImplication {A = ⊥} {B = ⊥} → ⊥ → ⊥
emptyCycleDoesNotProduceRight cycle impossible = impossible

data ClosurePredicate : Set where
  weakNonAlignment dissipativeInequality finiteTimeContinuation : ClosurePredicate

record ClaimedClosureArrows : Set₁ where
  constructor claimedClosureArrows
  field
    Interpretation : ClosurePredicate → Set
    weakToDissipative :
      Interpretation weakNonAlignment →
      Interpretation dissipativeInequality
    dissipativeToWeak :
      Interpretation dissipativeInequality →
      Interpretation weakNonAlignment

open ClaimedClosureArrows public

emptyClosureInterpretation : ClosurePredicate → Set
emptyClosureInterpretation weakNonAlignment = ⊥
emptyClosureInterpretation dissipativeInequality = ⊥
emptyClosureInterpretation finiteTimeContinuation = ⊤

emptyClaimedClosureArrows : ClaimedClosureArrows
emptyClaimedClosureArrows =
  claimedClosureArrows
    emptyClosureInterpretation
    (λ ())
    (λ ())

record FiniteTimeBridge (arrows : ClaimedClosureArrows) : Set where
  constructor finiteTimeBridge
  field
    longAverageToFiniteContinuation :
      Interpretation arrows weakNonAlignment →
      Interpretation arrows finiteTimeContinuation

open FiniteTimeBridge public

emptyLongAverageBridge : FiniteTimeBridge emptyClaimedClosureArrows
emptyLongAverageBridge = finiteTimeBridge (λ ())

finiteContinuationCanBeTrueWhileCycleEndpointsAreEmpty :
  Interpretation emptyClaimedClosureArrows finiteTimeContinuation
finiteContinuationCanBeTrueWhileCycleEndpointsAreEmpty = tt

record CircularityAuditConclusion : Set where
  constructor circularityAuditConclusion
  field
    mutualImplicationAloneProducesEitherEndpoint : Set
    independentProducerRequired : Set
    longTimeAverageAutomaticallyControlsFiniteBlowup : Set

canonicalCircularityAuditConclusion : CircularityAuditConclusion
canonicalCircularityAuditConclusion =
  circularityAuditConclusion ⊥ ⊤ ⊥
