module DASHI.Physics.Closure.NSTriadKNCotlarSteinAggregationBoundaryRound74Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Elias M. Stein.
-- Title: "Harmonic Analysis: Real-Variable Methods, Orthogonality, and
-- Oscillatory Integrals", Chapter VII: Almost Orthogonality.
-- Princeton Mathematical Series 43.
-- Chapter DOI: 10.1515/9781400883929-010.
--
-- Historical context: the Cotlar--Stein almost-orthogonality lemma aggregates
-- pairwise T_j^* T_k / T_j T_k^* control into an operator bound.
--
-- ROUND74 / AUTHORITY BOUNDARY
--
-- The existing NS B-lane already performs the finite bandwidth-one aggregation
-- AFTER the physical pairwise estimates are available:
--
--   17/64 + 65/512 + 65/512 = 133/256.
--
-- Therefore Cotlar--Stein is a correct conceptual/provenance description of
-- that downstream almost-orthogonality step, but it does NOT manufacture the
-- still-missing physical theorem
--
--   physical overlap <= six-three scale envelope.
--
-- This file records that boundary constructively.  It reuses the exact existing
-- finite row aggregation and gives a counterexample showing that the aggregate
-- endpoint 133/256 alone cannot recover the sharper same-shell endpoint 17/64.
-- Hence B3 remains a pairwise physical geometry theorem, not an application of
-- Cotlar--Stein by itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _<_; _≤_)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as Gram
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreAggregateRound60Exact as Aggregate
import DASHI.Physics.Closure.NSTriadKNComActiveSixThreeRealizationRound61Exact as SixThree

cotlarStyleBandwidthOneAggregation :
  (physical : SixThree.PhysicalActiveSixThreeOddPQSource) →
  ∀ q →
  Aggregate.normalizedOddPQBandwidthOneMass
    (SixThree.asPhysicalNormalizedOddPQSource physical) q
  ≤ Aggregate.bandwidthOneTarget
cotlarStyleBandwidthOneAggregation =
  SixThree.fullBandwidthOneMassBelow133Over256

-- Exact finite falsifier: a row can obey the aggregate endpoint while violating
-- the desired same-shell endpoint.  Thus aggregation cannot replace B3.
counterSame counterForward counterReverse : ℚ
counterSame = Aggregate.bandwidthOneTarget
counterForward = 0ℚ
counterReverse = 0ℚ

counterAggregateExact :
  counterSame + counterForward + counterReverse
  ≡ Aggregate.bandwidthOneTarget
counterAggregateExact = refl

counterSameExceedsSixThreeSameShell :
  Gram.sameShellTarget < counterSame
counterSameExceedsSixThreeSameShell =
  toWitness {a? = Gram.sameShellTarget <? counterSame} _

round74CotlarSteinAggregationAlreadyDownstreamConstructed : Bool
round74CotlarSteinAggregationAlreadyDownstreamConstructed = true

round74AggregateEndpointImpliesPairwiseSixThreeEnvelope : Bool
round74AggregateEndpointImpliesPairwiseSixThreeEnvelope = false

round74PhysicalPairwiseSixThreeOverlapStillRequired : Bool
round74PhysicalPairwiseSixThreeOverlapStillRequired = true

round74AggregateEndpointImpliesPairwiseSixThreeEnvelopeIsFalse :
  round74AggregateEndpointImpliesPairwiseSixThreeEnvelope ≡ false
round74AggregateEndpointImpliesPairwiseSixThreeEnvelopeIsFalse = refl
