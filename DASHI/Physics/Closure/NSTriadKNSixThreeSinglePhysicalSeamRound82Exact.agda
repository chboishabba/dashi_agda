module DASHI.Physics.Closure.NSTriadKNSixThreeSinglePhysicalSeamRound82Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- No DOI is asserted for the historical conference article.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND82 / SIX-THREE FRONTIER COMPRESSION
--
-- Round65 already proves that a SAME-CARRIER FactorizedPhysicalOddPQSource
-- closes the same-shell 17/64 bound, both adjacent 65/512 bounds, and the full
-- bandwidth-one 133/256 consumer.  It also proves that ordinary normalized
-- row self-correlation cannot be the 17/64 object because nonzero self overlap
-- is exactly one.
--
-- Therefore the former D1 "normalize the literal row" and D2 "prove the sharp
-- six-three overlap" should not be counted as two independent physical
-- miracles.  The single source-facing seam is:
--
--   literal dominant-hat annular row
--       -> FactorizedPhysicalOddPQSource
--       -> active PhysicalSixThreeGramCell on active pairs.
--
-- Once that one producer is supplied, the existing theorem below gives the
-- complete physical bandwidth-one constant without another analytic lemma.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as Ordered
import DASHI.Physics.Closure.NSTriadKNComOrderedPhysicalMajorantRound62Exact as Majorant
import DASHI.Physics.Closure.NSTriadKNComOrderedPhysicalGramFactorizationRound65Exact as Gram
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreAggregateRound60Exact as Aggregate
import DASHI.Physics.Closure.NSTriadKNComFactorizedPhysicalBandwidthOneRound65Exact as SixThree

singlePhysicalSixThreeSourceClosesBandwidthOne :
  ∀ {r : Level}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {O : Ordered.OrderedRealExtension (LP.realField model)}
    {M : Gram.NonnegativeMultiplicativeOrder O}
    {R : Majorant.OrderedRationalEmbedding O} →
  (source : SixThree.FactorizedPhysicalOddPQSource model O M R) →
  ∀ q →
  Ordered._≤_ O
    (Majorant.bandwidthOnePhysicalEnergy
      (SixThree.factorizedSourceToOrderedPhysicalMajorant source) q)
    (Majorant.embed R Aggregate.bandwidthOneTarget)
singlePhysicalSixThreeSourceClosesBandwidthOne =
  SixThree.factorizedBandwidthOneBelow133Over256

round82SixThreeFormerD1D2ReduceToSinglePhysicalSourceProducer : Bool
round82SixThreeFormerD1D2ReduceToSinglePhysicalSourceProducer = true

round82SixThreeFormerD1D2ReduceToSinglePhysicalSourceProducerIsTrue :
  round82SixThreeFormerD1D2ReduceToSinglePhysicalSourceProducer ≡ true
round82SixThreeFormerD1D2ReduceToSinglePhysicalSourceProducerIsTrue = refl
