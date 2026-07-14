module DASHI.Physics.Closure.NSTriadKNGate2ExactKNABoundedSampledTheorem where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNGate2ASampledComparisonEnvelope as Envelope
import DASHI.Physics.Closure.NSTriadKNGate2SampledFactorRouteWitness as Sampled

------------------------------------------------------------------------
-- Bounded exact-K_N(A) route theorem.
--
-- This is the strongest theorem currently supported by an inhabited
-- alternative-route input: the sampled shells N = 6, 8, 10 satisfy the
-- directional subquarter arithmetic and reject the coarse comparison route.
-- It is deliberately finite-shell and sampled.  It does not identify the
-- sampled ratio with the true PDE operator K_N(A), and it does not provide
-- the outside-seam decomposition.

record BoundedExactKNASampledRow : Set where
  constructor mkBoundedExactKNASampledRow
  field
    shell : Envelope.SampledShell

    directionalTransportReconstructs :
      Envelope.directionalProductUpper shell
        ≡ Envelope.directionalTheta shell

    directionalSubquarter :
      Envelope.directionalProductRouteBelowQuarter shell ≡ true

    directionalFactorBeatsCoarse :
      Envelope.directionalFactorBeatsShellwiseCoarseFactor shell ≡ true

    coarseRouteRejected :
      Envelope.shellwiseCoarseRouteCloses shell ≡ false

open BoundedExactKNASampledRow public

boundedExactKNASampledRow :
  (s : Envelope.SampledShell) → BoundedExactKNASampledRow
boundedExactKNASampledRow s =
  mkBoundedExactKNASampledRow
    s
    (Sampled.NSTriadKNGate2SampledFactorRouteWitnessPackage.directionalTransportReconstructs
      Sampled.canonicalNSTriadKNGate2SampledFactorRouteWitnessPackage
      s)
    (Sampled.NSTriadKNGate2SampledFactorRouteWitnessPackage.directionalTransportSubquarter
      Sampled.canonicalNSTriadKNGate2SampledFactorRouteWitnessPackage
      s)
    (Sampled.NSTriadKNGate2SampledFactorRouteWitnessPackage.directionalFactorBeatsCoarseFactor
      Sampled.canonicalNSTriadKNGate2SampledFactorRouteWitnessPackage
      s)
    (Sampled.NSTriadKNGate2SampledFactorRouteWitnessPackage.shellwiseCoarseRouteRejected
      Sampled.canonicalNSTriadKNGate2SampledFactorRouteWitnessPackage
      s)

------------------------------------------------------------------------
-- The bounded theorem consumes the existing concrete sampled package; no
-- pair-incidence or true-carrier hypothesis is introduced here.

boundedExactKNASampledDirectionalSubquarter :
  (s : Envelope.SampledShell) →
  Envelope.directionalProductRouteBelowQuarter s ≡ true
boundedExactKNASampledDirectionalSubquarter s =
  BoundedExactKNASampledRow.directionalSubquarter
    (boundedExactKNASampledRow s)

boundedExactKNASampledCoarseRouteRejected :
  (s : Envelope.SampledShell) →
  Envelope.shellwiseCoarseRouteCloses s ≡ false
boundedExactKNASampledCoarseRouteRejected s =
  BoundedExactKNASampledRow.coarseRouteRejected
    (boundedExactKNASampledRow s)
