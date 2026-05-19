module DASHI.Physics.Closure.ObservableTransportPrimeCompatibilityProfile where

open import Agda.Primitive using (Setω)

open import Ontology.GodelLattice using (FactorVec)
open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB
open import DASHI.Physics.Closure.PrimeCompatibilityProfile as PCP
open import DASHI.Physics.Closure.TransportedPrimeCompatibilityProfile as TPCP

------------------------------------------------------------------------
-- Generic lift: if a closure bundle already exports a transport witness into a
-- target carrier and that target carrier has a prime-address image, then the
-- closure carrier inherits a prime compatibility profile and the smaller
-- witness-level bridge automatically.

transportPrimeImage :
  (B : AGMB.AbstractGaugeMatterBundle) →
  (w : AGMB.ObservableTransportWitness B) →
  (AGMB.TargetCarrier w → FactorVec) →
  AGMB.Carrier B → FactorVec
transportPrimeImage B w primeEmbedding x =
  primeEmbedding (AGMB.ObservableTransportWitness.transport w x)

observableTransportPrimeCompatibilityProfile :
  (B : AGMB.AbstractGaugeMatterBundle) →
  (w : AGMB.ObservableTransportWitness B) →
  (AGMB.TargetCarrier w → FactorVec) →
  PCP.PrimeCompatibilityProfile (AGMB.Carrier B)
observableTransportPrimeCompatibilityProfile B w primeEmbedding =
  TPCP.transportedPrimeCompatibilityProfile
    (transportPrimeImage B w primeEmbedding)
