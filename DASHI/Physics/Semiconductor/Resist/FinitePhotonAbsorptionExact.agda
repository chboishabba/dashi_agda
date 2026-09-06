{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Resist.FinitePhotonAbsorptionExact where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Finite event-count carrier for one exposure region.
--
-- Incident photons are partitioned into absorbed, transmitted and reflected
-- counts.  This is deliberately a counting layer, not yet a probability law.
-- A later statistical owner can put a Binomial/Poisson model over these exact
-- finite outcomes without changing the event ontology.

record PhotonPartition : Set where
  constructor photonPartition
  field
    incident    : Nat
    absorbed    : Nat
    transmitted : Nat
    reflected   : Nat

open PhotonPartition public

PartitionConservesCount : PhotonPartition → Set
PartitionConservesCount x =
  absorbed x + (transmitted x + reflected x) ≡ incident x

exposureA : PhotonPartition
exposureA = photonPartition 100 60 30 10

exposureAConserves : PartitionConservesCount exposureA
exposureAConserves = refl

exposureB : PhotonPartition
exposureB = photonPartition 100 45 45 10

exposureBConserves : PartitionConservesCount exposureB
exposureBConserves = refl

sameIncidentCount : incident exposureA ≡ incident exposureB
sameIncidentCount = refl

data ⊥ : Set where

-- Same incident count does not determine absorption outcome.
absorptionNonDescent : absorbed exposureA ≡ absorbed exposureB → ⊥
absorptionNonDescent ()

-- Exact finite abstraction of an absorption trial summary.
record AbsorptionSummary : Set where
  constructor absorptionSummary
  field
    trials : Nat
    successes : Nat
    failures : Nat
    accounting : successes + failures ≡ trials

open AbsorptionSummary public

syntheticAbsorptionSummary : AbsorptionSummary
syntheticAbsorptionSummary = absorptionSummary 100 60 40 refl

-- Physics firewall:
-- Count conservation does not supply an absorption coefficient, depth profile,
-- Poisson/binomial law, electron yield, or chemical response.
