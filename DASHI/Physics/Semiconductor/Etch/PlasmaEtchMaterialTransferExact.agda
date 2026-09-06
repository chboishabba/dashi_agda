{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Etch.PlasmaEtchMaterialTransferExact where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Coarse plasma-etch state.  The goal is to separate ion delivery, neutral
-- chemistry, surface reaction and resulting geometry before introducing a
-- detailed sheath / transport / reaction model.

record EtchState : Set where
  constructor etchState
  field
    ionFluxCode      : Nat
    neutralFluxCode  : Nat
    reactiveSites    : Nat
    removedSites     : Nat
    sidewallLossCode : Nat

open EtchState public

-- Two synthetic executions with the same ion-flux coordinate but different
-- neutral chemistry and different material removal.
etchA : EtchState
etchA = etchState 100 80 90 70 8

etchB : EtchState
etchB = etchState 100 30 90 35 3

sameIonFlux : ionFluxCode etchA ≡ ionFluxCode etchB
sameIonFlux = refl

data ⊥ : Set where

ionFluxDoesNotDetermineRemoval : removedSites etchA ≡ removedSites etchB → ⊥
ionFluxDoesNotDetermineRemoval ()

-- Finite material-accounting carrier.  "removed + retained = initial" is a
-- bookkeeping theorem only; it does not assert where removed material goes or
-- whether the resulting profile is acceptable.
record MaterialPartition : Set where
  constructor materialPartition
  field
    initialSites : Nat
    removed      : Nat
    retained     : Nat
    conservation : removed + retained ≡ initialSites

open MaterialPartition public

syntheticMaterialPartition : MaterialPartition
syntheticMaterialPartition = materialPartition 100 70 30 refl

-- Scientific residuals for later descent.
data EtchResidual : Set where
  PlasmaSheathPotential : EtchResidual
  IonEnergyDistribution : EtchResidual
  IonAngularDistribution : EtchResidual
  RadicalDensityProfile : EtchResidual
  SurfaceReactionProbability : EtchResidual
  SputterYield : EtchResidual
  PassivationRate : EtchResidual
  LocalCharging : EtchResidual
  AspectRatioTransport : EtchResidual
  ExactSidewallProfile : EtchResidual

-- Firewall:
--   same ion flux != same etch rate/profile
-- because chemistry, energy/angular distributions, passivation and geometry
-- remain independent coordinates.
