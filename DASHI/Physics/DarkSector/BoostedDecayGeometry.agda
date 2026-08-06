module DASHI.Physics.DarkSector.BoostedDecayGeometry where

open import DASHI.Core.Prelude

import DASHI.Physics.DarkSector.MetastableLifetime as Lifetime

------------------------------------------------------------------------
-- Finite scaled version of ell = beta gamma c tau.  The factors are retained
-- separately so persistence depth is not confused with laboratory distance.

record BoostedDecayDatum : Set where
  constructor boostedDecayDatum
  field
    betaGammaUnits : Nat
    causalSpeedUnits : Nat
    properLifetimeUnits : Nat

open BoostedDecayDatum public

laboratoryDisplacement : BoostedDecayDatum → Nat
laboratoryDisplacement datum =
  betaGammaUnits datum
  * causalSpeedUnits datum
  * properLifetimeUnits datum

canonicalBoostedDecay : BoostedDecayDatum
canonicalBoostedDecay = boostedDecayDatum 2 1 4

canonicalLaboratoryDisplacementIsEight :
  laboratoryDisplacement canonicalBoostedDecay ≡ 8
canonicalLaboratoryDisplacementIsEight = refl

lifetimeMatchesScaledDecayDatum :
  properLifetimeUnits canonicalBoostedDecay
  ≡
  Lifetime.lifetimeUnits Lifetime.canonicalLongLivedDecay
lifetimeMatchesScaledDecayDatum = refl

------------------------------------------------------------------------
-- Two states with equal proper lifetime can have different lab displacement
-- when their boosts differ.

unboostedDecay : BoostedDecayDatum
unboostedDecay = boostedDecayDatum 1 1 4

boostChangesLaboratoryDisplacement :
  laboratoryDisplacement unboostedDecay ≡ 4
  ×
  laboratoryDisplacement canonicalBoostedDecay ≡ 8
boostChangesLaboratoryDisplacement = refl , refl

record BoostedDecayGeometryBoundary : Set where
  constructor boostedDecayGeometryBoundary
  field
    lifetimeTicksEqualSpatialDisplacement : Bool
    lifetimeTicksEqualSpatialDisplacementIsFalse :
      lifetimeTicksEqualSpatialDisplacement ≡ false

    finiteBetaGammaUnitsProveLorentzCovariance : Bool
    finiteBetaGammaUnitsProveLorentzCovarianceIsFalse :
      finiteBetaGammaUnitsProveLorentzCovariance ≡ false

    meanDisplacementDeterminesEveryDecayPoint : Bool
    meanDisplacementDeterminesEveryDecayPointIsFalse :
      meanDisplacementDeterminesEveryDecayPoint ≡ false

open BoostedDecayGeometryBoundary public

canonicalBoostedDecayGeometryBoundary : BoostedDecayGeometryBoundary
canonicalBoostedDecayGeometryBoundary =
  boostedDecayGeometryBoundary false refl false refl false refl
