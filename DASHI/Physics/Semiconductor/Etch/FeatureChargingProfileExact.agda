{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Etch.FeatureChargingProfileExact where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Source:
-- J. C. Arnold; H. H. Sawin,
-- "Charging of pattern features during plasma etching",
-- Journal of Applied Physics 70 (1991) 5314–5317,
-- DOI: 10.1063/1.350241.
--
-- Arnold and Sawin model localized charging in insulating trench features and
-- show that the resulting electric field can deflect arriving ions and alter
-- local ion flux / profile evolution.  The finite code below owns that causal
-- factorization only; it is not an electrostatic field solver.

record ChargingState : Set where
  constructor chargingState
  field
    electronArrivalCode : Nat
    ionArrivalCode      : Nat
    netChargeCode       : Nat
    ionDeflectionCode   : Nat
    bottomRemovalCode   : Nat
    sidewallRemovalCode : Nat

open ChargingState public

unchargedLike : ChargingState
unchargedLike = chargingState 100 100 0 0 70 5

chargedLike : ChargingState
chargedLike = chargingState 80 100 20 25 45 20

sameIonArrival : ionArrivalCode unchargedLike ≡ ionArrivalCode chargedLike
sameIonArrival = refl

data ⊥ : Set where

-- Equal incoming ion count at the feature entrance does not determine equal
-- bottom removal once local charging/deflection differs.
chargingBreaksIonArrivalDescent :
  bottomRemovalCode unchargedLike ≡ bottomRemovalCode chargedLike → ⊥
chargingBreaksIonArrivalDescent ()

profileNonDescent :
  sidewallRemovalCode unchargedLike ≡ sidewallRemovalCode chargedLike → ⊥
profileNonDescent ()

-- Simple charge accounting fixture.  This is a code-level conservation seam,
-- not Coulomb's law and not a capacitance model.
record ChargeAccounting : Set where
  constructor chargeAccounting
  field
    positiveArrivals : Nat
    negativeArrivals : Nat
    residualPositive : Nat
    accounting       : negativeArrivals + residualPositive ≡ positiveArrivals

open ChargeAccounting public

syntheticChargeAccounting : ChargeAccounting
syntheticChargeAccounting = chargeAccounting 100 80 20 refl

data ChargingResidual : Set where
  LocalPotential             : ChargingResidual
  CapacitanceGeometry        : ChargingResidual
  ElectronAngularFlux        : ChargingResidual
  IonTrajectoryDeflection    : ChargingResidual
  DielectricLeakage          : ChargingResidual
  ElectronTunneling          : ChargingResidual
  TimeDependentChargeBalance : ChargingResidual
  NotchGeometryEvolution     : ChargingResidual
  ExactChargingRecipeCoupling : ChargingResidual
