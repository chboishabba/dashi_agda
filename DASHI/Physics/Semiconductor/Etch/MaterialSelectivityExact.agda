{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Etch.MaterialSelectivityExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

data Material : Set where
  Silicon : Material
  SiliconDioxide : Material
  SiliconNitride : Material
  Resist : Material
  HardMask : Material
  Metal : Material

record SurfaceResponse : Set where
  constructor surfaceResponse
  field
    material : Material
    ionFluxCode : Nat
    neutralFluxCode : Nat
    passivationCode : Nat
    removedSites : Nat

open SurfaceResponse public

-- Same plasma-delivery coordinates, different material response.
siliconResponse : SurfaceResponse
siliconResponse = surfaceResponse Silicon 100 80 10 70

oxideResponse : SurfaceResponse
oxideResponse = surfaceResponse SiliconDioxide 100 80 10 25

sameIonFlux : ionFluxCode siliconResponse ≡ ionFluxCode oxideResponse
sameIonFlux = refl

sameNeutralFlux : neutralFluxCode siliconResponse ≡ neutralFluxCode oxideResponse
sameNeutralFlux = refl

samePassivation : passivationCode siliconResponse ≡ passivationCode oxideResponse
samePassivation = refl

data ⊥ : Set where

materialIdentityMatters : removedSites siliconResponse ≡ removedSites oxideResponse → ⊥
materialIdentityMatters ()

-- Exact finite selectivity witness: 70/25 reduces to 14/5.
record SelectivityWitness (a b : SurfaceResponse) : Set where
  constructor selectivityWitness
  field
    numerator : Nat
    denominator : Nat
    equation : removedSites a * denominator ≡ removedSites b * numerator

open SelectivityWitness public

siliconToOxideSyntheticSelectivity : SelectivityWitness siliconResponse oxideResponse
siliconToOxideSyntheticSelectivity = selectivityWitness 14 5 refl

-- Scientific residuals needed before any production etch recipe can be owned.
data SelectivityResidual : Set where
  SurfaceBindingEnergy : SelectivityResidual
  VolatileProductFormation : SelectivityResidual
  AdsorptionProbability : SelectivityResidual
  DesorptionProbability : SelectivityResidual
  PolymerPassivationChemistry : SelectivityResidual
  SputterYieldByMaterial : SelectivityResidual
  TemperatureDependence : SelectivityResidual
  CrystalOrientationDependence : SelectivityResidual
  ExactGasChemistry : SelectivityResidual

-- Firewall:
-- Same incoming ion/neutral flux and passivation code does not imply the same
-- etch response across different materials.
