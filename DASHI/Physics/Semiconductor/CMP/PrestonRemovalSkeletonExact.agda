{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.CMP.PrestonRemovalSkeletonExact where

open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Source:
-- Jihoon Seo, "A review on chemical and mechanical phenomena at the wafer
-- interface during chemical mechanical planarization", Journal of Materials
-- Research 36 (2021) 235–257, DOI: 10.1557/s43578-020-00060-x.
--
-- Preston's empirical relation is MRR = K P V.  This finite owner stores the
-- multiplication skeleton only.  It does not assert that real CMP removal is
-- completely determined by pressure and velocity.

record PrestonCoordinates : Set where
  constructor prestonCoordinates
  field
    coefficientCode : Nat
    pressureCode    : Nat
    velocityCode    : Nat
    removalCode     : Nat

open PrestonCoordinates public

PrestonLaw : PrestonCoordinates → Set
PrestonLaw x =
  coefficientCode x * (pressureCode x * velocityCode x) ≡ removalCode x

syntheticPreston : PrestonCoordinates
syntheticPreston = prestonCoordinates 2 3 5 30

syntheticPrestonLaw : PrestonLaw syntheticPreston
syntheticPrestonLaw = refl

-- Same P and V do not determine the same physical removal when the effective
-- chemistry/contact coefficient differs.
cmpA : PrestonCoordinates
cmpA = prestonCoordinates 2 3 5 30

cmpB : PrestonCoordinates
cmpB = prestonCoordinates 4 3 5 60

samePressure : pressureCode cmpA ≡ pressureCode cmpB
samePressure = refl

sameVelocity : velocityCode cmpA ≡ velocityCode cmpB
sameVelocity = refl

data ⊥ : Set where

pressureVelocityDoNotDetermineRemoval : removalCode cmpA ≡ removalCode cmpB → ⊥
pressureVelocityDoNotDetermineRemoval ()

data CMPResidual : Set where
  PadCompliance : CMPResidual
  AbrasiveSizeDistribution : CMPResidual
  AbrasiveShape : CMPResidual
  SlurryChemistry : CMPResidual
  SurfacePassivation : CMPResidual
  RealContactArea : CMPResidual
  PatternDensity : CMPResidual
  DishingErosion : CMPResidual
  ExactProductionRecipe : CMPResidual
