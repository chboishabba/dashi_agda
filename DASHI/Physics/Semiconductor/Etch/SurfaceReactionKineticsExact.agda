{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Etch.SurfaceReactionKineticsExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Sources:
-- J. W. Coburn; Harold F. Winters,
-- "Plasma etching—A discussion of mechanisms",
-- Journal of Vacuum Science and Technology 16 (1979) 391–403,
-- DOI: 10.1116/1.569958.
--
-- J. W. Coburn; Harold F. Winters,
-- "Ion- and electron-assisted gas-surface chemistry—An important effect in plasma etching",
-- Journal of Applied Physics 50 (1979) 3189–3196,
-- DOI: 10.1063/1.326355.
--
-- These sources motivate separating adsorption, surface-product formation,
-- desorption/volatility, and ion-assisted enhancement.  The finite Nat-valued
-- carrier below is an exact bookkeeping skeleton, not a calibrated kinetic law.

record SurfaceReactionState : Set where
  constructor surfaceReactionState
  field
    arrivingReactiveSpecies : Nat
    adsorbedSpecies         : Nat
    activatedSites          : Nat
    volatileProducts        : Nat
    nonvolatileProducts     : Nat
    desorbedProducts        : Nat
    ionAssistanceCode       : Nat

open SurfaceReactionState public

-- Conservation seam for the product branch only.  It deliberately does not
-- claim every arriving species reacts, nor that every product desorbs.
ProductPartition : SurfaceReactionState → Set
ProductPartition x =
  volatileProducts x + nonvolatileProducts x ≡ activatedSites x

reactionA : SurfaceReactionState
reactionA = surfaceReactionState 100 80 60 45 15 40 20

reactionAProductPartition : ProductPartition reactionA
reactionAProductPartition = refl

reactionB : SurfaceReactionState
reactionB = surfaceReactionState 100 80 60 20 40 10 20

reactionBProductPartition : ProductPartition reactionB
reactionBProductPartition = refl

sameArrival : arrivingReactiveSpecies reactionA ≡ arrivingReactiveSpecies reactionB
sameArrival = refl

sameAdsorption : adsorbedSpecies reactionA ≡ adsorbedSpecies reactionB
sameAdsorption = refl

sameIonAssistance : ionAssistanceCode reactionA ≡ ionAssistanceCode reactionB
sameIonAssistance = refl

data ⊥ : Set where

-- Same incoming chemistry and same ion-assistance coordinate do not determine
-- volatile-product formation.  Material identity and surface state still matter.
volatileProductNonDescent :
  volatileProducts reactionA ≡ volatileProducts reactionB → ⊥
volatileProductNonDescent ()

-- A minimal rate skeleton represented without division:
--   removed * denominator = exposureTime * numerator.
record RemovalRateWitness : Set where
  constructor removalRateWitness
  field
    removedSites : Nat
    exposureTime : Nat
    numerator    : Nat
    denominator  : Nat
    rateLaw      : removedSites * denominator ≡ exposureTime * numerator

open RemovalRateWitness public

syntheticRemovalRate : RemovalRateWitness
syntheticRemovalRate = removalRateWitness 40 8 5 1 refl

-- Scientific residuals for later calibrated descent.
data SurfaceReactionResidual : Set where
  AdsorptionProbability        : SurfaceReactionResidual
  ActivationBarrier            : SurfaceReactionResidual
  SurfaceCoverageDependence    : SurfaceReactionResidual
  IonEnhancedReactionYield     : SurfaceReactionResidual
  ProductVolatility            : SurfaceReactionResidual
  DesorptionRateConstant       : SurfaceReactionResidual
  TemperatureDependence        : SurfaceReactionResidual
  MaterialSpecificRateLaw      : SurfaceReactionResidual
  ExactProcessChemistry        : SurfaceReactionResidual
