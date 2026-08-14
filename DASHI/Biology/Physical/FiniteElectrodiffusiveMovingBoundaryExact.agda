module DASHI.Biology.Physical.FiniteElectrodiffusiveMovingBoundaryExact where

------------------------------------------------------------------------
-- SOURCE-FACING MOTIVATION
-- A. L. Hodgkin and A. F. Huxley,
-- "A quantitative description of membrane current and its application to
-- conduction and excitation in nerve", Journal of Physiology 117 (1952).
-- DOI: 10.1113/jphysiol.1952.sp004764.
--
-- Alan M. Turing, "The Chemical Basis of Morphogenesis",
-- Philosophical Transactions of the Royal Society B 237 (1952).
-- DOI: 10.1098/rstb.1952.0012.
--
-- DASHI CONTRIBUTION
-- Exact finite-volume skeletons for electrodiffusive transfer, charge balance,
-- moving-boundary material balance, and active free-energy bookkeeping.  These
-- are conservative discretisation invariants underneath a later analytic
-- Poisson--Nernst--Planck / mechanochemical moving-domain theorem; no PDE
-- existence/uniqueness claim is made here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.SIBiologyDimensionsExact as BioSI
import DASHI.Biology.Physical.PhysicalBiologyDimensionAlgebraExact as Dim
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- Typed continuum-law signature.
------------------------------------------------------------------------

record ElectrodiffusiveFieldLaw : Set₁ where
  field
    Position Species : Set
    ConcentrationField : Species → Position → Set
    PotentialField : Position → Set
    FluxField : Species → Position → Set
    ReactionField : Species → Position → Set
    nernstPlanckFlux :
      (i : Species) → (x : Position) →
      ConcentrationField i x → PotentialField x → FluxField i x
    continuityUpdate :
      (i : Species) → (x : Position) →
      ConcentrationField i x → FluxField i x → ReactionField i x →
      ConcentrationField i x

open ElectrodiffusiveFieldLaw public

record MovingBoundaryLaw : Set₁ where
  field
    BoundaryState BulkState ControlState : Set
    normalVelocity : BoundaryState → BulkState → ControlState → Nat
    advanceBoundary : BoundaryState → Nat → BoundaryState

open MovingBoundaryLaw public

------------------------------------------------------------------------
-- Finite two-volume electrodiffusive transport.
------------------------------------------------------------------------

record IonPairState : Set where
  constructor ionPair
  field
    left right : Nat

open IonPairState public

totalAmount : IonPairState → Nat
totalAmount s = left s + right s

data FluxDirection : Set where leftToRight rightToLeft stationary : FluxDirection

transport : FluxDirection → IonPairState → IonPairState
transport stationary s = s
transport leftToRight (ionPair zero r) = ionPair zero r
transport leftToRight (ionPair (suc l) r) = ionPair l (suc r)
transport rightToLeft (ionPair l zero) = ionPair l zero
transport rightToLeft (ionPair l (suc r)) = ionPair (suc l) r

transportConservesAmount :
  (d : FluxDirection) (s : IonPairState) →
  totalAmount (transport d s) ≡ totalAmount s
transportConservesAmount stationary s = refl
transportConservesAmount leftToRight (ionPair zero r) = refl
transportConservesAmount leftToRight (ionPair (suc l) r) = +-suc l r
transportConservesAmount rightToLeft (ionPair l zero) = refl
transportConservesAmount rightToLeft (ionPair l (suc r)) = sym (+-suc l r)

------------------------------------------------------------------------
-- Charge is amount times a fixed valence magnitude.  The signed multi-species
-- Poisson constraint is left to the analytic layer, but conservative transfer
-- cannot create charge magnitude for one fixed-valence species.
------------------------------------------------------------------------

chargeMagnitude : Nat → IonPairState → Nat
chargeMagnitude z s = z * totalAmount s

transportConservesChargeMagnitude :
  (z : Nat) (d : FluxDirection) (s : IonPairState) →
  chargeMagnitude z (transport d s) ≡ chargeMagnitude z s
transportConservesChargeMagnitude z d s =
  cong (λ n → z * n) (transportConservesAmount d s)

------------------------------------------------------------------------
-- Finite Reynolds-transport analogue for a growing material domain.
------------------------------------------------------------------------

record GrowingCompartment : Set where
  constructor growingCompartment
  field
    volumeCells materialAmount : Nat

open GrowingCompartment public

growBoundary : Nat → Nat → GrowingCompartment → GrowingCompartment
growBoundary addedVolume incomingMaterial c =
  growingCompartment
    (addedVolume + volumeCells c)
    (incomingMaterial + materialAmount c)

movingBoundaryMaterialBalance :
  (dv influx : Nat) (c : GrowingCompartment) →
  materialAmount (growBoundary dv influx c)
  ≡ influx + materialAmount c
movingBoundaryMaterialBalance dv influx c = refl

movingBoundaryVolumeBalance :
  (dv influx : Nat) (c : GrowingCompartment) →
  volumeCells (growBoundary dv influx c)
  ≡ dv + volumeCells c
movingBoundaryVolumeBalance dv influx c = refl

------------------------------------------------------------------------
-- Active free-energy bookkeeping.  Stored energy can rise only because a
-- metabolic/external work term appears explicitly in the balance.
------------------------------------------------------------------------

record ActiveEnergyStep : Set where
  constructor activeEnergyStep
  field
    storedBefore metabolicInput dissipation storedAfter : Nat
    balance : storedAfter + dissipation ≡ storedBefore + metabolicInput

open ActiveEnergyStep public

canonicalPassiveStep : ActiveEnergyStep
canonicalPassiveStep = activeEnergyStep 10 0 3 7 refl

passiveDissipationLowersStoredEnergy :
  storedAfter canonicalPassiveStep < storedBefore canonicalPassiveStep
passiveDissipationLowersStoredEnergy = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))

canonicalActiveStep : ActiveEnergyStep
canonicalActiveStep = activeEnergyStep 10 4 3 11 refl

activeEnergyBalance :
  storedAfter canonicalActiveStep + dissipation canonicalActiveStep
  ≡ storedBefore canonicalActiveStep + metabolicInput canonicalActiveStep
activeEnergyBalance = balance canonicalActiveStep

------------------------------------------------------------------------
-- SI owner bridge.  The seven-base-dimension SI owner and the existing MLT
-- mechanics owner are intentionally kept typed separately; the latter already
-- proves pressure-gradient = density*acceleration, while these aliases pin the
-- electrodiffusive carriers to the SI owner.
------------------------------------------------------------------------

MolarFluxDimension : SI.Dimension
MolarFluxDimension = BioSI.MolarFlux

CurrentDensityDimension : SI.Dimension
CurrentDensityDimension = BioSI.CurrentDensity

ForceDensityDimension : SI.Dimension
ForceDensityDimension = BioSI.ForceDensity

mechanicalForceDensityOwner : Set
mechanicalForceDensityOwner = Dim.biologicalForceDensityMechanicalDimension ≡ Dim.biologicalForceDensityMechanicalDimension

mechanicalForceDensityOwnerWitness : mechanicalForceDensityOwner
mechanicalForceDensityOwnerWitness = refl

record AnalyticAuthorityBoundary : Set where
  field
    finiteTransportProvesPNPWellPosedness : Bool
    finiteTransportProvesPNPWellPosednessIsFalse :
      finiteTransportProvesPNPWellPosedness ≡ false
    finiteMovingBoundaryProvesTopologicalMorphogenesisPDE : Bool
    finiteMovingBoundaryProvesTopologicalMorphogenesisPDEIsFalse :
      finiteMovingBoundaryProvesTopologicalMorphogenesisPDE ≡ false

canonicalAnalyticAuthorityBoundary : AnalyticAuthorityBoundary
canonicalAnalyticAuthorityBoundary = record
  { finiteTransportProvesPNPWellPosedness = false
  ; finiteTransportProvesPNPWellPosednessIsFalse = refl
  ; finiteMovingBoundaryProvesTopologicalMorphogenesisPDE = false
  ; finiteMovingBoundaryProvesTopologicalMorphogenesisPDEIsFalse = refl
  }
