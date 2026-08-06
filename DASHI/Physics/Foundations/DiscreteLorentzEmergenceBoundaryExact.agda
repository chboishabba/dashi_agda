module DASHI.Physics.Foundations.DiscreteLorentzEmergenceBoundaryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Internal discreteness and spacetime discreteness are separate axes.

data InternalCarrierKind : Set where
  finiteTriadicInternalCarrier : InternalCarrierKind
  continuousInternalCarrier : InternalCarrierKind

data SpacetimeCarrierKind : Set where
  continuousSpacetimeCarrier : SpacetimeCarrierKind
  regularLatticeSpacetimeCarrier : SpacetimeCarrierKind
  randomCausalDiscreteCarrier : SpacetimeCarrierKind

record CarrierProduct : Set where
  constructor carrierProduct
  field
    internalCarrier : InternalCarrierKind
    spacetimeCarrier : SpacetimeCarrierKind

open CarrierProduct public

triadicInternalContinuousSpacetime : CarrierProduct
triadicInternalContinuousSpacetime =
  carrierProduct finiteTriadicInternalCarrier continuousSpacetimeCarrier

triadicInternalDoesNotForceSpacetimeLattice :
  spacetimeCarrier triadicInternalContinuousSpacetime
  ≡
  continuousSpacetimeCarrier
triadicInternalDoesNotForceSpacetimeLattice = refl

------------------------------------------------------------------------
-- A fixed regular lattice has direction-dependent high-frequency penalties in
-- this finite model, while its declared infrared sector is isotropic.

data MomentumDirection : Set where
  axisMomentum : MomentumDirection
  diagonalMomentum : MomentumDirection

data MomentumRegime : Set where
  infraredMomentum : MomentumRegime
  ultravioletMomentum : MomentumRegime

latticeCorrection : MomentumRegime → MomentumDirection → Nat
latticeCorrection infraredMomentum axisMomentum = 0
latticeCorrection infraredMomentum diagonalMomentum = 0
latticeCorrection ultravioletMomentum axisMomentum = 1
latticeCorrection ultravioletMomentum diagonalMomentum = 2

infraredCorrectionIsDirectionIndependent :
  latticeCorrection infraredMomentum axisMomentum
  ≡
  latticeCorrection infraredMomentum diagonalMomentum
infraredCorrectionIsDirectionIndependent = refl

ultravioletCorrectionDetectsPreferredDirections :
  latticeCorrection ultravioletMomentum axisMomentum ≡ 1
  ×
  latticeCorrection ultravioletMomentum diagonalMomentum ≡ 2
ultravioletCorrectionDetectsPreferredDirections = refl , refl

------------------------------------------------------------------------
-- Controlled low-energy relativistic dispersion with a bounded correction.

record EffectiveDispersionDatum : Set where
  constructor effectiveDispersionDatum
  field
    energySquared : Nat
    momentumSquared : Nat
    massSquared : Nat
    correction : Nat

open EffectiveDispersionDatum public

canonicalInfraredDispersion : EffectiveDispersionDatum
canonicalInfraredDispersion = effectiveDispersionDatum 25 9 16 0

canonicalUltravioletDispersion : EffectiveDispersionDatum
canonicalUltravioletDispersion = effectiveDispersionDatum 27 9 16 2

relativisticResidual : EffectiveDispersionDatum → Nat
relativisticResidual datum =
  (energySquared datum ∸ (momentumSquared datum + massSquared datum))
  +
  ((momentumSquared datum + massSquared datum) ∸ energySquared datum)

infraredResidualVanishes :
  relativisticResidual canonicalInfraredDispersion ≡ 0
infraredResidualVanishes = refl

ultravioletResidualIsTwo :
  relativisticResidual canonicalUltravioletDispersion ≡ 2
ultravioletResidualIsTwo = refl

record DiscreteLorentzBoundary : Set where
  constructor discreteLorentzBoundary
  field
    finiteInternalAlphabetImpliesSpacetimeDiscreteness : Bool
    finiteInternalAlphabetImpliesSpacetimeDiscretenessIsFalse :
      finiteInternalAlphabetImpliesSpacetimeDiscreteness ≡ false

    everyDiscreteSpacetimeHasObservableInfraredLorentzViolation : Bool
    everyDiscreteSpacetimeHasObservableInfraredLorentzViolationIsFalse :
      everyDiscreteSpacetimeHasObservableInfraredLorentzViolation ≡ false

    regularLatticePreservesExactContinuousLorentzSymmetryAtAllScales : Bool
    regularLatticePreservesExactContinuousLorentzSymmetryAtAllScalesIsFalse :
      regularLatticePreservesExactContinuousLorentzSymmetryAtAllScales ≡ false

    oneInfraredDispersionWitnessProvesPoincareInvariance : Bool
    oneInfraredDispersionWitnessProvesPoincareInvarianceIsFalse :
      oneInfraredDispersionWitnessProvesPoincareInvariance ≡ false

open DiscreteLorentzBoundary public

canonicalDiscreteLorentzBoundary : DiscreteLorentzBoundary
canonicalDiscreteLorentzBoundary =
  discreteLorentzBoundary false refl false refl false refl false refl
