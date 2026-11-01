module DASHI.Physics.Chemistry.AtomicOrbitDiameterControl where

-- Diameter is a localisation/control observable.  It is not inserted as a new
-- physical force or an arbitrary additive energy term.

record AtomicOrbitDiameterControl : Set₁ where
  field
    ChargeIndex       : Set
    OrbitProfile      : Set
    Bound             : Set

    orbitAtCharge     : ChargeIndex → OrbitProfile → Set
    spectrallySelected : ChargeIndex → OrbitProfile → Set

    diameterBound     : OrbitProfile → Bound
    localized         : OrbitProfile → Set
    corePenetrating   : OrbitProfile → Set
    finiteOverlap     : OrbitProfile → OrbitProfile → Set

    spectralSelectionImpliesLocalization :
      ∀ {z ψ} → spectrallySelected z ψ → localized ψ

    localizationControlsDiameter :
      ∀ {ψ} → localized ψ → Set

    separatedDiameterControlsOverlap :
      ∀ {ψ φ} → localized ψ → localized φ → finiteOverlap ψ φ

-- The ordering of orbit profiles is intentionally richer than one scalar
-- diameter.  Penetration, nodal/angular data, screening and interaction terms
-- may be carried by ProfileDescriptor.
record OrbitSelectionDescriptor
  (D : AtomicOrbitDiameterControl) : Set₁ where
  open AtomicOrbitDiameterControl D
  field
    ProfileDescriptor : Set
    describe          : OrbitProfile → ProfileDescriptor
    LowerCost         : ProfileDescriptor → ProfileDescriptor → Set

    selectedIsAdmissibleMinimum :
      ∀ {z ψ} → spectrallySelected z ψ → Set
