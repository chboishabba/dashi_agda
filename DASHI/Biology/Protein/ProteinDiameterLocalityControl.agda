module DASHI.Biology.Protein.ProteinDiameterLocalityControl where

-- Diameter and radius-like observables are control quantities derived from a
-- conformation.  They are not silently inserted as a new physical force.
record ProteinProfileGeometry : Set₁ where
  field
    Conformation  : Set
    Extent        : Set
    RadiusGyration : Set
    ContactMap    : Set
    SurfaceProfile : Set
    PocketProfile : Set
    DomainProfile : Set
    FlexibilityProfile : Set

    extent        : Conformation → Extent
    radiusGyration : Conformation → RadiusGyration
    contacts      : Conformation → ContactMap
    surface       : Conformation → SurfaceProfile
    pockets       : Conformation → PocketProfile
    domains       : Conformation → DomainProfile
    flexibility   : Conformation → FlexibilityProfile

record ProteinLocalityControl
  (G : ProteinProfileGeometry) : Set₁ where
  open ProteinProfileGeometry G
  field
    LocalContact : ContactMap → Set
    Compact      : Extent → Set
    DomainSeparated : DomainProfile → Set
    InterfaceReachControlled : SurfaceProfile → Set
    StericOverlapControlled  : ContactMap → Set

record ProteinDiameterBound
  (G : ProteinProfileGeometry) : Set₁ where
  open ProteinProfileGeometry G
  field
    Bound : Set
    _≤extent_ : Extent → Bound → Set
    boundFor : Conformation → Bound
    extentControlled :
      (x : Conformation) → extent x ≤extent boundFor x

record LocalityFromProfileWitness
  {G : ProteinProfileGeometry}
  (L : ProteinLocalityControl G) : Set₁ where
  open ProteinProfileGeometry G
  open ProteinLocalityControl L
  field
    conformation : Conformation
    localContacts : LocalContact (contacts conformation)
    domainSeparation : DomainSeparated (domains conformation)
    interfaceControlled : InterfaceReachControlled (surface conformation)
    overlapControlled : StericOverlapControlled (contacts conformation)

-- A scalar extent cannot replace the full profile.  Folding order and function
-- may depend on penetration, contact topology, pockets, charge, and flexibility
-- even when two conformations have comparable diameter.
record DiameterInsufficiencyBoundary
  (G : ProteinProfileGeometry) : Set₁ where
  open ProteinProfileGeometry G
  field
    first second : Conformation
    ComparableExtent : Extent → Extent → Set
    comparableExtent : ComparableExtent (extent first) (extent second)
    DistinctContactGeometry : ContactMap → ContactMap → Set
    distinctContacts : DistinctContactGeometry (contacts first) (contacts second)
