module DASHI.Core.IsotypicMultiplicityObserverRefinementExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Incoming marked-Hecke work (#585) exhibits the exact pattern
--
--   scalar joint fingerprint
--       < representation/isotypic observer
--       < representation + multiplicity observer.
--
-- In particular, two states can agree on every scalar observable which factors
-- through a chosen joint spectral fingerprint while differing either in their
-- irreducible symmetry type or inside a multiplicity copy of the SAME type.
--
-- This module extracts that theorem generically into the existing observer
-- refinement lattice.  It does not assume that representation labels are
-- physical truth, that a commutant is complete, or that every scalar operator
-- factors through the selected fingerprint.  Factorization is an explicit
-- premise for each scalar observer family.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- Three observer axes: scalar spectral data, irrep label, multiplicity label.
------------------------------------------------------------------------

record RepresentationObserverSystem
    (State Spectral Irrep Multiplicity : Set) : Set where
  field
    spectral : Observer.Observer State Spectral
    irrep : Observer.Observer State Irrep
    multiplicity : Observer.Observer State Multiplicity

open RepresentationObserverSystem public

isotypicObserver :
  ∀ {State Spectral Irrep Multiplicity} →
  RepresentationObserverSystem State Spectral Irrep Multiplicity →
  Observer.Observer State (Spectral × Irrep)
isotypicObserver system =
  Observer.pairObserver (spectral system) (irrep system)

multiplicityObserver :
  ∀ {State Spectral Irrep Multiplicity} →
  RepresentationObserverSystem State Spectral Irrep Multiplicity →
  Observer.Observer State (Spectral × (Irrep × Multiplicity))
multiplicityObserver system x =
  spectral system x , (irrep system x , multiplicity system x)

isotypicRefinesSpectral :
  ∀ {State Spectral Irrep Multiplicity}
    (system : RepresentationObserverSystem State Spectral Irrep Multiplicity) →
  Observer.Refines (spectral system) (isotypicObserver system)
isotypicRefinesSpectral system =
  Observer.pairRefinesLeft (spectral system) (irrep system)

multiplicityRefinesIsotypic :
  ∀ {State Spectral Irrep Multiplicity}
    (system : RepresentationObserverSystem State Spectral Irrep Multiplicity) →
  Observer.Refines (isotypicObserver system) (multiplicityObserver system)
multiplicityRefinesIsotypic system x y equality =
  let
    sameSpectral = cong proj₁ equality
    sameIrrep = cong (λ value → proj₁ (proj₂ value)) equality
  in
  cong₂ _,_ sameSpectral sameIrrep

multiplicityRefinesSpectral :
  ∀ {State Spectral Irrep Multiplicity}
    (system : RepresentationObserverSystem State Spectral Irrep Multiplicity) →
  Observer.Refines (spectral system) (multiplicityObserver system)
multiplicityRefinesSpectral system x y equality = cong proj₁ equality

------------------------------------------------------------------------
-- Two distinct failure modes of a scalar spectral observer.
------------------------------------------------------------------------

record IsotypicCollision
    {State Spectral Irrep Multiplicity : Set}
    (system : RepresentationObserverSystem State Spectral Irrep Multiplicity) : Set where
  field
    left right : State
    sameSpectral : spectral system left ≡ spectral system right
    differentIrrep : irrep system left ≡ irrep system right → ⊥

open IsotypicCollision public

isotypicCollisionGivesStrictRefinement :
  ∀ {State Spectral Irrep Multiplicity}
    {system : RepresentationObserverSystem State Spectral Irrep Multiplicity} →
  IsotypicCollision system →
  Observer.StrictRefinement
    (spectral system)
    (isotypicObserver system)
isotypicCollisionGivesStrictRefinement {system = system} collision =
  Observer.strictPairRefinement
    (spectral system)
    (irrep system)
    (left collision)
    (right collision)
    (sameSpectral collision)
    (differentIrrep collision)

record MultiplicityCollision
    {State Spectral Irrep Multiplicity : Set}
    (system : RepresentationObserverSystem State Spectral Irrep Multiplicity) : Set where
  field
    left right : State
    sameSpectral : spectral system left ≡ spectral system right
    sameIrrep : irrep system left ≡ irrep system right
    differentMultiplicity :
      multiplicity system left ≡ multiplicity system right → ⊥

open MultiplicityCollision public

multiplicityCollisionGivesStrictIsotypicRefinement :
  ∀ {State Spectral Irrep Multiplicity}
    {system : RepresentationObserverSystem State Spectral Irrep Multiplicity} →
  MultiplicityCollision system →
  Observer.StrictRefinement
    (isotypicObserver system)
    (multiplicityObserver system)
multiplicityCollisionGivesStrictIsotypicRefinement {system = system} collision =
  Observer.strictRefinement
    (multiplicityRefinesIsotypic system)
    (left collision)
    (right collision)
    (cong₂ _,_ (sameSpectral collision) (sameIrrep collision))
    (λ equality →
      differentMultiplicity collision
        (cong (λ value → proj₂ (proj₂ value)) equality))

------------------------------------------------------------------------
-- Any scalar observer explicitly generated from the chosen spectral
-- fingerprint remains constant on a spectral fibre.
------------------------------------------------------------------------

record SpectralFactorizedObserver
    {State Spectral Value : Set}
    (spectralObserver : Observer.Observer State Spectral) : Set where
  field
    observe : Observer.Observer State Value
    factor : Spectral → Value
    factorsExactly : (x : State) → observe x ≡ factor (spectralObserver x)

open SpectralFactorizedObserver public

spectralCollisionPropagatesThroughFactorizedObserver :
  ∀ {State Spectral Value}
    {spectralObserver : Observer.Observer State Spectral} →
  (generated : SpectralFactorizedObserver {Value = Value} spectralObserver) →
  (x y : State) →
  spectralObserver x ≡ spectralObserver y →
  observe generated x ≡ observe generated y
spectralCollisionPropagatesThroughFactorizedObserver generated x y same =
  trans
    (factorsExactly generated x)
    (trans
      (cong (factor generated) same)
      (sym (factorsExactly generated y)))

record IndexedSpectralObserverFamily
    {State Spectral : Set}
    (Index Value : Set)
    (spectralObserver : Observer.Observer State Spectral) : Set where
  field
    observeAt : Index → Observer.Observer State Value
    factorAt : Index → Spectral → Value
    factorsExactlyAt :
      (index : Index) → (x : State) →
      observeAt index x ≡ factorAt index (spectralObserver x)

open IndexedSpectralObserverFamily public

spectralCollisionInvisibleToWholeGeneratedFamily :
  ∀ {State Spectral Index Value}
    {spectralObserver : Observer.Observer State Spectral} →
  (family : IndexedSpectralObserverFamily Index Value spectralObserver) →
  (x y : State) →
  spectralObserver x ≡ spectralObserver y →
  (index : Index) →
  observeAt family index x ≡ observeAt family index y
spectralCollisionInvisibleToWholeGeneratedFamily family x y same index =
  trans
    (factorsExactlyAt family index x)
    (trans
      (cong (factorAt family index) same)
      (sym (factorsExactlyAt family index y)))

------------------------------------------------------------------------
-- Boundary: a scalar family generated by the spectral fingerprint cannot
-- recover representation data which the fingerprint has already quotiented.
------------------------------------------------------------------------

record IsotypicMultiplicityObserverBoundary : Set where
  field
    irrepCanStrictlyRefineScalarFingerprint : Bool
    multiplicityCanStrictlyRefineIsotypicFingerprint : Bool
    factorizedScalarFamilyCannotRepairSpectralCollision : Bool
    representationLabelsAutomaticallyPhysicallyComplete : Bool
    allCommutantOperatorsAutomaticallyFactorThroughChosenSpectrum : Bool

canonicalIsotypicMultiplicityObserverBoundary :
  IsotypicMultiplicityObserverBoundary
canonicalIsotypicMultiplicityObserverBoundary = record
  { irrepCanStrictlyRefineScalarFingerprint = true
  ; multiplicityCanStrictlyRefineIsotypicFingerprint = true
  ; factorizedScalarFamilyCannotRepairSpectralCollision = true
  ; representationLabelsAutomaticallyPhysicallyComplete = false
  ; allCommutantOperatorsAutomaticallyFactorThroughChosenSpectrum = false
  }
