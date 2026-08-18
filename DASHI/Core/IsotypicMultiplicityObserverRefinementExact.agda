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
-- Two states can agree on every scalar observable which factors through a
-- chosen joint spectral fingerprint while differing either in irreducible
-- symmetry type or inside a multiplicity copy of the SAME type.
--
-- This extracts that theorem generically into the existing observer lattice.
-- Representation labels are not promoted to physical truth, and factorization
-- through the selected spectral fingerprint is always an explicit premise.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.ObserverRefinementLatticeExact as Observer

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
isotypicObserver system = Observer.pairObserver (spectral system) (irrep system)

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
  cong₂ _,_
    (cong proj₁ equality)
    (cong (λ value → proj₁ (proj₂ value)) equality)

multiplicityRefinesSpectral :
  ∀ {State Spectral Irrep Multiplicity}
    (system : RepresentationObserverSystem State Spectral Irrep Multiplicity) →
  Observer.Refines (spectral system) (multiplicityObserver system)
multiplicityRefinesSpectral system x y equality = cong proj₁ equality

record IsotypicCollision
    {State Spectral Irrep Multiplicity : Set}
    (system : RepresentationObserverSystem State Spectral Irrep Multiplicity) : Set where
  field
    isoLeft isoRight : State
    isoSameSpectral : spectral system isoLeft ≡ spectral system isoRight
    differentIrrep : irrep system isoLeft ≡ irrep system isoRight → ⊥

open IsotypicCollision public

isotypicCollisionGivesStrictRefinement :
  ∀ {State Spectral Irrep Multiplicity}
    {system : RepresentationObserverSystem State Spectral Irrep Multiplicity} →
  IsotypicCollision system →
  Observer.StrictRefinement (spectral system) (isotypicObserver system)
isotypicCollisionGivesStrictRefinement {system = system} collision =
  Observer.strictPairRefinement
    (spectral system)
    (irrep system)
    (isoLeft collision)
    (isoRight collision)
    (isoSameSpectral collision)
    (differentIrrep collision)

record MultiplicityCollision
    {State Spectral Irrep Multiplicity : Set}
    (system : RepresentationObserverSystem State Spectral Irrep Multiplicity) : Set where
  field
    multLeft multRight : State
    multSameSpectral : spectral system multLeft ≡ spectral system multRight
    multSameIrrep : irrep system multLeft ≡ irrep system multRight
    differentMultiplicity :
      multiplicity system multLeft ≡ multiplicity system multRight → ⊥

open MultiplicityCollision public

multiplicityCollisionGivesStrictIsotypicRefinement :
  ∀ {State Spectral Irrep Multiplicity}
    {system : RepresentationObserverSystem State Spectral Irrep Multiplicity} →
  MultiplicityCollision system →
  Observer.StrictRefinement (isotypicObserver system) (multiplicityObserver system)
multiplicityCollisionGivesStrictIsotypicRefinement {system = system} collision =
  Observer.strictRefinement
    (multiplicityRefinesIsotypic system)
    (multLeft collision)
    (multRight collision)
    (cong₂ _,_ (multSameSpectral collision) (multSameIrrep collision))
    (λ equality →
      differentMultiplicity collision
        (cong (λ value → proj₂ (proj₂ value)) equality))

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
