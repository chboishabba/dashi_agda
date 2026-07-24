module DASHI.Physics.YangMills.BalabanPhysicalHaloOriginExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (weakenIndex)
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact

------------------------------------------------------------------------
-- Literal translated halo origins.
--
-- A relative offset is converted to an actual torus origin by repeatedly
-- applying the cyclic predecessor in each coordinate.  The containing-origin
-- carrier stores both the physical origin and its offset witness.  This gives
-- definitional round trips and transfers the exact W^4 offset count to a list
-- of concrete origin sites without relying on cardinality alone.
------------------------------------------------------------------------

lastCyclicIndex : ∀ n → CyclicIndex (suc n)
lastCyclicIndex zero = zeroᵢ
lastCyclicIndex (suc n) = sucᵢ (lastCyclicIndex n)

cyclicPredecessor : ∀ {n} → CyclicIndex n → CyclicIndex n
cyclicPredecessor {zero} ()
cyclicPredecessor {suc n} zeroᵢ = lastCyclicIndex n
cyclicPredecessor {suc n} (sucᵢ index) = weakenIndex index

shiftBackByOffset :
  ∀ {width latticeSide} →
  CyclicIndex width → CyclicIndex latticeSide → CyclicIndex latticeSide
shiftBackByOffset zeroᵢ site = site
shiftBackByOffset (sucᵢ offset) site =
  cyclicPredecessor (shiftBackByOffset offset site)

shiftBackPair :
  ∀ {width latticeSide} →
  Pair2 (CyclicIndex width) →
  Pair2 (CyclicIndex latticeSide) →
  Pair2 (CyclicIndex latticeSide)
shiftBackPair (pair offset0 offset1) (pair site0 site1) =
  pair
    (shiftBackByOffset offset0 site0)
    (shiftBackByOffset offset1 site1)

shiftBackFourfold :
  ∀ {width latticeSide} →
  Fourfold (CyclicIndex width) →
  Fourfold (CyclicIndex latticeSide) →
  Fourfold (CyclicIndex latticeSide)
shiftBackFourfold (pair offset01 offset23) (pair site01 site23) =
  pair
    (shiftBackPair offset01 site01)
    (shiftBackPair offset23 site23)

record PhysicalHaloGeometry (latticeSide : Nat) : Set where
  constructor physicalHaloGeometry
  field
    cover : RegularTranslatedHaloCover

open PhysicalHaloGeometry public

record PhysicalContainingOrigin
    {latticeSide : Nat}
    (geometry : PhysicalHaloGeometry latticeSide)
    (site : periodicTorus4Definition latticeSide) : Set where
  constructor physicalContainingOrigin
  field
    relativeOffset : localContainingHaloOffsets (cover geometry)
    originSite : periodicTorus4Definition latticeSide
    originSiteDefinition :
      originSite ≡ shiftBackFourfold relativeOffset site

open PhysicalContainingOrigin public

originFromPhysicalOffset :
  ∀ {latticeSide}
    (geometry : PhysicalHaloGeometry latticeSide)
    (site : periodicTorus4Definition latticeSide) →
  localContainingHaloOffsets (cover geometry) →
  PhysicalContainingOrigin geometry site
originFromPhysicalOffset geometry site offset =
  physicalContainingOrigin offset (shiftBackFourfold offset site) refl

offsetFromPhysicalOrigin :
  ∀ {latticeSide}
    {geometry : PhysicalHaloGeometry latticeSide}
    {site : periodicTorus4Definition latticeSide} →
  PhysicalContainingOrigin geometry site →
  localContainingHaloOffsets (cover geometry)
offsetFromPhysicalOrigin = relativeOffset

physicalOffsetAfterOrigin :
  ∀ {latticeSide}
    (geometry : PhysicalHaloGeometry latticeSide)
    (site : periodicTorus4Definition latticeSide)
    offset →
  offsetFromPhysicalOrigin (originFromPhysicalOffset geometry site offset)
  ≡ offset
physicalOffsetAfterOrigin geometry site offset = refl

physicalOriginAfterOffset :
  ∀ {latticeSide}
    (geometry : PhysicalHaloGeometry latticeSide)
    (site : periodicTorus4Definition latticeSide)
    origin →
  originFromPhysicalOffset geometry site (offsetFromPhysicalOrigin origin)
  ≡ origin
physicalOriginAfterOffset geometry site
  (physicalContainingOrigin offset .(shiftBackFourfold offset site) refl) = refl

physicalHaloOriginRoundTrips :
  ∀ {latticeSide} (geometry : PhysicalHaloGeometry latticeSide) →
  HaloOriginOffsetRoundTrips
    (cover geometry)
    (periodicTorus4Definition latticeSide)
physicalHaloOriginRoundTrips geometry = record
  { ContainingOrigin = PhysicalContainingOrigin geometry
  ; originFromOffset = originFromPhysicalOffset geometry
  ; offsetFromOrigin = λ site → offsetFromPhysicalOrigin
  ; offsetAfterOrigin = physicalOffsetAfterOrigin geometry
  ; originAfterOffset = physicalOriginAfterOffset geometry
  }

literalPhysicalContainingOrigins :
  ∀ {latticeSide}
    (geometry : PhysicalHaloGeometry latticeSide)
    (site : periodicTorus4Definition latticeSide) →
  Agda.Builtin.List.List (PhysicalContainingOrigin geometry site)
literalPhysicalContainingOrigins geometry site =
  physicalContainingOriginEnumeration
    (physicalHaloOriginRoundTrips geometry) site

literalPhysicalContainingOriginCount :
  ∀ {latticeSide}
    (geometry : PhysicalHaloGeometry latticeSide)
    (site : periodicTorus4Definition latticeSide) →
  Data.List.Base.length (literalPhysicalContainingOrigins geometry site)
  ≡ literalHaloOverlapCount (cover geometry)
literalPhysicalContainingOriginCount geometry site =
  physicalContainingOriginEnumerationLength
    (physicalHaloOriginRoundTrips geometry) site

cyclicPredecessorDefinitionLevel : ProofLevel
cyclicPredecessorDefinitionLevel = machineChecked

physicalHaloOriginConstructionLevel : ProofLevel
physicalHaloOriginConstructionLevel = machineChecked

physicalBlockOriginOffsetBijectionLevel : ProofLevel
physicalBlockOriginOffsetBijectionLevel = machineChecked

physicalContainingOriginCountLevel : ProofLevel
physicalContainingOriginCountLevel = machineChecked

physicalOriginMatchesWilsonBlockContainmentLevel : ProofLevel
physicalOriginMatchesWilsonBlockContainmentLevel = conditional
