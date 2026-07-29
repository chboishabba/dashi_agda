module DASHI.Physics.YangMills.BalabanClayGate4TypedReuseAndFiniteGeometryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (Dec; yes; no)

import DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion as ExistingRG
import DASHI.Physics.YangMills.BalabanClayP2BadComponentGeometryExact as ExistingGeometry

------------------------------------------------------------------------
-- Typed reuse of the existing small-field RG owner.
--
-- This replaces string references in the archaeology table by projections from
-- an actual OneStepRGCutset inhabitant.  No new small-field authority is
-- introduced here.
------------------------------------------------------------------------

record ExistingSmallFieldToCombinedRGAdapter
    (Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density : Set) : Set₁ where
  field
    rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density

open ExistingSmallFieldToCombinedRGAdapter public

smallFieldCoordinatesExist :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (adapter : ExistingSmallFieldToCombinedRGAdapter Configuration Background
      Fluctuation GaugeOrbit Polymer Region Coupling Bound Density) {U} →
  ExistingRG.SmallFieldConfiguration (rg adapter) U →
  ExistingRG.Σ Background (λ Ubg →
    ExistingRG.Σ Fluctuation (λ Z →
      ExistingRG.SmallFieldCoordinates (rg adapter) Ubg Z
      ExistingRG.×
      U ≡ ExistingRG.multiplyConfiguration (rg adapter) Ubg
        (ExistingRG.exp (rg adapter) Z)))
smallFieldCoordinatesExist adapter = ExistingRG.fluctuationCoordinatesExist (rg adapter)

smallFieldLocalization :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (adapter : ExistingSmallFieldToCombinedRGAdapter Configuration Background
      Fluctuation GaugeOrbit Polymer Region Coupling Bound Density) →
  ExistingRG.PolymerLocalizationStable (rg adapter)
smallFieldLocalization adapter = ExistingRG.polymerLocalizationStable (rg adapter)

smallFieldSupportPreservation :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (adapter : ExistingSmallFieldToCombinedRGAdapter Configuration Background
      Fluctuation GaugeOrbit Polymer Region Coupling Bound Density) →
  ExistingRG.LocalizationPreservesSupport (rg adapter)
smallFieldSupportPreservation adapter =
  ExistingRG.localizationPreservesSupport (rg adapter)

smallFieldExponentialWeightPreservation :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (adapter : ExistingSmallFieldToCombinedRGAdapter Configuration Background
      Fluctuation GaugeOrbit Polymer Region Coupling Bound Density) →
  ExistingRG.LocalizationPreservesExponentialWeight (rg adapter)
smallFieldExponentialWeightPreservation adapter =
  ExistingRG.localizationPreservesExponentialWeight (rg adapter)

smallFieldWardPreservation :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (adapter : ExistingSmallFieldToCombinedRGAdapter Configuration Background
      Fluctuation GaugeOrbit Polymer Region Coupling Bound Density) →
  ExistingRG.LocalizationPreservesWardIdentity (rg adapter)
smallFieldWardPreservation adapter =
  ExistingRG.localizationPreservesWardIdentity (rg adapter)

smallFieldCouplingFlow :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (adapter : ExistingSmallFieldToCombinedRGAdapter Configuration Background
      Fluctuation GaugeOrbit Polymer Region Coupling Bound Density) →
  ExistingRG.CouplingRenormalization (rg adapter)
smallFieldCouplingFlow adapter = ExistingRG.couplingRenormalization (rg adapter)

smallFieldPolymerContraction :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (adapter : ExistingSmallFieldToCombinedRGAdapter Configuration Background
      Fluctuation GaugeOrbit Polymer Region Coupling Bound Density) →
  ExistingRG.LessEqual (rg adapter)
    (ExistingRG.polymerNorm (rg adapter) (ExistingRG.E-next (rg adapter)))
    (ExistingRG.addBound (rg adapter)
      (ExistingRG.multiplyBound (rg adapter)
        (ExistingRG.lambdaPolymer (rg adapter))
        (ExistingRG.polymerNorm (rg adapter) (ExistingRG.E (rg adapter))))
      (ExistingRG.perturbativeError (rg adapter)))
smallFieldPolymerContraction adapter = ExistingRG.oneStepPolymerContraction (rg adapter)

------------------------------------------------------------------------
-- Existing finite bad-component geometry as the large-field region carrier.
------------------------------------------------------------------------

record ExistingBadComponentLargeFieldCarrier
    (Configuration Gauge Block : Set) : Set₁ where
  field
    geometry : ExistingGeometry.BadBlockGeometry Configuration Gauge Block
    configuration : Configuration

open ExistingBadComponentLargeFieldCarrier public

LargeFieldRegion :
  ∀ {Configuration Gauge Block} →
  ExistingBadComponentLargeFieldCarrier Configuration Gauge Block → Set
LargeFieldRegion carrier =
  ExistingGeometry.BadComponent (geometry carrier) (configuration carrier)

RegionContains :
  ∀ {Configuration Gauge Block}
    (carrier : ExistingBadComponentLargeFieldCarrier Configuration Gauge Block) →
  LargeFieldRegion carrier → Block → Set
RegionContains carrier = ExistingGeometry.Contains

regionPairwiseConnected :
  ∀ {Configuration Gauge Block}
    (carrier : ExistingBadComponentLargeFieldCarrier Configuration Gauge Block)
    (region : LargeFieldRegion carrier) →
  ExistingGeometry.PairwiseConnected region
regionPairwiseConnected carrier = ExistingGeometry.componentConnected

largeFieldBlockDecidable :
  ∀ {Configuration Gauge Block}
    (carrier : ExistingBadComponentLargeFieldCarrier Configuration Gauge Block)
    block →
  Dec (ExistingGeometry.BadBlock (geometry carrier) (configuration carrier) block)
largeFieldBlockDecidable carrier =
  ExistingGeometry.badBlockMeasurable (geometry carrier) (configuration carrier)

------------------------------------------------------------------------
-- Exact first-/second-class support split.
------------------------------------------------------------------------

data LocalizedClass : Set where
  firstClass secondClass : LocalizedClass

record SupportLargeFieldIntersection (Term Region : Set) : Set₁ where
  field
    Intersects : Term → Region → Set
    intersectsDecidable : ∀ term region → Dec (Intersects term region)

open SupportLargeFieldIntersection public

classifyLocalizedTerm :
  ∀ {Term Region} →
  SupportLargeFieldIntersection Term Region → Term → Region → LocalizedClass
classifyLocalizedTerm dataSet term region with intersectsDecidable dataSet term region
... | yes _ = secondClass
... | no _ = firstClass

data ClassifiedLocalizedTerm {Term Region : Set}
    (dataSet : SupportLargeFieldIntersection Term Region)
    (term : Term) (region : Region) : LocalizedClass → Set where
  classifiedFirst :
    (doesNotIntersect : Intersects dataSet term region → ⊥) →
    ClassifiedLocalizedTerm dataSet term region firstClass
  classifiedSecond :
    Intersects dataSet term region →
    ClassifiedLocalizedTerm dataSet term region secondClass

-- Explicit empty proposition used by the negative branch of Dec.
data ⊥ : Set where

classifyLocalizedTermExact :
  ∀ {Term Region}
    (dataSet : SupportLargeFieldIntersection Term Region)
    (term : Term) (region : Region) →
  ClassifiedLocalizedTerm dataSet term region
    (classifyLocalizedTerm dataSet term region)
classifyLocalizedTermExact dataSet term region
  with intersectsDecidable dataSet term region
... | yes intersects = classifiedSecond intersects
... | no doesNotIntersect = classifiedFirst doesNotIntersect

------------------------------------------------------------------------
-- Boundary-term reinjection as exact list bookkeeping.
------------------------------------------------------------------------

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ right = right
(left ∷ rest) ++ right = left ∷ (rest ++ right)

record BoundaryTermCarrier (Term : Set) : Set₁ where
  field
    IsBoundary : Term → Set
    boundaryDecidable : ∀ term → Dec (IsBoundary term)

open BoundaryTermCarrier public

collectBoundaryTerms :
  ∀ {Term} → BoundaryTermCarrier Term → List Term → List Term
collectBoundaryTerms carrier [] = []
collectBoundaryTerms carrier (term ∷ rest)
  with boundaryDecidable carrier term
... | yes _ = term ∷ collectBoundaryTerms carrier rest
... | no _ = collectBoundaryTerms carrier rest

reinjectBoundaryTerms :
  ∀ {Term} → List Term → List Term → List Term
reinjectBoundaryTerms boundaryTerms nextDensity = boundaryTerms ++ nextDensity

reinjectNoBoundaryIsIdentity :
  ∀ {Term} (nextDensity : List Term) →
  reinjectBoundaryTerms [] nextDensity ≡ nextDensity
reinjectNoBoundaryIsIdentity nextDensity = refl

------------------------------------------------------------------------
-- Status split.
------------------------------------------------------------------------

typedExistingSmallFieldReuseLevel : ProofLevel
typedExistingSmallFieldReuseLevel = machineChecked

existingBadComponentLargeFieldReuseLevel : ProofLevel
existingBadComponentLargeFieldReuseLevel = machineChecked

finiteFirstSecondClassSplitLevel : ProofLevel
finiteFirstSecondClassSplitLevel = machineChecked

boundaryTermListReinjectionLevel : ProofLevel
boundaryTermListReinjectionLevel = machineChecked

largeFieldEnlargementAndCollarInputsLevel : ProofLevel
largeFieldEnlargementAndCollarInputsLevel = conditional
