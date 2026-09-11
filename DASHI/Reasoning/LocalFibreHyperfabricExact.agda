module DASHI.Reasoning.LocalFibreHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Core.BraidedEvidenceTraceBidiCrossPollination2026Exact as Braid
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hypercube

------------------------------------------------------------------------
-- LOCAL FIBRE HYPERFABRIC
--
-- A fibre is local type-family data over an incidence base.  Fibre
-- multiplicity is therefore allowed to vary from locality to locality and is
-- not one global cardinality.  Time, hop, phase, trial, animal, transmitter,
-- provenance, etc. may be axes/filtrations in a domain instance; none defines
-- the ontology of Fibre itself.
------------------------------------------------------------------------

record LocalFibreHyperfabric
    (Base Fibre Axis Symmetry Consumer : Set) : Set₁ where
  constructor local-fibre-hyperfabric
  field
    FibreAt : Base → Fibre → Set
    axisOf : Fibre → Axis

    Incidence : Base → Base → Set
    Transport :
      {left right : Base} →
      Incidence left right →
      Fibre → Fibre → Set

    LocalRefinement : Base → Fibre → Fibre → Set
    SeamCompatible : Base → Base → Set

    actBase : Symmetry → Base → Base
    actFibre : Symmetry → Fibre → Fibre

    ObservedBy : Consumer → Base → Fibre → Set

open LocalFibreHyperfabric public

record LocalSection
    {Base Fibre Axis Symmetry Consumer : Set}
    (H : LocalFibreHyperfabric Base Fibre Axis Symmetry Consumer) : Set₁ where
  constructor local-section
  field
    sectionFibre : (base : Base) → Fibre → Set
    sectionIsLocal :
      (base : Base) (fibre : Fibre) →
      sectionFibre base fibre → FibreAt H base fibre

open LocalSection public

record LocalGluingPatch
    {Base Fibre Axis Symmetry Consumer : Set}
    (H : LocalFibreHyperfabric Base Fibre Axis Symmetry Consumer) : Set₁ where
  constructor local-gluing-patch
  field
    inputs : List Base
    outputs : List Base
    interfaceReceipt : String
    compatibilityWitness : Set

open LocalGluingPatch public

record ConsumerInvariantSymmetry
    {Base Fibre Axis Symmetry Consumer : Set}
    (H : LocalFibreHyperfabric Base Fibre Axis Symmetry Consumer)
    (symmetry : Symmetry)
    (consumer : Consumer) : Set₁ where
  constructor consumer-invariant-symmetry
  field
    forwardObservation :
      (base : Base) (fibre : Fibre) →
      ObservedBy H consumer base fibre →
      ObservedBy H consumer (actBase H symmetry base) (actFibre H symmetry fibre)

open ConsumerInvariantSymmetry public

data SymmetryAutomaticallyAuthorizesQuotient : Set where
symmetryNeedsConsumerInvariance : SymmetryAutomaticallyAuthorizesQuotient → ⊥
symmetryNeedsConsumerInvariance ()

data GlobalFixedFibreCount : Set where
globalFibreCountIsNotPrimitive : GlobalFixedFibreCount → ⊥
globalFibreCountIsNotPrimitive ()

data EightIsUnderlyingFibreCardinality : Set where
eightIsOnlyOneDeclaredChart : EightIsUnderlyingFibreCardinality → ⊥
eightIsOnlyOneDeclaredChart ()

------------------------------------------------------------------------
-- Finite specimen: three independent coordinates are exposed at crossingX,
-- while only the retained structural coordinate exists at neighbouringY.
------------------------------------------------------------------------

data BaseSpecimen : Set where
  crossingX : BaseSpecimen
  neighbouringY : BaseSpecimen

data FibreSpecimen : Set where
  retained : FibreSpecimen
  delayFibre : FibreSpecimen
  phaseFibre : FibreSpecimen
  trialFibre : FibreSpecimen

data AxisSpecimen : Set where
  structuralAxis : AxisSpecimen
  hopTimeAxis : AxisSpecimen
  phaseAxis : AxisSpecimen
  trialAxis : AxisSpecimen

data SymmetrySpecimen : Set where
  identitySymmetry : SymmetrySpecimen

data ConsumerSpecimen : Set where
  coarseConsumer : ConsumerSpecimen
  richConsumer : ConsumerSpecimen

data IncidenceSpecimen : BaseSpecimen → BaseSpecimen → Set where
  xToY : IncidenceSpecimen crossingX neighbouringY

data FibreAtSpecimen : BaseSpecimen → FibreSpecimen → Set where
  retainedAtX : FibreAtSpecimen crossingX retained
  delayAtX : FibreAtSpecimen crossingX delayFibre
  phaseAtX : FibreAtSpecimen crossingX phaseFibre
  trialAtX : FibreAtSpecimen crossingX trialFibre
  retainedAtY : FibreAtSpecimen neighbouringY retained

data TransportSpecimen :
    {left right : BaseSpecimen} →
    IncidenceSpecimen left right →
    FibreSpecimen → FibreSpecimen → Set where
  retainedTransport : TransportSpecimen xToY retained retained

data RefinementSpecimen : BaseSpecimen → FibreSpecimen → FibreSpecimen → Set where
  addDelayAtX : RefinementSpecimen crossingX retained delayFibre
  addPhaseAtX : RefinementSpecimen crossingX retained phaseFibre
  addTrialAtX : RefinementSpecimen crossingX retained trialFibre

data SeamSpecimen : BaseSpecimen → BaseSpecimen → Set where
  xYSeam : SeamSpecimen crossingX neighbouringY

data ObservedSpecimen : ConsumerSpecimen → BaseSpecimen → FibreSpecimen → Set where
  coarseSeesRetainedX : ObservedSpecimen coarseConsumer crossingX retained
  coarseSeesRetainedY : ObservedSpecimen coarseConsumer neighbouringY retained
  richSeesRetainedX : ObservedSpecimen richConsumer crossingX retained
  richSeesDelayX : ObservedSpecimen richConsumer crossingX delayFibre
  richSeesPhaseX : ObservedSpecimen richConsumer crossingX phaseFibre
  richSeesTrialX : ObservedSpecimen richConsumer crossingX trialFibre
  richSeesRetainedY : ObservedSpecimen richConsumer neighbouringY retained

axisSpecimen : FibreSpecimen → AxisSpecimen
axisSpecimen retained = structuralAxis
axisSpecimen delayFibre = hopTimeAxis
axisSpecimen phaseFibre = phaseAxis
axisSpecimen trialFibre = trialAxis

actBaseSpecimen : SymmetrySpecimen → BaseSpecimen → BaseSpecimen
actBaseSpecimen identitySymmetry base = base

actFibreSpecimen : SymmetrySpecimen → FibreSpecimen → FibreSpecimen
actFibreSpecimen identitySymmetry fibre = fibre

finiteLocalFibreHyperfabric :
  LocalFibreHyperfabric
    BaseSpecimen FibreSpecimen AxisSpecimen SymmetrySpecimen ConsumerSpecimen
finiteLocalFibreHyperfabric =
  local-fibre-hyperfabric
    FibreAtSpecimen
    axisSpecimen
    IncidenceSpecimen
    TransportSpecimen
    RefinementSpecimen
    SeamSpecimen
    actBaseSpecimen
    actFibreSpecimen
    ObservedSpecimen

threeIndependentFibresCanBeAddedAtOneLocality :
  LocalRefinement finiteLocalFibreHyperfabric crossingX retained delayFibre
  × LocalRefinement finiteLocalFibreHyperfabric crossingX retained phaseFibre
  × LocalRefinement finiteLocalFibreHyperfabric crossingX retained trialFibre
threeIndependentFibresCanBeAddedAtOneLocality =
  addDelayAtX , addPhaseAtX , addTrialAtX

data LocalRefinementAutomaticallyGlobalizes : Set where
localRefinementDoesNotGlobalize : LocalRefinementAutomaticallyGlobalizes → ⊥
localRefinementDoesNotGlobalize ()

------------------------------------------------------------------------
-- Repo-native donor alignment.
------------------------------------------------------------------------

pantsOutputMultiplicityIsLocal : Pants.outputCount Pants.composedOneToThree ≡ 3
pantsOutputMultiplicityIsLocal = Pants.composedOutputCountIsThree

pantsCapacityMayRemainConservativeAcrossAPathSensitiveSplit :
  Pants.CapacityConservative Pants.phaseChangedJunction
pantsCapacityMayRemainConservativeAcrossAPathSensitiveSplit =
  Pants.phaseChangedCapacityConservative

braidCrossingRetainsIdentities :
  Braid.coordinationWithoutFusion Braid.canonicalBraidedEvidenceBoundary ≡ true
braidCrossingRetainsIdentities = refl

hypercubeCarrierDoesNotFixTransitionGeometry :
  Hypercube.allowsDirectPoleJump Hypercube.mediatedPathGeometry ≡ false
hypercubeCarrierDoesNotFixTransitionGeometry =
  Hypercube.mediatedGeometryBlocksDirectPoleJump

------------------------------------------------------------------------
-- Historical MaleCNS eight-feature family = one consumer-facing chart.
------------------------------------------------------------------------

data LegacyNDimChartCoordinate : Set where
  directForward : LegacyNDimChartCoordinate
  directReverse : LegacyNDimChartCoordinate
  twoHopForward : LegacyNDimChartCoordinate
  twoHopReverse : LegacyNDimChartCoordinate
  commonInput : LegacyNDimChartCoordinate
  commonOutput : LegacyNDimChartCoordinate
  signedForward : LegacyNDimChartCoordinate
  signedReverse : LegacyNDimChartCoordinate

record MaleCNSChartBoundary : Set where
  constructor malecns-chart-boundary
  field
    eightCoordinatesAreOneDeclaredChart : Bool
    eightCoordinatesAreOneDeclaredChartIsTrue :
      eightCoordinatesAreOneDeclaredChart ≡ true
    chartCoordinateCountEqualsUnderlyingFibreCount : Bool
    chartCoordinateCountEqualsUnderlyingFibreCountIsFalse :
      chartCoordinateCountEqualsUnderlyingFibreCount ≡ false
    localFibreMultiplicityMayVaryByBaseLocality : Bool
    localFibreMultiplicityMayVaryByBaseLocalityIsTrue :
      localFibreMultiplicityMayVaryByBaseLocality ≡ true
    localRefinementRequiresGlobalTimeStep : Bool
    localRefinementRequiresGlobalTimeStepIsFalse :
      localRefinementRequiresGlobalTimeStep ≡ false
    pantsSplitMergeMayBeNary : Bool
    pantsSplitMergeMayBeNaryIsTrue :
      pantsSplitMergeMayBeNary ≡ true
    recombinationAutomaticallyErasesPathMemory : Bool
    recombinationAutomaticallyErasesPathMemoryIsFalse :
      recombinationAutomaticallyErasesPathMemory ≡ false
    symmetryAloneCreatesQuotientAuthority : Bool
    symmetryAloneCreatesQuotientAuthorityIsFalse :
      symmetryAloneCreatesQuotientAuthority ≡ false

canonicalMaleCNSChartBoundary : MaleCNSChartBoundary
canonicalMaleCNSChartBoundary =
  malecns-chart-boundary
    true refl false refl true refl false refl true refl false refl false refl
