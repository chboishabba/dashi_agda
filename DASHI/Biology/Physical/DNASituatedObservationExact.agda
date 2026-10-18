module DASHI.Biology.Physical.DNASituatedObservationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Biology.DNAChemistryCarrier as DNA
import DASHI.Biology.Physical.BDNACalibratedHelicalGeometryExact as B
import DASHI.Biology.Physical.DNASituatedObservationSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- SITUATED DNA OBSERVATION
--
-- This owner supplies the DNA-side contrast requested by the cross-domain
-- backprop roadmap.  The finite DNA base -> UV chart is a genuine exact
-- bijection on the four-base carrier.  Structural/helical observations are
-- instead situated by sequence context, environment, coordinate convention,
-- method and source manifestation.
--
-- The non-factorability witnesses below are DASHI synthesis.  Olson/Lavery/
-- Pasi retain ownership only of the source-bounded coordinate/conformation
-- premises recorded in DNASituatedObservationSourceAtlasExact.
------------------------------------------------------------------------

data DNAGeometryObservable : Set where
  uvBaseIdentityObservable : DNAGeometryObservable
  basePairStepSixObservable : DNAGeometryObservable
  helicalFrameObservable : DNAGeometryObservable
  se3StepObservable : DNAGeometryObservable

data CoordinateConvention : Set where
  dashiUVConvention : CoordinateConvention
  olsonStandardFrameConvention : CoordinateConvention
  repositoryAlternativeConvention : CoordinateConvention

data ObservationMethod : Set where
  exactFiniteAlgebra : ObservationMethod
  molecularDynamicsObservation : ObservationMethod
  structuralReferenceCalibration : ObservationMethod
  geometricComposition : ObservationMethod

data DNAProvenanceRole : Set where
  dashiAlgebraicConstruction : DNAProvenanceRole
  literatureGeometryObservation : DNAProvenanceRole

data SequenceContextRole : Set where
  centralStepOnly : SequenceContextRole
  nearestNeighbourContext : SequenceContextRole
  tetranucleotideContext : SequenceContextRole

record DNASituatedObservation : Set where
  constructor dna-situated-observation
  field
    leftBase : DNA.DNABase
    rightBase : DNA.DNABase
    sequenceContextRole : SequenceContextRole
    flankingContext : String
    environment : B.HelixEnvironment
    observable : DNAGeometryObservable
    coordinateConvention : CoordinateConvention
    method : ObservationMethod
    provenanceRole : DNAProvenanceRole
    sourceIdentity : String
    sourceLocator : String
    paymentReading : String
open DNASituatedObservation public

referenceCGStepObservation : DNASituatedObservation
referenceCGStepObservation = dna-situated-observation
  DNA.C DNA.G
  centralStepOnly
  "central CpG step; no flanking context promoted by this reference fixture"
  (B.helixEnvironment B.physiologicalLike B.referenceTemperature)
  basePairStepSixObservable
  olsonStandardFrameConvention
  structuralReferenceCalibration
  literatureGeometryObservation
  "Olson et al. 2001 DOI 10.1006/jmbi.2001.4987 / PMID 11601858"
  "standard-reference-frame source role plus repository ideal-B calibration interface"
  "coordinate convention is retained; ideal B values are not universal sequence/environment truth"

pasiTetranucleotideObservation : DNASituatedObservation
pasiTetranucleotideObservation = dna-situated-observation
  DNA.C DNA.G
  tetranucleotideContext
  "central step embedded in source-defined tetranucleotide context"
  (B.helixEnvironment B.physiologicalLike B.referenceTemperature)
  basePairStepSixObservable
  olsonStandardFrameConvention
  molecularDynamicsObservation
  literatureGeometryObservation
  "Pasi et al. 2014 DOI 10.1093/nar/gku855 / PMID 25260586 / PMCID PMC4231739"
  "source study over all 136 distinct tetranucleotide sequences"
  "helical parameters/fluctuations remain context- and method-bounded; no complete DNA-state claim"

------------------------------------------------------------------------
-- Positive exact coordinate theorem: unlike the situated geometry projections,
-- the UV chart is literally invertible on DNABase.
------------------------------------------------------------------------

uvRoundTrip : (base : DNA.DNABase) → DNA.fromUV (DNA.toUV base) ≡ base
uvRoundTrip = DNA.fromUV-toUV

uvCoordinateRoundTrip :
  (coordinate : DNA.UVCoordinate) →
  DNA.toUV (DNA.fromUV coordinate) ≡ coordinate
uvCoordinateRoundTrip = DNA.toUV-fromUV

------------------------------------------------------------------------
-- Finite context collision: the same central dinucleotide does not recover the
-- flanking-context coordinate needed by the context-sensitive geometry studies.
------------------------------------------------------------------------

data DNAContextWorld : Set where
  cgATFlankedWorld : DNAContextWorld
  cgGCFlankedWorld : DNAContextWorld

data CentralStepIdentity : Set where
  cgCentralStep : CentralStepIdentity

data FlankingContextIdentity : Set where
  atFlankingContext : FlankingContextIdentity
  gcFlankingContext : FlankingContextIdentity

centralStepProjection : DNAContextWorld → CentralStepIdentity
centralStepProjection cgATFlankedWorld = cgCentralStep
centralStepProjection cgGCFlankedWorld = cgCentralStep

flankingContextProjection : DNAContextWorld → FlankingContextIdentity
flankingContextProjection cgATFlankedWorld = atFlankingContext
flankingContextProjection cgGCFlankedWorld = gcFlankingContext

centralStepCannotRecoverFlankingContext :
  INF.FactorsThrough centralStepProjection flankingContextProjection → ⊥
centralStepCannotRecoverFlankingContext =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      cgATFlankedWorld
      cgGCFlankedWorld
      refl
      (λ ()))

------------------------------------------------------------------------
-- Measurement-identity collision: a shared parameter label is not enough to
-- identify the coordinate convention that gives the value its meaning.  The
-- alternative convention world is a repository-local information witness, not
-- a claim about a particular external software package.
------------------------------------------------------------------------

data DNAParameterWorld : Set where
  standardFrameTwistWorld : DNAParameterWorld
  alternativeConventionTwistWorld : DNAParameterWorld

data CoarseParameterName : Set where
  twistParameterName : CoarseParameterName

data ParameterDefinitionIdentity : Set where
  olsonTwistDefinition : ParameterDefinitionIdentity
  alternativeTwistDefinition : ParameterDefinitionIdentity

parameterNameProjection : DNAParameterWorld → CoarseParameterName
parameterNameProjection _ = twistParameterName

parameterDefinitionProjection : DNAParameterWorld → ParameterDefinitionIdentity
parameterDefinitionProjection standardFrameTwistWorld = olsonTwistDefinition
parameterDefinitionProjection alternativeConventionTwistWorld = alternativeTwistDefinition

parameterNameCannotRecoverMeasurementDefinition :
  INF.FactorsThrough parameterNameProjection parameterDefinitionProjection → ⊥
parameterNameCannotRecoverMeasurementDefinition =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      standardFrameTwistWorld
      alternativeConventionTwistWorld
      refl
      (λ ()))

------------------------------------------------------------------------
-- Reuse the existing B-DNA authority boundary rather than creating another
-- geometry ontology.
------------------------------------------------------------------------

bDNAAuthorityBoundary : B.BDNAAuthorityBoundary
bDNAAuthorityBoundary = B.canonicalBDNAAuthorityBoundary

------------------------------------------------------------------------
-- WrongType / exactness firewalls.
------------------------------------------------------------------------

data UVBijectionCreatesCompleteDNAState : Set where
data SameDinucleotideCreatesSameStepGeometry : Set where
data SameParameterNameCreatesSameMeasurementObject : Set where
data SimulationGeometryCreatesUniversalExperimentalGeometry : Set where

uvBijectionDoesNotCreateCompleteDNAState : UVBijectionCreatesCompleteDNAState → ⊥
uvBijectionDoesNotCreateCompleteDNAState ()

sameDinucleotideDoesNotCreateSameStepGeometry : SameDinucleotideCreatesSameStepGeometry → ⊥
sameDinucleotideDoesNotCreateSameStepGeometry ()

sameParameterNameDoesNotCreateSameMeasurementObject :
  SameParameterNameCreatesSameMeasurementObject → ⊥
sameParameterNameDoesNotCreateSameMeasurementObject ()

simulationGeometryDoesNotCreateUniversalExperimentalGeometry :
  SimulationGeometryCreatesUniversalExperimentalGeometry → ⊥
simulationGeometryDoesNotCreateUniversalExperimentalGeometry ()

record DNASituatedObservationBoundary : Set where
  constructor dna-situated-observation-boundary
  field
    uvChartExactWherePaid : Bool
    uvChartHasExplicitInverse : Bool
    centralStepInsufficientForContext : Bool
    parameterNameInsufficientForMeasurementIdentity : Bool
    sequenceContextRetained : Bool
    environmentRetained : Bool
    coordinateConventionRetained : Bool
    sourceManifestationRetained : Bool
    bDNAAuthorityBoundaryReused : Bool
    uvChartCreatesCompleteDNAState : Bool
    sameDinucleotideCreatesSameStepGeometry : Bool
    simulationCreatesUniversalExperimentalGeometry : Bool
open DNASituatedObservationBoundary public

canonicalDNASituatedObservationBoundary : DNASituatedObservationBoundary
canonicalDNASituatedObservationBoundary =
  dna-situated-observation-boundary
    true true true true true true true true true
    false false false
