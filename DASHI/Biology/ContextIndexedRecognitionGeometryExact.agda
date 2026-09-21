module DASHI.Biology.ContextIndexedRecognitionGeometryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.TargetIndexedRecognitionGeometryExact as Geometry
import DASHI.Biology.TargetIndexedRecognitionAdmissibleRegionExact as Region
import DASHI.Biology.Protein.ProteinConformationAttractor as Protein
import DASHI.Biology.IonicMimicryGeometryExact as Ionic

------------------------------------------------------------------------
-- CONTEXT-INDEXED RECOGNITION GEOMETRY
--
-- Recognition depends not only on the nominal target identity, but on target
-- state and environment:
--
--   receptor conformation
--   binding-site rigidity
--   membrane / solvent environment
--   protonation / ionic conditions
--   history / allosteric state
--
-- This owner proves the structural consequence: the same chemical-pair
-- mismatch can move from admitted to rejected when only target context
-- changes.
------------------------------------------------------------------------

data RecognitionContextKind : Set where
  proteinConformationContext : RecognitionContextKind
  bindingSiteRigidityContext : RecognitionContextKind
  solventMembraneContext : RecognitionContextKind
  ionicEnvironmentContext : RecognitionContextKind
  allostericHistoryContext : RecognitionContextKind

record RecognitionContext : Set where
  constructor recognitionContext
  field
    contextKind : RecognitionContextKind
    contextReference : String
    targetStateReference : String
    environmentReference : String

open RecognitionContext public

record ContextIndexedRecognitionTarget : Set where
  constructor contextIndexedRecognitionTarget
  field
    nominalTargetReference : String
    context : RecognitionContext
    geometry : Geometry.TargetRecognitionGeometry
    region : Region.TargetAdmissibleRegion

    targetIdentityPreservedAcrossContext : Bool
    targetIdentityPreservedAcrossContextIsTrue :
      targetIdentityPreservedAcrossContext ≡ true

open ContextIndexedRecognitionTarget public

------------------------------------------------------------------------
-- Finite exact fixture:
--
-- same nominal target + same pair mismatch
-- context 0 -> permissive coordination region
-- context 1 -> strict coordination region
------------------------------------------------------------------------

context0 : RecognitionContext
context0 =
  recognitionContext
    bindingSiteRigidityContext
    "fixture context 0"
    "same nominal target / permissive target state"
    "finite DASHI environment 0"

context1 : RecognitionContext
context1 =
  recognitionContext
    bindingSiteRigidityContext
    "fixture context 1"
    "same nominal target / strict target state"
    "finite DASHI environment 1"

targetInContext0 : ContextIndexedRecognitionTarget
targetInContext0 =
  contextIndexedRecognitionTarget
    "same nominal target"
    context0
    Geometry.targetA
    Region.permissiveRegion
    true refl

targetInContext1 : ContextIndexedRecognitionTarget
targetInContext1 =
  contextIndexedRecognitionTarget
    "same nominal target"
    context1
    Geometry.targetA
    Region.strictCoordinationRegion
    true refl

AdmittedInContext :
  ContextIndexedRecognitionTarget →
  Geometry.RecognitionMismatch →
  Set
AdmittedInContext target mismatch =
  Region.AdmittedByRegion (region target) mismatch

canonicalPairAdmittedInContext0 :
  AdmittedInContext targetInContext0 Geometry.canonicalPairMismatch
canonicalPairAdmittedInContext0 =
  Region.canonicalPairInsidePermissiveRegion

canonicalPairRejectedInContext1 :
  AdmittedInContext targetInContext1 Geometry.canonicalPairMismatch
  →
  ⊥
canonicalPairRejectedInContext1 =
  Region.canonicalPairOutsideStrictCoordinationRegion

record SameTargetDifferentContextWitness : Set where
  constructor sameTargetDifferentContextWitness
  field
    pair : Geometry.RecognitionMismatch
    firstTargetState : ContextIndexedRecognitionTarget
    secondTargetState : ContextIndexedRecognitionTarget

    sameNominalTargetReference : Bool
    sameNominalTargetReferenceIsTrue :
      sameNominalTargetReference ≡ true

    admittedFirst :
      AdmittedInContext firstTargetState pair

    rejectedSecond :
      AdmittedInContext secondTargetState pair → ⊥

open SameTargetDifferentContextWitness public

canonicalSameTargetDifferentContextWitness :
  SameTargetDifferentContextWitness
canonicalSameTargetDifferentContextWitness =
  sameTargetDifferentContextWitness
    Geometry.canonicalPairMismatch
    targetInContext0
    targetInContext1
    true refl
    canonicalPairAdmittedInContext0
    canonicalPairRejectedInContext1


------------------------------------------------------------------------
-- Typed protein-conformation adapter.
--
-- A concrete receptor model can now map each actual conformation in an
-- existing ProteinConformationSystem to its own recognition geometry/region.
-- This is the intended owner for future HTR2A state-specific calibration.
------------------------------------------------------------------------

record ConformationIndexedRecognitionSystem
    (P : Protein.ProteinConformationSystem) : Set₁ where
  open Protein.ProteinConformationSystem P
  field
    geometryAt :
      Conformation →
      Geometry.TargetRecognitionGeometry

    regionAt :
      Conformation →
      Region.TargetAdmissibleRegion

    geometryTargetMatchesRegion :
      (state : Conformation) →
      Geometry.targetReference (geometryAt state)
      ≡
      Geometry.targetReference
        (Region.geometry (regionAt state))

    conformationIndexIsExplicit : Bool
    conformationIndexIsExplicitIsTrue :
      conformationIndexIsExplicit ≡ true

    conformationDoesNotDetermineAffinityByDefinition : Bool
    conformationDoesNotDetermineAffinityByDefinitionIsFalse :
      conformationDoesNotDetermineAffinityByDefinition ≡ false

open ConformationIndexedRecognitionSystem public

record ConformationIndexedRecognitionObservation
    {P : Protein.ProteinConformationSystem}
    (system : ConformationIndexedRecognitionSystem P) : Set₁ where
  open Protein.ProteinConformationSystem P
  field
    conformation : Conformation
    mismatch : Geometry.RecognitionMismatch

    admitted :
      Region.AdmittedByRegion
        (ConformationIndexedRecognitionSystem.regionAt system conformation)
        mismatch

    observationReference : String

open ConformationIndexedRecognitionObservation public

------------------------------------------------------------------------
-- Existing protein-conformation owner is the intended non-toy state carrier.
------------------------------------------------------------------------

proteinConformationSystemType : Set₁
proteinConformationSystemType =
  Protein.ProteinConformationSystem

proteinConformationReading : String
proteinConformationReading =
  "ProteinConformationAttractor already makes target conformation depend on sequence, environment and state/history, with possible multiple stable/metastable attractors. A future receptor-specific adapter should index recognition geometry by an inhabitant of that system rather than by a free String."

ionicSiteContextReading : String
ionicSiteContextReading =
  "IonicMimicryGeometryExact already provides the Pb2+/Ca2+ source-facing example: rigid/crowded and flexible/sparse binding-site contexts can produce different substitution outcomes for the same ion pair."

ionicBoundary : Ionic.IonicMimicryGeometryBoundary
ionicBoundary =
  Ionic.canonicalIonicMimicryGeometryBoundary

------------------------------------------------------------------------
-- Context transport.
------------------------------------------------------------------------

record RecognitionContextTransport
    (source target : ContextIndexedRecognitionTarget) : Set where
  constructor recognitionContextTransport
  field
    sameNominalTarget : Bool
    sameNominalTargetIsTrue :
      sameNominalTarget ≡ true

    contextChangeReference : String

    weightsMayChange : Bool
    weightsMayChangeIsTrue :
      weightsMayChange ≡ true

    tolerancesMayChange : Bool
    tolerancesMayChangeIsTrue :
      tolerancesMayChange ≡ true

    pairIdentityChanges : Bool
    pairIdentityChangesIsFalse :
      pairIdentityChanges ≡ false

open RecognitionContextTransport public

canonicalContextTransport :
  RecognitionContextTransport targetInContext0 targetInContext1
canonicalContextTransport =
  recognitionContextTransport
    true refl
    "finite binding-site-state change"
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Anti-collapse.
------------------------------------------------------------------------

data NominalTargetFixesRecognitionGeometry : Set where
data SameLigandPairMeansSameRecognitionAcrossConformations : Set where
data ProteinConformationIsIrrelevantToBinding : Set where
data ContextChangeMeansChemicalIdentityChanged : Set where

nominalTargetDoesNotFixGeometry :
  NominalTargetFixesRecognitionGeometry → ⊥
nominalTargetDoesNotFixGeometry ()

samePairDoesNotForceSameRecognitionAcrossConformations :
  SameLigandPairMeansSameRecognitionAcrossConformations → ⊥
samePairDoesNotForceSameRecognitionAcrossConformations ()

proteinConformationNotErased :
  ProteinConformationIsIrrelevantToBinding → ⊥
proteinConformationNotErased ()

contextChangeDoesNotChangeChemicalIdentity :
  ContextChangeMeansChemicalIdentityChanged → ⊥
contextChangeDoesNotChangeChemicalIdentity ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ContextIndexedRecognitionBoundary : Set where
  constructor contextIndexedRecognitionBoundary
  field
    samePairCanChangeAdmissionAcrossTargetStates : Bool
    samePairCanChangeAdmissionAcrossTargetStatesIsTrue :
      samePairCanChangeAdmissionAcrossTargetStates ≡ true

    recognitionGeometryIsContextIndexed : Bool
    recognitionGeometryIsContextIndexedIsTrue :
      recognitionGeometryIsContextIndexed ≡ true

    nominalTargetLabelFullyDeterminesGeometry : Bool
    nominalTargetLabelFullyDeterminesGeometryIsFalse :
      nominalTargetLabelFullyDeterminesGeometry ≡ false

    currentFixtureIsCalibratedProteinPhysics : Bool
    currentFixtureIsCalibratedProteinPhysicsIsFalse :
      currentFixtureIsCalibratedProteinPhysics ≡ false

open ContextIndexedRecognitionBoundary public

canonicalContextIndexedRecognitionBoundary :
  ContextIndexedRecognitionBoundary
canonicalContextIndexedRecognitionBoundary =
  contextIndexedRecognitionBoundary
    true refl
    true refl
    false refl
    false refl
