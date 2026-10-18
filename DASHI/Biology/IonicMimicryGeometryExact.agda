module DASHI.Biology.IonicMimicryGeometryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.IonicMimicrySourceAtlasExact as Sources
import DASHI.Biology.BioactiveMolecularRecognitionBridge as Recognition
import DASHI.Biology.NeurochemicalAtomicChemistryBridge as AtomicChem
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Chemistry369

------------------------------------------------------------------------
-- GEOMETRIC / ELECTROSTATIC MIMICRY
--
-- "Looks like" is not one relation.
--
-- For ions and molecules, a target may respond to overlapping subsets of:
--   charge
--   size
--   ligand donor chemistry
--   coordination number
--   coordination geometry
--   hydration / solvent organization
--   conformational accommodation
--   kinetics / occupancy
--
-- Matching some coordinates can permit substitution even while other
-- coordinates differ enough to distort the host protein.
------------------------------------------------------------------------

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Sources.canonicalIonicMimicrySourceAtlas

data MimicryCoordinate : Set where
  formalChargeCoordinate : MimicryCoordinate
  effectiveSizeCoordinate : MimicryCoordinate
  donorAtomPreferenceCoordinate : MimicryCoordinate
  coordinationNumberCoordinate : MimicryCoordinate
  coordinationGeometryCoordinate : MimicryCoordinate
  hydrationCoordinate : MimicryCoordinate
  siteFlexibilityCoordinate : MimicryCoordinate
  conformationalResponseCoordinate : MimicryCoordinate
  affinityCoordinate : MimicryCoordinate
  kineticCoordinate : MimicryCoordinate

data MimicryRelation : Set where
  overlappingCoordinate : MimicryRelation
  substitutableInSourceAssay : MimicryRelation
  nativeGeometryPreserved : MimicryRelation
  geometryDistorted : MimicryRelation
  targetActivated : MimicryRelation
  targetInhibited : MimicryRelation
  unresolved : MimicryRelation

data IonIdentity : Set where
  calciumII : IonIdentity
  leadII : IonIdentity
  strontiumII : IonIdentity
  bariumII : IonIdentity
  zincII : IonIdentity
  magnesiumII : IonIdentity

record IonMimicryCoordinateReceipt : Set where
  constructor ionMimicryCoordinateReceipt
  field
    source : Source.AttributedSource
    nativeIon : IonIdentity
    mimicIon : IonIdentity
    coordinate : MimicryCoordinate
    relation : MimicryRelation
    reading : String

    chemicalIdentityCollapsed : Bool
    chemicalIdentityCollapsedIsFalse :
      chemicalIdentityCollapsed ≡ false

open IonMimicryCoordinateReceipt public

pbCaChargeOverlap : IonMimicryCoordinateReceipt
pbCaChargeOverlap =
  ionMimicryCoordinateReceipt
    Sources.kirbergerYang2008
    calciumII
    leadII
    formalChargeCoordinate
    overlappingCoordinate
    "Ca2+ and Pb2+ share the same formal +2 charge coordinate, but charge equality is only one component of recognition."
    false refl

pbCaOxygenDonorOverlap : IonMimicryCoordinateReceipt
pbCaOxygenDonorOverlap =
  ionMimicryCoordinateReceipt
    Sources.kirbergerYang2008
    calciumII
    leadII
    donorAtomPreferenceCoordinate
    overlappingCoordinate
    "Oxygen donors dominate both Ca2+- and Pb2+-binding protein sites in the cited structural survey."
    false refl

pbCaCoordinationDifference : IonMimicryCoordinateReceipt
pbCaCoordinationDifference =
  ionMimicryCoordinateReceipt
    Sources.kirbergerYang2008
    calciumII
    leadII
    coordinationNumberCoordinate
    geometryDistorted
    "The structural survey reports lower typical Pb2+ ligand counts than canonical EF-hand Ca2+ sites, so substitution need not preserve coordination number."
    false refl

pbInEFHandSubstitution : IonMimicryCoordinateReceipt
pbInEFHandSubstitution =
  ionMimicryCoordinateReceipt
    Sources.kumarEtAl2012
    calciumII
    leadII
    coordinationGeometryCoordinate
    substitutableInSourceAssay
    "Pb2+ occupies Ca2+-binding EF-hand motifs with broadly similar overall protein structure but metal-specific coordination details."
    false refl

pbRigidSiteGeometryPreservation : IonMimicryCoordinateReceipt
pbRigidSiteGeometryPreservation =
  ionMimicryCoordinateReceipt
    Sources.dudevGrauffelLim2018
    calciumII
    leadII
    siteFlexibilityCoordinate
    nativeGeometryPreserved
    "In the cited modeled rigid/crowded Ca2+ sites, Pb2+ can preserve native-like geometry and may activate the host protein at low concentration."
    false refl

pbFlexibleSiteGeometryDistortion : IonMimicryCoordinateReceipt
pbFlexibleSiteGeometryDistortion =
  ionMimicryCoordinateReceipt
    Sources.dudevGrauffelLim2018
    calciumII
    leadII
    siteFlexibilityCoordinate
    geometryDistorted
    "In the cited modeled flexible/fewer-ligand sites, Pb2+ can displace Ca2+ while deforming native geometry."
    false refl

pbCalmodulinFunctionalSubstitution : IonMimicryCoordinateReceipt
pbCalmodulinFunctionalSubstitution =
  ionMimicryCoordinateReceipt
    Sources.habermannEtAl1983
    calciumII
    leadII
    conformationalResponseCoordinate
    substitutableInSourceAssay
    "Pb2+ substituted for Ca2+ in several calmodulin-dependent assay contexts in the cited study."
    false refl

pbPKCGeometry : IonMimicryCoordinateReceipt
pbPKCGeometry =
  ionMimicryCoordinateReceipt
    Sources.moralesEtAl2011
    calciumII
    leadII
    coordinationGeometryCoordinate
    substitutableInSourceAssay
    "Pb2+ binds the PKCalpha C2 domain and can occupy distinct coordination geometries in the same protein context."
    false refl

canonicalPbCaMimicryCoordinates : List IonMimicryCoordinateReceipt
canonicalPbCaMimicryCoordinates =
  pbCaChargeOverlap
  ∷ pbCaOxygenDonorOverlap
  ∷ pbCaCoordinationDifference
  ∷ pbInEFHandSubstitution
  ∷ pbRigidSiteGeometryPreservation
  ∷ pbFlexibleSiteGeometryDistortion
  ∷ pbCalmodulinFunctionalSubstitution
  ∷ pbPKCGeometry
  ∷ []

------------------------------------------------------------------------
-- Geometry is target-relative rather than globally intrinsic.
------------------------------------------------------------------------

data BindingSiteRigidity : Set where
  rigidCrowdedSite : BindingSiteRigidity
  flexibleSparseSite : BindingSiteRigidity
  intermediateSite : BindingSiteRigidity

data MimicryOutcome : Set where
  nativeLikeActivationCandidate : MimicryOutcome
  partialFunctionalSubstitutionCandidate : MimicryOutcome
  distortedMalfunctionCandidate : MimicryOutcome
  inhibitionCandidate : MimicryOutcome
  noGeneralOutcome : MimicryOutcome

siteConditionedPbOutcome : BindingSiteRigidity → MimicryOutcome
siteConditionedPbOutcome rigidCrowdedSite =
  nativeLikeActivationCandidate
siteConditionedPbOutcome flexibleSparseSite =
  distortedMalfunctionCandidate
siteConditionedPbOutcome intermediateSite =
  noGeneralOutcome

rigidityChangesOutcome :
  siteConditionedPbOutcome rigidCrowdedSite
  ≡
  siteConditionedPbOutcome flexibleSparseSite
  →
  ⊥
rigidityChangesOutcome ()

------------------------------------------------------------------------
-- Reuse the repo's pre-existing recognition coordinates.
------------------------------------------------------------------------

similarityCarriers : List Recognition.BioactiveSimilarityCarrier
similarityCarriers =
  Recognition.canonicalBioactiveSimilarityCarriers

atomicChemistrySlots : List AtomicChem.NeurochemicalAtomicChemistrySlot
atomicChemistrySlots =
  AtomicChem.canonicalNeurochemicalAtomicChemistrySlots

chemistryBoundary : Chemistry369.AtomicChemistryCrossPollinationBoundary
chemistryBoundary =
  Chemistry369.canonicalAtomicChemistryCrossPollinationBoundary

------------------------------------------------------------------------
-- General anti-collapse results.
------------------------------------------------------------------------

data SameChargeMeansSameBiologicalAction : Set where
data SimilarRadiusMeansSameBindingGeometry : Set where
data SubstitutionMeansChemicalIdentity : Set where
data BindingMeansFunctionalEquivalence : Set where
data GeometryAloneDeterminesAffinity : Set where

sameChargeDoesNotMeanSameAction :
  SameChargeMeansSameBiologicalAction → ⊥
sameChargeDoesNotMeanSameAction ()

similarRadiusDoesNotMeanSameGeometry :
  SimilarRadiusMeansSameBindingGeometry → ⊥
similarRadiusDoesNotMeanSameGeometry ()

substitutionDoesNotMeanChemicalIdentity :
  SubstitutionMeansChemicalIdentity → ⊥
substitutionDoesNotMeanChemicalIdentity ()

bindingDoesNotMeanFunctionalEquivalence :
  BindingMeansFunctionalEquivalence → ⊥
bindingDoesNotMeanFunctionalEquivalence ()

geometryAloneDoesNotDetermineAffinity :
  GeometryAloneDeterminesAffinity → ⊥
geometryAloneDoesNotDetermineAffinity ()

------------------------------------------------------------------------
-- Generalized recognition rule.
------------------------------------------------------------------------

record TargetRelativeMimicry : Set where
  constructor targetRelativeMimicry
  field
    nativeIdentity : String
    candidateIdentity : String
    targetReference : String
    matchedCoordinates : List MimicryCoordinate
    mismatchedCoordinates : List MimicryCoordinate
    siteRigidity : BindingSiteRigidity
    observedOutcome : MimicryOutcome
    protocolReference : String

    coordinateOverlapNotIdentity : Bool
    coordinateOverlapNotIdentityIsTrue :
      coordinateOverlapNotIdentity ≡ true

    targetRelativeNotGlobal : Bool
    targetRelativeNotGlobalIsTrue :
      targetRelativeNotGlobal ≡ true

open TargetRelativeMimicry public

canonicalPbCaTargetRelativeMimicry : TargetRelativeMimicry
canonicalPbCaTargetRelativeMimicry =
  targetRelativeMimicry
    "Ca2+"
    "Pb2+"
    "Ca2+-binding protein site"
    ( formalChargeCoordinate
    ∷ donorAtomPreferenceCoordinate
    ∷ effectiveSizeCoordinate
    ∷ []
    )
    ( coordinationNumberCoordinate
    ∷ coordinationGeometryCoordinate
    ∷ hydrationCoordinate
    ∷ []
    )
    intermediateSite
    noGeneralOutcome
    "source/site specific"
    true refl
    true refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record IonicMimicryGeometryBoundary : Set where
  constructor ionicMimicryGeometryBoundary
  field
    chargeSizeGeometrySeparated : Bool
    chargeSizeGeometrySeparatedIsTrue :
      chargeSizeGeometrySeparated ≡ true

    siteFlexibilityChangesMimicryOutcome : Bool
    siteFlexibilityChangesMimicryOutcomeIsTrue :
      siteFlexibilityChangesMimicryOutcome ≡ true

    leadCalciumChemicalIdentityEqual : Bool
    leadCalciumChemicalIdentityEqualIsFalse :
      leadCalciumChemicalIdentityEqual ≡ false

    allCalciumSitesVulnerableToLeadInSameWay : Bool
    allCalciumSitesVulnerableToLeadInSameWayIsFalse :
      allCalciumSitesVulnerableToLeadInSameWay ≡ false

    geometryAloneSufficientForBiologicalEffect : Bool
    geometryAloneSufficientForBiologicalEffectIsFalse :
      geometryAloneSufficientForBiologicalEffect ≡ false

open IonicMimicryGeometryBoundary public

canonicalIonicMimicryGeometryBoundary : IonicMimicryGeometryBoundary
canonicalIonicMimicryGeometryBoundary =
  ionicMimicryGeometryBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
