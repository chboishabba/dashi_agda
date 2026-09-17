module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseChemicalSystemExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Biology.Molecular.MolecularAssemblyBoundary as Molecular
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Hyper
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact as Empirical

------------------------------------------------------------------------
-- ADENYLATE-KINASE CHEMICAL SYSTEM
--
-- This owner closes the chemistry-identity layer below the current CV/state
-- graph without pretending that species identity determines conformation,
-- kinetics, atomistic force fields, or catalytic mechanism.  PubChem/QID/Rhea/
-- EC/UniProt identifiers are retained as identity coordinates only.
------------------------------------------------------------------------

adkArticleSource : Attribution.AttributedSource
adkArticleSource = Attr.liLiuJiSource

rheaSource : Attribution.AttributedSource
rheaSource = Attribution.mkNoDOISource
  "Rhea consortium / Swiss-Prot biocuration"
  "RHEA:12973 adenylate kinase reaction"
  "Rhea reaction knowledgebase"
  "retrieved 2026"
  "https://www.rhea-db.org/rhea/12973"
  Attribution.institutionalSource
  "pays curated reaction identity AMP + ATP = 2 ADP and participant charge/speciation for RHEA:12973; it does not pay AdK conformational dynamics"
  Attribution.publicAttribution

rheaSourceReceipt : Snowball.SourceRoleSnowballReceipt rheaSource
rheaSourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt rheaSource

------------------------------------------------------------------------
-- External chemical identities.
------------------------------------------------------------------------

atpPubChemCID : String
atpPubChemCID = "5957"
ampPubChemCID : String
ampPubChemCID = "6083"
adpPubChemCID : String
adpPubChemCID = "6022"
ap5aPubChemCID : String
ap5aPubChemCID = "53477724"
magnesiumPubChemCID : String
magnesiumPubChemCID = "888"

atpQID : Identity.ExternalIdentityDemand
atpQID = Identity.mkOptionalIdentityDemand
  "AdK chemical-system identity"
  "ATP Wikidata identity"
  "adenosine triphosphate"
  Identity.wikidataQid
  (Identity.verified "Wikidata" "Q80863")

ampQID : Identity.ExternalIdentityDemand
ampQID = Identity.mkOptionalIdentityDemand
  "AdK chemical-system identity"
  "AMP Wikidata identity"
  "adenosine monophosphate"
  Identity.wikidataQid
  (Identity.verified "Wikidata" "Q318369")

adpQID : Identity.ExternalIdentityDemand
adpQID = Identity.mkOptionalIdentityDemand
  "AdK chemical-system identity"
  "ADP Wikidata identity"
  "adenosine diphosphate"
  Identity.wikidataQid
  (Identity.verified "Wikidata" "Q185253")

ap5aQID : Identity.ExternalIdentityDemand
ap5aQID = Identity.mkOptionalIdentityDemand
  "AdK chemical-system identity"
  "Ap5A / diadenosine pentaphosphate Wikidata identity"
  "diadenosine pentaphosphate"
  Identity.wikidataQid
  (Identity.unresolved "same-object Wikidata QID not independently verified; PubChem CID 53477724 retained")

magnesiumQID : Identity.ExternalIdentityDemand
magnesiumQID = Identity.mkOptionalIdentityDemand
  "AdK chemical-system identity"
  "magnesium(2+) Wikidata identity"
  "magnesium(2+)"
  Identity.wikidataQid
  (Identity.verified "Wikidata" "Q26987404")

record ChemicalIdentityCoordinate : Set where
  constructor chemical-identity-coordinate
  field
    label : String
    pubChemCID : String
    qid : Identity.ExternalIdentityDemand
    reactionRole : String
    protonationOrChargeRole : String
    identitySourceRole : String
open ChemicalIdentityCoordinate public

atpIdentity : ChemicalIdentityCoordinate
atpIdentity = chemical-identity-coordinate
  "ATP" atpPubChemCID atpQID
  "RHEA:12973 reactant"
  "Rhea participant ATP charge -4; PubChem CID 5957 is retained as compound identity and is not silently equated to every protonation state"
  "PubChem/Wikidata identity + Rhea reaction participant"

ampIdentity : ChemicalIdentityCoordinate
ampIdentity = chemical-identity-coordinate
  "AMP" ampPubChemCID ampQID
  "RHEA:12973 reactant"
  "Rhea participant AMP charge -2; PubChem CID 6083 retained separately from reaction-state charge"
  "PubChem/Wikidata identity + Rhea reaction participant"

adpIdentity : ChemicalIdentityCoordinate
adpIdentity = chemical-identity-coordinate
  "ADP" adpPubChemCID adpQID
  "RHEA:12973 product, stoichiometric coefficient 2"
  "Rhea participant ADP charge -3; PubChem CID 6022 retained separately from reaction-state charge"
  "PubChem/Wikidata identity + Rhea reaction participant"

ap5aIdentity : ChemicalIdentityCoordinate
ap5aIdentity = chemical-identity-coordinate
  "Ap5A / diadenosine pentaphosphate" ap5aPubChemCID ap5aQID
  "structural inhibitor / transition-state-analogue context in the 1AKE lane; not automatically a catalytic reactant"
  "protonation state not promoted from bare PubChem identity"
  "PubChem identity + source-bounded structural context"

magnesiumIdentity : ChemicalIdentityCoordinate
magnesiumIdentity = chemical-identity-coordinate
  "Mg2+" magnesiumPubChemCID magnesiumQID
  "cofactor/context coordinate only where independently source-paid; RHEA:12973 core reaction identity does not by itself require insertion of Mg2+"
  "Mg2+ cation, PubChem CID 888"
  "PubChem/Wikidata identity; context role remains source-gated"

------------------------------------------------------------------------
-- Reuse the generic chemistry kernel for a qualitative reaction carrier.
------------------------------------------------------------------------

mkSpecies : String → String → String → Chemistry.Species
mkSpecies ident charge composition = record
  { speciesId = ident
  ; phase = Chemistry.dissolved
  ; chargeLabel = charge
  ; compositionLabel = composition
  ; mobilityClass = Chemistry.mobile
  ; activityModelLabel = "aqueous biochemical activity/speciation model unresolved at this bridge"
  ; opticalRoleLabel = "not used"
  ; evidence = Chemistry.literatureEstablished
  }

atpSpecies : Chemistry.Species
atpSpecies = mkSpecies "ATP / PubChem CID 5957 / Q80863" "Rhea charge -4" "C10H12N5O13P3 in Rhea participant form"

ampSpecies : Chemistry.Species
ampSpecies = mkSpecies "AMP / PubChem CID 6083 / Q318369" "Rhea charge -2" "C10H12N5O7P in Rhea participant form"

adpSpecies : Chemistry.Species
adpSpecies = mkSpecies "ADP / PubChem CID 6022 / Q185253" "Rhea charge -3" "C10H12N5O10P2 in Rhea participant form"

ap5aSpecies : Chemistry.Species
ap5aSpecies = mkSpecies "Ap5A / PubChem CID 53477724" "reaction-state charge unresolved" "diadenosine pentaphosphate structural inhibitor identity"

mg2Species : Chemistry.Species
mg2Species = mkSpecies "Mg2+ / PubChem CID 888 / Q26987404" "+2" "Mg2+"

oneATP : Chemistry.StoichiometricTerm
oneATP = record { species = atpSpecies ; coefficient = 1 }
oneAMP : Chemistry.StoichiometricTerm
oneAMP = record { species = ampSpecies ; coefficient = 1 }
twoADP : Chemistry.StoichiometricTerm
twoADP = record { species = adpSpecies ; coefficient = 2 }

adkCondition : Chemistry.Condition
adkCondition = record
  { conditionLabel = "adenylate-kinase biochemical reaction context; pH, ionic strength, Mg2+ occupancy and ligand state remain separate obligations"
  ; environment = Chemistry.emptyEnvironment
  ; guardExpression = "source-specific biochemical conditions required"
  }

adkRateLaw : Chemistry.RateLaw
adkRateLaw = Chemistry.unknownRate

adenylateKinaseReaction : Chemistry.Transition
adenylateKinaseReaction = record
  { transitionId = "RHEA:12973 / EC 2.7.4.3 : AMP + ATP = 2 ADP"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants = oneAMP ∷ oneATP ∷ []
  ; products = twoADP ∷ []
  ; catalysts = []
  ; rateLaw = adkRateLaw
  ; condition = adkCondition
  ; reversibility = Chemistry.reversible
  ; evidence = Chemistry.literatureEstablished
  }

molecularAssemblyBoundary : Molecular.MolecularAssemblyBoundary
molecularAssemblyBoundary = Molecular.canonicalMolecularAssemblyBoundary

atomicChemistryBoundary : Hyper.AtomicChemistryCrossPollinationBoundary
atomicChemistryBoundary = Hyper.canonicalAtomicChemistryCrossPollinationBoundary

openClosedEmpiricalBoundary : Empirical.AdenylateKinaseEmpiricalBoundary
openClosedEmpiricalBoundary = Empirical.canonicalAdenylateKinaseEmpiricalBoundary

------------------------------------------------------------------------
-- WrongType / source-role firewalls.
------------------------------------------------------------------------

data PubChemIdentityCreatesReactionState : Set where
data QidCreatesChemicalMechanism : Set where
data ReactionStoichiometryCreatesConformation : Set where
data Ap5AIdentityCreatesCatalyticTransitionState : Set where
data MgIdentityCreatesUniversalCofactorOccupancy : Set where
data SpeciesIdentityCreatesForceField : Set where

pubChemDoesNotCreateReactionState : PubChemIdentityCreatesReactionState → ⊥
pubChemDoesNotCreateReactionState ()
qidDoesNotCreateChemicalMechanism : QidCreatesChemicalMechanism → ⊥
qidDoesNotCreateChemicalMechanism ()
stoichiometryDoesNotCreateConformation : ReactionStoichiometryCreatesConformation → ⊥
stoichiometryDoesNotCreateConformation ()
ap5aIdentityDoesNotCreateCatalyticTransitionState : Ap5AIdentityCreatesCatalyticTransitionState → ⊥
ap5aIdentityDoesNotCreateCatalyticTransitionState ()
mgIdentityDoesNotCreateUniversalOccupancy : MgIdentityCreatesUniversalCofactorOccupancy → ⊥
mgIdentityDoesNotCreateUniversalOccupancy ()
speciesIdentityDoesNotCreateForceField : SpeciesIdentityCreatesForceField → ⊥
speciesIdentityDoesNotCreateForceField ()

record AdKChemicalSystemBoundary : Set where
  constructor adk-chemical-system-boundary
  field
    reactionIdentityPaid : Bool
    atpAmpAdpPubChemPaid : Bool
    atpAmpAdpQidsPaid : Bool
    ap5aPubChemPaid : Bool
    ap5aQidPaid : Bool
    magnesiumPubChemQidPaid : Bool
    reactionChargeRolesRetained : Bool
    genericChemistryKernelReused : Bool
    atomicMolecularBridgeReused : Bool
    pubChemCreatesReactionMechanism : Bool
    reactionStoichiometryCreatesConformation : Bool
    ap5aIdentityCreatesUniversalTransitionState : Bool
    magnesiumIdentityCreatesUniversalOccupancy : Bool
    chemicalIdentityCreatesForceField : Bool

canonicalAdKChemicalSystemBoundary : AdKChemicalSystemBoundary
canonicalAdKChemicalSystemBoundary = adk-chemical-system-boundary
  true true true true false true true true true
  false false false false false
