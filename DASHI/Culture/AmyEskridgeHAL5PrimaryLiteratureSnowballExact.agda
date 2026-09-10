module DASHI.Culture.AmyEskridgeHAL5PrimaryLiteratureSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.AmyEskridgeMechanismAssociationProvenanceExact as Assoc

------------------------------------------------------------------------
-- AMY HAL5 -> PRIMARY-LITERATURE SNOWBALL
--
-- Each row preserves three distinct things:
--   (1) what Amy's official HAL5 deck actually mentions;
--   (2) an independently attributable primary publication for that historical
--       mechanism family when one has been identified;
--   (3) whether DASHI has inspected an exact theorem/equation carrier.
--
-- A source row may be accumulated before all downstream physics debts are paid.
-- Amy's deck does not become the primary paper, and the primary paper does not
-- become an Amy-authored result.
------------------------------------------------------------------------

data PrimaryInspectionStatus : Set where
  bibliographicIdentityOnly : PrimaryInspectionStatus
  abstractInspected : PrimaryInspectionStatus
  exactCarrierInspected : PrimaryInspectionStatus

data PrimaryRelation : Set where
  historicalMechanismPrimarySource : PrimaryRelation
  laterReplicationOrConstraint : PrimaryRelation
  contextualFollowup : PrimaryRelation

record AmyPrimaryLiteratureSnowballAtom : Set where
  constructor amy-primary-literature-snowball-atom
  field
    amyAssociation : Assoc.MechanismAssociationReceipt
    amyDeckCoordinate : String
    primaryAuthors : String
    primaryTitle : String
    primaryPublication : String
    primaryDOI : String
    relation : PrimaryRelation
    inspectionStatus : PrimaryInspectionStatus
    sourceRoleBoundary : String

open AmyPrimaryLiteratureSnowballAtom public

liTorr1991Atom : AmyPrimaryLiteratureSnowballAtom
liTorr1991Atom =
  amy-primary-literature-snowball-atom
    Assoc.liTorrAssociation
    "HAL5-Dec2018-Talk-AntiGravity.pdf, PDF page 24"
    "Ning Li; D. G. Torr"
    "Effects of a gravitomagnetic field on pure superconductors"
    "Physical Review D 43, 457 (1991)"
    "10.1103/PhysRevD.43.457"
    historicalMechanismPrimarySource
    abstractInspected
    "Amy discusses Li-Torr historically; Li and Torr own the primary paper; DASHI owns any modern source/mass-current reconstruction"

liTorr1992Atom : AmyPrimaryLiteratureSnowballAtom
liTorr1992Atom =
  amy-primary-literature-snowball-atom
    Assoc.liTorrAssociation
    "HAL5-Dec2018-Talk-AntiGravity.pdf, PDF page 24"
    "Ning Li; D. G. Torr"
    "Gravitational effects on the magnetic attenuation of superconductors"
    "Physical Review B 46, 5489 (1992)"
    "10.1103/PhysRevB.46.5489"
    historicalMechanismPrimarySource
    abstractInspected
    "Amy discussion != Li/Torr authorship transfer; primary theory != experimental validation"

podkletnov1992Atom : AmyPrimaryLiteratureSnowballAtom
podkletnov1992Atom =
  amy-primary-literature-snowball-atom
    Assoc.podkletnovAssociation
    "HAL5-Dec2018-Talk-AntiGravity.pdf, PDF page 26"
    "E. Podkletnov; R. Nieminen"
    "A possibility of gravitational force shielding by bulk YBa2Cu3O7-x superconductor"
    "Physica C 203 (1992) 441-444"
    "10.1016/0921-4534(92)90055-H"
    historicalMechanismPrimarySource
    abstractInspected
    "Records the published shielding/weight-loss claim as Podkletnov/Nieminen's result; Amy's slide is evidence only that she discussed that claim"

woodward1992Atom : AmyPrimaryLiteratureSnowballAtom
woodward1992Atom =
  amy-primary-literature-snowball-atom
    Assoc.woodwardAssociation
    "HAL5-Dec2018-Talk-AntiGravity.pdf, PDF page 23"
    "James F. Woodward"
    "A stationary apparent weight shift from a transient Machian mass fluctuation"
    "Foundations of Physics Letters 5 (1992) 425-442"
    "10.1007/BF00690424"
    historicalMechanismPrimarySource
    bibliographicIdentityOnly
    "Amy's Woodward/Mach slide seeds this primary-source route; no exact equation or experimental claim is imported until the paper carrier is inspected"

------------------------------------------------------------------------
-- Snowball semantics: bibliographic/source atoms may accumulate before a
-- consumer has enough exact source material to pay a theory or experiment leaf.
------------------------------------------------------------------------

record AmyPrimaryLiteratureSnowballBoundary : Set where
  constructor amy-primary-literature-snowball-boundary
  field
    amyDeckMentionEqualsPrimaryPaperAuthorship : Bool
    primaryPaperEqualsAmyEndorsement : Bool
    bibliographicIdentityEqualsExactEquationInspection : Bool
    abstractInspectionEqualsExperimentalReplication : Bool
    laterConstraintMayRewriteOriginalClaim : Bool
    atomsMayAccumulateOutOfDependencyOrder : Bool
    sourceRolesRemainDistinctDuringSnowball : Bool

canonicalAmyPrimaryLiteratureSnowballBoundary : AmyPrimaryLiteratureSnowballBoundary
canonicalAmyPrimaryLiteratureSnowballBoundary =
  amy-primary-literature-snowball-boundary false false false false false true true
