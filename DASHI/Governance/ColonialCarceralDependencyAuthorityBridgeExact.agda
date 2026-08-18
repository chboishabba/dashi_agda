module DASHI.Governance.ColonialCarceralDependencyAuthorityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DependentAuthorityCoercionKernel as Coercion
import DASHI.Governance.InstitutionalTechniqueTransferCore as Transfer
import DASHI.Biology.TrumpPsychogeographicPolicyAtlasExact as Trump

------------------------------------------------------------------------
-- SOURCE CALIBRATION
--
-- This bridge is structural. It reuses source-scoped repository surfaces for
-- Indigenous land/extraction/consultation/naming and detention/removal/data
-- infrastructure, but does not assert that colonial, carceral, familial or
-- religious systems are historically identical.
--
-- Existing Trump policy atlas sources are primary-policy records and remain
-- bounded to the policy surfaces they document. This module introduces no new
-- historical causal conclusion merely from reuse of those carriers.
------------------------------------------------------------------------

data AuthorityScale : Set where
  familyScale institutionScale stateScale territorialScale : AuthorityScale

data ExitMode : Set where
  physicalExit materialExit socialBelongingExit epistemicExit territorialExit proceduralExit : ExitMode

data ConstraintMode : Set where
  bodilyConstraint detentionConstraint materialDependencyConstraint : ConstraintMode
  socialSanctionConstraint beliefClosureConstraint landDisplacementConstraint : ConstraintMode
  administrativeClassificationConstraint : ConstraintMode

record DependencyAuthorityTopology : Set where
  constructor dependencyAuthorityTopology
  field
    scale : AuthorityScale
    exits : List ExitMode
    constraints : List ConstraintMode
    authorityRelation : Coercion.AuthorityRelation
    sourceScopedLabel : String

------------------------------------------------------------------------
-- Domain-specific constructors keep empirical classes apart while exposing
-- the common lower-level topology.
------------------------------------------------------------------------

data DomainTopologyCase : Set where
  dependentChildCase : DependencyAuthorityTopology → DomainTopologyCase
  colonialAdministrationCase : DependencyAuthorityTopology → DomainTopologyCase
  detentionCarceralCase : DependencyAuthorityTopology → DomainTopologyCase
  civicDataAdministrationCase : DependencyAuthorityTopology → DomainTopologyCase

record ColonialCarceralCrossPollination : Set where
  constructor colonialCarceralCrossPollination
  field
    childTopology : DependencyAuthorityTopology
    colonialTopology : DependencyAuthorityTopology
    carceralTopology : DependencyAuthorityTopology
    civicDataTopology : DependencyAuthorityTopology
    commonCoordinatesMayBeCompared : Bool
    domainsHistoricallyEquivalent : Bool
    sharedTopologyCreatesSameLegalClassification : Bool

------------------------------------------------------------------------
-- Existing repository surfaces provide the typed domain anchors.
------------------------------------------------------------------------

indigenousPolicySurfaceImported : Trump.TrumpPolicyCase
indigenousPolicySurfaceImported = Trump.indigenousPolicyCase

immigrationDetentionSurfaceImported : Trump.TrumpPolicyCase
immigrationDetentionSurfaceImported = Trump.immigrationRaidsMassDeportationCase

palantirDataSurfaceImported : Trump.TrumpPolicyCase
palantirDataSurfaceImported = Trump.palantirSurveillanceProcurementCase

policingDomainImported : Transfer.InstitutionalDomain
policingDomainImported = Transfer.policingDomain

carceralDomainImported : Transfer.InstitutionalDomain
carceralDomainImported = Transfer.carceralDomain

civicAdministrationDomainImported : Transfer.InstitutionalDomain
civicAdministrationDomainImported = Transfer.civicAdministrationDomain

------------------------------------------------------------------------
-- Exact semantic boundaries.
------------------------------------------------------------------------

data SharedExitConstraintEstablishesHistoricalIdentity : Set where

data ColonialTopologyEstablishesSlavery : Set where

data CarceralTopologyEstablishesAbuse : Set where

data FamilyTopologyEstablishesColoniality : Set where

sharedExitConstraintDoesNotEstablishHistoricalIdentity :
  SharedExitConstraintEstablishesHistoricalIdentity → ⊥
sharedExitConstraintDoesNotEstablishHistoricalIdentity ()

colonialTopologyDoesNotEstablishSlavery :
  ColonialTopologyEstablishesSlavery → ⊥
colonialTopologyDoesNotEstablishSlavery ()

carceralTopologyDoesNotEstablishAbuse :
  CarceralTopologyEstablishesAbuse → ⊥
carceralTopologyDoesNotEstablishAbuse ()

familyTopologyDoesNotEstablishColoniality :
  FamilyTopologyEstablishesColoniality → ⊥
familyTopologyDoesNotEstablishColoniality ()

record ColonialCarceralDependencyBoundary : Set where
  constructor colonialCarceralDependencyBoundary
  field
    dependencyAuthorityExitTopologyShared : Bool
    comparisonAcrossScalesAllowed : Bool
    familyReligionEqualsColonialSystem : Bool
    colonialSystemEqualsCarceralSystem : Bool
    detentionEqualsSlavery : Bool
    indigenousPolicySurfaceCreatesHistoricalColonisationProof : Bool
    procurementSurfaceCreatesCarceralAbuseProof : Bool

canonicalColonialCarceralDependencyBoundary :
  ColonialCarceralDependencyBoundary
canonicalColonialCarceralDependencyBoundary =
  colonialCarceralDependencyBoundary
    true true false false false false false
