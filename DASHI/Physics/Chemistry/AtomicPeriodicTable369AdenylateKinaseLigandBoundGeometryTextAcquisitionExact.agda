module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLigandBoundGeometryTextAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseGammaLCrystalReferenceAcquisitionExact as GammaLRefs

------------------------------------------------------------------------
-- MACHINE-READABLE LIGAND-BOUND GEOMETRY / PATH CONSTRAINT ACQUISITION
--
-- Li, Liu & Ji's ligand-bound metadynamics prose pays several numeric/role
-- constraints without requiring visual transcription of Figure 6:
--   * most ligand-bound AdK crystal structures lie in the closed cluster near
--     theta1 ~= 65 deg, theta2 ~= 28 deg;
--   * the region near theta1 ~= 90 deg, theta2 ~= 30 deg is strongly
--     energetically unfavourable;
--   * the favoured route is alpha_L -> beta_L -> gamma_L -> delta_L -> zeta_L;
--   * delta_L is described as an NMP semi-open state;
--   * two known crystal structures lie near gamma_L and one lies near epsilon_L.
--
-- These are region/path constraints.  They do NOT assign exact theta1/theta2 or
-- dLN values to gamma_L, beta_L, delta_L, epsilon_L, or any other named
-- intermediate state.  In particular, proximity of 1DVR/2C9Y to gamma_L cannot
-- be inverted into exact gamma_L coordinates.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Sparse.liLiuJi2015Source

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

attributionEnvelope = Attr.canonicalAdKCalibrationAttributionBoundary

articleDOI : Identity.ExternalIdentityDemand
articleDOI = Attr.articleDOI

articlePMID : Identity.ExternalIdentityDemand
articlePMID = Attr.articlePMID

articlePMCID : Identity.ExternalIdentityDemand
articlePMCID = Attr.articlePMCID

articleQID : Identity.ExternalIdentityDemand
articleQID = Attr.articleQID

adkQID : Identity.ExternalIdentityDemand
adkQID = Attr.adkQID

------------------------------------------------------------------------
-- Numeric region constraints acquired from machine-readable article text.
------------------------------------------------------------------------

record ApproxAnglePoint : Set where
  constructor approx-angle-point
  field
    thetaOneDegrees : Nat
    thetaTwoDegrees : Nat
    approximationRole : String
    sourceLocator : String
open ApproxAnglePoint public

ligandBoundClosedCluster : ApproxAnglePoint
ligandBoundClosedCluster = approx-angle-point
  65 28
  "approximate center/representative coordinates reported for the closed cluster occupied by most ligand-bound crystal structures; not an exact coordinate of every closed structure or of zeta_L"
  "Li-Liu-Ji 2015, ligand-bound metadynamics prose following Figure 6: most ligand-bound crystal structures stay in the closed state, theta1 approximately 65 degrees and theta2 approximately 28 degrees"

ligandBoundNmpFirstUnfavourableRegion : ApproxAnglePoint
ligandBoundNmpFirstUnfavourableRegion = approx-angle-point
  90 30
  "approximate strongly energetically unfavourable region; source uses it to argue against NMP-first closure under ligand-bound conditions"
  "Li-Liu-Ji 2015, ligand-bound metadynamics prose following Figure 6: region around theta1 approximately 90 degrees and theta2 approximately 30 degrees is strongly unfavourable"

closedClusterThetaOnePaid : Bool
closedClusterThetaOnePaid = true

closedClusterThetaTwoPaid : Bool
closedClusterThetaTwoPaid = true

unfavourableRegionPaid : Bool
unfavourableRegionPaid = true

------------------------------------------------------------------------
-- Source-paid route and classification roles.
------------------------------------------------------------------------

data LigandBoundState : Set where
  alphaL betaL gammaL deltaL epsilonL zetaL : LigandBoundState

record LigandBoundRoute : Set where
  constructor ligand-bound-route
  field
    first : LigandBoundState
    second : LigandBoundState
    third : LigandBoundState
    fourth : LigandBoundState
    fifth : LigandBoundState
    sourceLocator : String
    interpretation : String
open LigandBoundRoute public

favouredLigandBoundRoute : LigandBoundRoute
favouredLigandBoundRoute = ligand-bound-route
  alphaL betaL gammaL deltaL zetaL
  "Li-Liu-Ji 2015, ligand-bound metadynamics prose/Figure 6"
  "source-described favoured gorge/path from open to closed; route membership does not assign exact intermediate coordinates or experimental kinetics"

favouredPathPaid : Bool
favouredPathPaid = true

record NamedStateRoleConstraint : Set where
  constructor named-state-role-constraint
  field
    state : LigandBoundState
    role : String
    sourceLocator : String
    exactThetaOnePaid : Bool
    exactThetaTwoPaid : Bool
    exactDLnPaid : Bool
open NamedStateRoleConstraint public

deltaLRole : NamedStateRoleConstraint
deltaLRole = named-state-role-constraint
  deltaL
  "semi-open NMP state on the ligand-bound route; source also says its free energy is slightly below zeta_L"
  "Li-Liu-Ji 2015, ligand-bound metadynamics prose following Figure 6"
  false false false

gammaLRole : NamedStateRoleConstraint
gammaLRole = named-state-role-constraint
  gammaL
  "intermediate state with two independent cross-species crystal structures reported nearby under the paper's theta1/theta2 projection"
  "Li-Liu-Ji 2015 Figure 6a/prose; see retained 1DVR/2C9Y same-object reference snowball"
  false false false

epsilonLRole : NamedStateRoleConstraint
epsilonLRole = named-state-role-constraint
  epsilonL
  "intermediate state with one known crystal structure reported nearby, but the machine-readable prose inspected here does not name that PDB object"
  "Li-Liu-Ji 2015 ligand-bound metadynamics prose following Figure 6"
  false false false

-- Reuse, do not rewrite, the independently attributed gamma_L-near structures.
oneDVRNearGammaL = GammaLRefs.oneDVRReference
twoC9YNearGammaL = GammaLRefs.twoC9YReference

gammaLExactCoordinatePaid : Bool
gammaLExactCoordinatePaid = false

intermediateDLnNamedStatePaid : Bool
intermediateDLnNamedStatePaid = false

------------------------------------------------------------------------
-- WrongType / same-object firewalls.
------------------------------------------------------------------------

data ClosedClusterCenterCreatesZetaLExactCoordinates : Set where
data UnfavourableRegionCreatesTransitionStateIdentity : Set where
data NearGammaLCrystalsCreateGammaLCoordinates : Set where
data RouteMembershipCreatesNamedStateDLn : Set where
data SourcePathCreatesExperimentalMechanism : Set where

data IdentityMetadataCreatesGeometry : Set where

closedClusterDoesNotCreateZetaLExactCoordinates : ClosedClusterCenterCreatesZetaLExactCoordinates → ⊥
closedClusterDoesNotCreateZetaLExactCoordinates ()

unfavourableRegionDoesNotCreateTransitionStateIdentity : UnfavourableRegionCreatesTransitionStateIdentity → ⊥
unfavourableRegionDoesNotCreateTransitionStateIdentity ()

nearGammaLCrystalsDoNotCreateGammaLCoordinates : NearGammaLCrystalsCreateGammaLCoordinates → ⊥
nearGammaLCrystalsDoNotCreateGammaLCoordinates ()

routeMembershipDoesNotCreateNamedStateDLn : RouteMembershipCreatesNamedStateDLn → ⊥
routeMembershipDoesNotCreateNamedStateDLn ()

sourcePathDoesNotCreateExperimentalMechanism : SourcePathCreatesExperimentalMechanism → ⊥
sourcePathDoesNotCreateExperimentalMechanism ()

identityMetadataDoesNotCreateGeometry : IdentityMetadataCreatesGeometry → ⊥
identityMetadataDoesNotCreateGeometry ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record LigandBoundGeometryTextBoundary : Set where
  constructor ligand-bound-geometry-text-boundary
  field
    closedClusterApprox65_28Paid : Bool
    nmpFirstUnfavourableApprox90_30Paid : Bool
    alphaBetaGammaDeltaZetaRoutePaid : Bool
    deltaLSemiOpenNmpRolePaid : Bool
    twoCrystalsNearGammaLPaid : Bool
    oneCrystalNearEpsilonLPaidQualitatively : Bool
    exactGammaLThetaCoordinatesPaid : Bool
    exactNamedIntermediateDLnPaid : Bool
    nearGammaLCrystalEqualsGammaL : Bool
    sourceRouteEqualsExperimentalMechanism : Bool
    qidDoiUniProtCreateGeometry : Bool
    sourceAuthorshipTransfersToDashiFormalisation : Bool
    nextResidual : String
open LigandBoundGeometryTextBoundary public

canonicalLigandBoundGeometryTextBoundary : LigandBoundGeometryTextBoundary
canonicalLigandBoundGeometryTextBoundary = ligand-bound-geometry-text-boundary
  true true true true true true
  false false false false false false
  "identify the single crystal reported near epsilon_L if a same-object source/table locator names it, and acquire exact gamma_L/beta_L/delta_L/epsilon_L theta or dLN values only from locator-specific source material. Do not invert cluster centers or near-state PDB references into named-state coordinates."
