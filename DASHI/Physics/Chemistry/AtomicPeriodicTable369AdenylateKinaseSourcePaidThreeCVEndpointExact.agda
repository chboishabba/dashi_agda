module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourcePaidThreeCVEndpointExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseEndpointDLnAcquisitionExact as DLn
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseNDimGeometricResidualExact as NDim
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseStructuralIdentitySnowballExact as Structural

------------------------------------------------------------------------
-- SOURCE-PAID THREE-CV ENDPOINT PAIR
--
-- The article text pays all three endpoint coordinates used by Li, Liu & Ji:
--   open 4AKE  : theta1 ≈ 95 deg, theta2 ≈ 61 deg, dLN ≈ 38 A
--   closed 1AKE: theta1 ≈ 68 deg, theta2 ≈ 28 deg, dLN ≈ 20 A.
--
-- This owner composes those same-article/source-paid values into a three-CV
-- endpoint carrier.  The composition is DASHI synthesis.  It does not promote
-- approximate printed values to exact physical truth, fill any intermediate
-- state, or infer a transition path from two endpoint points.
------------------------------------------------------------------------

data EndpointRole : Set where
  openEndpointRole : EndpointRole
  closedEndpointRole : EndpointRole

record ThreeCVEndpoint : Set where
  constructor three-cv-endpoint
  field
    endpointRole : EndpointRole
    pdbLabel : String
    thetaOneDegrees : Nat
    thetaTwoDegrees : Nat
    dLnAngstrom : Nat
    source : Attribution.AttributedSource
    pdbSource : Attribution.AttributedSource
    articleDOI : Identity.ExternalIdentityDemand
    articleQID : Identity.ExternalIdentityDemand
    adkQID : Identity.ExternalIdentityDemand
    uniprot : Identity.ExternalIdentityDemand
    interpretation : String
open ThreeCVEndpoint public

source : Attribution.AttributedSource
source = DLn.source

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

openEndpoint : ThreeCVEndpoint
openEndpoint = three-cv-endpoint
  openEndpointRole
  "4AKE"
  95
  61
  DLn.openEndpointDLnAngstrom
  source
  Structural.open4AKESource
  Attr.articleDOI
  Attr.articleQID
  Structural.adkQid
  Structural.adkUniProt
  "same-article three-CV open endpoint: theta1~95 deg, theta2~61 deg, dLN~38 A; PDB 4AKE is the structural reference role"

closedEndpoint : ThreeCVEndpoint
closedEndpoint = three-cv-endpoint
  closedEndpointRole
  "1AKE"
  68
  28
  DLn.closedEndpointDLnAngstrom
  source
  Structural.closed1AKESource
  Attr.articleDOI
  Attr.articleQID
  Structural.adkQid
  Structural.adkUniProt
  "same-article three-CV closed endpoint: theta1~68 deg, theta2~28 deg, dLN~20 A; PDB 1AKE is the structural reference role"

------------------------------------------------------------------------
-- Coordinate separation.
------------------------------------------------------------------------

thetaOneSeparatesEndpoints :
  thetaOneDegrees openEndpoint ≡ thetaOneDegrees closedEndpoint → ⊥
thetaOneSeparatesEndpoints ()

thetaTwoSeparatesEndpoints :
  thetaTwoDegrees openEndpoint ≡ thetaTwoDegrees closedEndpoint → ⊥
thetaTwoSeparatesEndpoints ()

dLnSeparatesEndpoints :
  dLnAngstrom openEndpoint ≡ dLnAngstrom closedEndpoint → ⊥
dLnSeparatesEndpoints ()

record ThreeCVTriple : Set where
  constructor three-cv-triple
  field
    thetaOne : Nat
    thetaTwo : Nat
    dLn : Nat
open ThreeCVTriple public

endpointTriple : ThreeCVEndpoint → ThreeCVTriple
endpointTriple endpoint = three-cv-triple
  (thetaOneDegrees endpoint)
  (thetaTwoDegrees endpoint)
  (dLnAngstrom endpoint)

endpointTriplesDiffer :
  endpointTriple openEndpoint ≡ endpointTriple closedEndpoint → ⊥
endpointTriplesDiffer ()

------------------------------------------------------------------------
-- Reuse prior NDim donor instead of replacing it.
------------------------------------------------------------------------

ndimDonor : NDim.AdKNDimGeometricBoundary
ndimDonor = NDim.canonicalAdKNDimGeometricBoundary

------------------------------------------------------------------------
-- Attribution-wrapped numeric atoms.
------------------------------------------------------------------------

openDLnAtom : Attr.CalibrationAtomEnvelope
openDLnAtom = DLn.openEndpointDLnAtom

closedDLnAtom : Attr.CalibrationAtomEnvelope
closedDLnAtom = DLn.closedEndpointDLnAtom

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data EndpointTripleDeterminesTransitionPath : Set where
data EndpointTripleCreatesIntermediateStateTable : Set where
data ApproximateCoordinatesBecomeExactPhysicalTruth : Set where
data SameThreeCoordinateSchemaCreatesSameStateIdentity : Set where

endpointTripleDoesNotDeterminePath : EndpointTripleDeterminesTransitionPath → ⊥
endpointTripleDoesNotDeterminePath ()

endpointTripleDoesNotCreateIntermediateTable : EndpointTripleCreatesIntermediateStateTable → ⊥
endpointTripleDoesNotCreateIntermediateTable ()

approximateCoordinatesDoNotBecomeExactTruth : ApproximateCoordinatesBecomeExactPhysicalTruth → ⊥
approximateCoordinatesDoNotBecomeExactTruth ()

sameCoordinateSchemaDoesNotCreateStateIdentity : SameThreeCoordinateSchemaCreatesSameStateIdentity → ⊥
sameCoordinateSchemaDoesNotCreateStateIdentity ()

record SourcePaidThreeCVEndpointBoundary : Set where
  constructor source-paid-three-cv-endpoint-boundary
  field
    sourcePaysAllThreeEndpointCoordinates : Bool
    openTriplePaid : Bool
    closedTriplePaid : Bool
    dLnAddsRealThirdCoordinate : Bool
    articleDoiRetained : Bool
    articleQidResolved : Bool
    pdbDoisRetained : Bool
    uniprotRetained : Bool
    adkQidRetained : Bool
    endpointTripleDeterminesTransitionPath : Bool
    endpointTripleCreatesIntermediateStateTable : Bool
    approximateCoordinatesPromotedToExactPhysicalTruth : Bool
    threeCoordinatesEqualCompleteProteinState : Bool
open SourcePaidThreeCVEndpointBoundary public

canonicalSourcePaidThreeCVEndpointBoundary : SourcePaidThreeCVEndpointBoundary
canonicalSourcePaidThreeCVEndpointBoundary = source-paid-three-cv-endpoint-boundary
  true true true true
  true false true true true
  false false false false

sourcePaysAllThreeEndpointCoordinates : Bool
sourcePaysAllThreeEndpointCoordinates = true

endpointTripleDeterminesTransitionPath : Bool
endpointTripleDeterminesTransitionPath = false

endpointTripleCreatesIntermediateStateTable : Bool
endpointTripleCreatesIntermediateStateTable = false
