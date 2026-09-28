module DASHI.Analysis.RiemannSSP15FilteredProvenanceCapstoneExact where

------------------------------------------------------------------------
-- RH FILTERED PROVENANCE / SSP15 CAPSTONE
--
-- What is paid:
--
-- * the bare integer row has explicit Smith form (1,0,0,0);
-- * the raw depth tuple (0,5,5,5) is not GL_4(Z)-invariant;
-- * the mod-3^5 kernel is the preferred transported filtered object;
-- * a guarded 5 x 3 RH-role / SSP15 internal-lane codec is exact;
-- * the pointed signed layer preserves provenance that zero valuation erases;
-- * the chosen 5 x 3 grid is transverse to both CM splitting and the
--   prime-native nonary complement observer.
--
-- What remains:
--
-- A PRODUCER-SIDE SAME-OBJECT certificate identifying four actual analytic
-- coordinates whose primitive-row coefficients are exactly
--
--   pole   -> 80
--   origin -> 243
--   j      -> 1215
--   s      -> 972.
--
-- Only such a certificate licenses treating the O/j/s depth-five roles as
-- analytic provenance rather than a repository indexing choice.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Analysis.RiemannPrimitiveKernelSmithFiltrationSeparationExact as Smith
import DASHI.Analysis.RiemannSSP15DepthFiveRoleCodecExact as Codec
import DASHI.Analysis.RiemannSSP15SignedProvenanceBridgeExact as Signed
import DASHI.Analysis.RiemannSSP15PartitionSeparationExact as Partition
import DASHI.Analysis.RiemannSSP15ChosenGridTransversalityExact as Transverse
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Nonary
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as Internal
import DASHI.Analysis.RiemannSSP15RHProducerDonorManifestExact as Donor
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as Branch

------------------------------------------------------------------------
-- 1. Producer-side role authority socket.
------------------------------------------------------------------------

record PrimitiveRowProducerRoleCertificate : Set₁ where
  constructor primitive-row-producer-role-certificate
  field
    ProducerCoordinate : Set

    poleCoordinate : ProducerCoordinate
    originCoordinate : ProducerCoordinate
    jCoordinate : ProducerCoordinate
    sCoordinate : ProducerCoordinate

    coefficientOf : ProducerCoordinate -> Nat

    poleCoefficientExact :
      coefficientOf poleCoordinate ≡ 80

    originCoefficientExact :
      coefficientOf originCoordinate ≡ 243

    jCoefficientExact :
      coefficientOf jCoordinate ≡ 1215

    sCoefficientExact :
      coefficientOf sCoordinate ≡ 972

    sourceOwner : String

open PrimitiveRowProducerRoleCertificate public

depthFiveProducerCoordinate :
  (certificate : PrimitiveRowProducerRoleCertificate) ->
  Codec.RHDepthFiveRole ->
  ProducerCoordinate certificate
depthFiveProducerCoordinate certificate Codec.originRole =
  originCoordinate certificate
depthFiveProducerCoordinate certificate Codec.jRole =
  jCoordinate certificate
depthFiveProducerCoordinate certificate Codec.sRole =
  sCoordinate certificate

depthFiveProducerCoefficient :
  (certificate : PrimitiveRowProducerRoleCertificate) ->
  Codec.RHDepthFiveRole ->
  Nat
depthFiveProducerCoefficient certificate role =
  coefficientOf certificate
    (depthFiveProducerCoordinate certificate role)

depthFiveOriginCoefficientExact :
  (certificate : PrimitiveRowProducerRoleCertificate) ->
  depthFiveProducerCoefficient certificate Codec.originRole ≡ 243
depthFiveOriginCoefficientExact =
  originCoefficientExact

depthFiveJCoefficientExact :
  (certificate : PrimitiveRowProducerRoleCertificate) ->
  depthFiveProducerCoefficient certificate Codec.jRole ≡ 1215
depthFiveJCoefficientExact =
  jCoefficientExact

depthFiveSCoefficientExact :
  (certificate : PrimitiveRowProducerRoleCertificate) ->
  depthFiveProducerCoefficient certificate Codec.sRole ≡ 972
depthFiveSCoefficientExact =
  sCoefficientExact

------------------------------------------------------------------------
-- 2. Conditional producer-marked SSP15 code.
------------------------------------------------------------------------

record ProducerMarkedSSP15Code
    (certificate : PrimitiveRowProducerRoleCertificate) : Set where
  constructor producer-marked-ssp15-code
  field
    mode : Nonary.ComplementMode5
    role : Codec.RHDepthFiveRole

    producerCoordinate :
      ProducerCoordinate certificate

    producerCoordinateIsRoleCoordinate :
      producerCoordinate
      ≡ depthFiveProducerCoordinate certificate role

open ProducerMarkedSSP15Code public

canonicalProducerMarkedCode :
  (certificate : PrimitiveRowProducerRoleCertificate) ->
  Nonary.ComplementMode5 ->
  Codec.RHDepthFiveRole ->
  ProducerMarkedSSP15Code certificate
canonicalProducerMarkedCode certificate mode role =
  producer-marked-ssp15-code
    mode
    role
    (depthFiveProducerCoordinate certificate role)
    refl

eraseProducerMark :
  {certificate : PrimitiveRowProducerRoleCertificate} ->
  ProducerMarkedSSP15Code certificate ->
  Codec.RHSSP15RoleCode
eraseProducerMark code =
  mode code , role code

compileProducerMarkedToInternalLane :
  {certificate : PrimitiveRowProducerRoleCertificate} ->
  ProducerMarkedSSP15Code certificate ->
  Internal.SSP15InternalLane
compileProducerMarkedToInternalLane code =
  Codec.encodeRoleCode (eraseProducerMark code)

compileProducerMarkedToPointedSigned :
  {certificate : PrimitiveRowProducerRoleCertificate} ->
  ProducerMarkedSSP15Code certificate ->
  Branch.PointedSignedSSPLane
compileProducerMarkedToPointedSigned code =
  Signed.roleCodeToPointedSigned (eraseProducerMark code)

producerMarkedRoundTripAtRoleCode :
  (certificate : PrimitiveRowProducerRoleCertificate) ->
  (mode : Nonary.ComplementMode5) ->
  (role : Codec.RHDepthFiveRole) ->
  Signed.pointedSignedToRoleCode
    (compileProducerMarkedToPointedSigned
      (canonicalProducerMarkedCode certificate mode role))
  ≡
  (mode , role)
producerMarkedRoundTripAtRoleCode certificate mode role =
  Signed.roleCodePointedRoundTrip (mode , role)

------------------------------------------------------------------------
-- 3. Existing structural payments reused.
------------------------------------------------------------------------

bareSmithInvariantOneOwned : Bool
bareSmithInvariantOneOwned = true

rawDepthTupleBasisInvariant : Bool
rawDepthTupleBasisInvariant = false

filteredKernelPreferred : Bool
filteredKernelPreferred = true

roleCodecFifteenOwned : Bool
roleCodecFifteenOwned = true

chosenGridTransverseToCMAndNativeObservers : Bool
chosenGridTransverseToCMAndNativeObservers = true

------------------------------------------------------------------------
-- 4. The source authority is intentionally not manufactured here.
------------------------------------------------------------------------

data RepositoryCodecAloneCreatesProducerCertificate : Set where

repositoryCodecDoesNotCreateProducerCertificate :
  RepositoryCodecAloneCreatesProducerCertificate -> ⊥
repositoryCodecDoesNotCreateProducerCertificate ()

record RiemannSSP15FilteredProvenanceBoundary : Set where
  constructor riemann-ssp15-filtered-provenance-boundary
  field
    primitiveSmithInvariantOnePaid : Bool
    rawDepthTupleBasisInvariantFlag : Bool
    filteredKernelPreferredFlag : Bool
    fiveByThreeRoleCodecPaid : Bool
    pointedSignedProvenancePaid : Bool
    partitionSeparationPaid : Bool
    chosenGridTransversalityPaid : Bool
    producerRoleCertificateTypeDefined : Bool
    sourceNativeProducerTheoremLocatedAndPinned : Bool
    sourceNativeFourCoordinateTermsLocated : Bool
    sourceNativeProducerCertificateInhabitedOnDonorBranch : Bool
    donorImportedIntoCurrentLeanSourceGraph : Bool
    producerRoleCertificateInhabitedHere : Bool
    rhDepthFiveRolesPromotedToAnalyticProvenanceHere : Bool

canonicalRiemannSSP15FilteredProvenanceBoundary :
  RiemannSSP15FilteredProvenanceBoundary
canonicalRiemannSSP15FilteredProvenanceBoundary =
  riemann-ssp15-filtered-provenance-boundary
    true false true true true true true true
    true true true false false false
