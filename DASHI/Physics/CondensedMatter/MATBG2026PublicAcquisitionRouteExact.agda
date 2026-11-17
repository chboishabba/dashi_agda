module DASHI.Physics.CondensedMatter.MATBG2026PublicAcquisitionRouteExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PUBLIC ACQUISITION ROUTES FOR THE TWO 2026 MATBG STUDIES
--
-- This module records first-party / publisher / public-repository routes only.
-- A route existing is not the same as possessing the bytes, replaying them, or
-- establishing same-sample identity across the two studies.
--
-- PMC changed its dataset-distribution infrastructure in August 2026. Article
-- identity/full-text availability is therefore kept separate from both the
-- retired legacy OA Web Service/package mechanism and the current PMC Cloud
-- Service route class.  A supported route class does not prove that the exact
-- MATBG supplement payload has been located in that service.
------------------------------------------------------------------------

record PublicAcquisitionRoute : Set where
  constructor public-acquisition-route
  field
    sourceDOI : String
    sourceOwner : String
    routeKind : String
    routeIdentifier : String
    routeRole : String
    routeObserved : Bool
    experimentalBytesAcquiredHere : Bool
    routeCreatesSameSampleIdentity : Bool

open PublicAcquisitionRoute public

xiaoNaturePublisherRoute : PublicAcquisitionRoute
xiaoNaturePublisherRoute = public-acquisition-route
  "10.1038/s41586-026-10378-x"
  "Xiao et al."
  "publisher"
  "Nature article/source-data surface"
  "paper states displayed data are provided with the paper; further plot/analysis data on request"
  true false false

xiaoPMCRoute : PublicAcquisitionRoute
xiaoPMCRoute = public-acquisition-route
  "10.1038/s41586-026-10378-x"
  "Xiao et al."
  "public full-text repository"
  "PMC13149035"
  "open-access article identity and associated-data metadata; not a guarantee of deposited QTM numerical arrays, legacy OA package availability, or exact Cloud Service payload membership"
  true false false

xiaoNIMSMDRRoute : PublicAcquisitionRoute
xiaoNIMSMDRRoute = public-acquisition-route
  "10.1038/s41586-026-10378-x"
  "Xiao et al.; NIMS hosts the repository route for its authors"
  "institutional materials-data repository route"
  "SAMURAI article 33032dbe-e3ab-4528-80b0-5ac13062ab74 -> NIMS Materials Data Repository surface"
  "SAMURAI explicitly advertises fulltext and dataset(s) on MDR; exact experimental-array deposit remains unconfirmed"
  true false false

zhangNaturePublisherRoute : PublicAcquisitionRoute
zhangNaturePublisherRoute = public-acquisition-route
  "10.1038/s41467-026-76179-y"
  "Zhang et al."
  "publisher"
  "Nature Communications Source Data 1-4"
  "publisher exposes four Source Data XLSX downloads"
  true false false

zhangPMCRoute : PublicAcquisitionRoute
zhangPMCRoute = public-acquisition-route
  "10.1038/s41467-026-76179-y"
  "Zhang et al."
  "public full-text repository"
  "PMC13575161"
  "open-access article identity and data-availability metadata; workbook bytes and exact Cloud Service payload membership remain separate acquisition claims"
  true false false

record MATBGPublicAcquisitionBoundary : Set where
  constructor matbg-public-acquisition-boundary
  field
    xiaoPublisherRoutePaid : Bool
    xiaoPMCRoutePaid : Bool
    xiaoNIMSMDRRoutePaid : Bool
    zhangPublisherRoutePaid : Bool
    zhangPMCRoutePaid : Bool
    pmcArticleIdentityRoutePaid : Bool
    legacyPMCOAPackageEndpointOperational : Bool
    currentPMCCloudServiceSupported : Bool
    exactMATBGCloudPayloadConfirmed : Bool
    pmcArticleIdentityCountsAsPayloadByteRoute : Bool
    firstPartyLiveRouteStillRequiredForBytes : Bool
    qtmExperimentalBytesPaid : Bool
    entropyExperimentalBytesPaid : Bool
    qtmExperimentalReplayPaid : Bool
    entropyExperimentalReplayPaid : Bool
    crossStudySameSamplePaid : Bool
    publicRouteDoesNotTransferDataOwnership : Bool
    publicRouteDoesNotCreateExperimentalAuthority : Bool

open MATBGPublicAcquisitionBoundary public

canonicalMATBGPublicAcquisitionBoundary : MATBGPublicAcquisitionBoundary
canonicalMATBGPublicAcquisitionBoundary =
  matbg-public-acquisition-boundary
    true true true true true
    true false true false false true
    false false false false false
    true true
