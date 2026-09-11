module DASHI.Culture.AmyEskridgePOAMSRegisteredSTIAcquisitionRouteExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- AMY / POAMS REGISTERED-STI ACQUISITION ROUTE
--
-- NASA's current NTRS surface distinguishes publicly available content from
-- NTRS Registered Content, described by NASA as the complete STI collection for
-- authorized NASA users.  The public page also routes questions to the NASA STI
-- Information Desk.  This pays an acquisition route only: it does not establish
-- that the missing POAMS EDAA/NF-1676B object is present in registered content.
------------------------------------------------------------------------

record RegisteredSTIAcquisitionRoute : Set where
  constructor registered-sti-acquisition-route
  field
    targetPublicObject : String
    publicRepository : String
    registeredRepository : String
    nasaDescriptionOfRegisteredScope : String
    publicContactRoute : String
    centerRoutingContext : String
    nasaQid : String
    msfcQid : String
    deweyTraversal : String
    repeatedPublicSearchPerformed : Bool
    poamsSpecificEDAAFoundPublicly : Bool
    registeredContentMayContainTarget : Bool
    registeredContentProvesTargetExists : Bool
    publicSearchFailureProvesNoRecord : Bool
    nextAcquisition : String

open RegisteredSTIAcquisitionRoute public

poamsRegisteredSTIRoute : RegisteredSTIAcquisitionRoute
poamsRegisteredSTIRoute = registered-sti-acquisition-route
  "NASA/TM-20205010911 / M-1531 / NTRS 20205010911"
  "NASA Technical Reports Server public repository"
  "NASA STI Repository Registered Content / former NTRS-R"
  "NASA describes Registered Content as including the complete STI collection and restricting access to authorized NASA civil servants, contractors and grantees"
  "NASA STI Information Desk"
  "MSFC Propulsion Systems Department / Engineering Directorate -> STI Compliance and Distribution Services"
  "Q23548"
  "Q618696"
  "530 Physics / 629 Engineering traversal only"
  true false true false false
  "request/search POAMS-specific EDAA/NF-1676B metadata through the NASA STI Information Desk and MSFC STI compliance/distribution route, keyed by M-1531, NTRS 20205010911, title, authors, SAA8-1519855 and funding MSFC-RMB-QUANTUM-SAA8-1519855-1; require attached-object/version and Amy-linked same-object receipts before promotion"

record RegisteredSTIBoundary : Set where
  constructor registered-sti-boundary
  field
    completeCollectionDescriptionImpliesSpecificEDAAExists : Bool
    restrictedAccessImpliesSuppression : Bool
    publicSearchFailureImpliesDeletion : Bool
    registeredRouteMayGuideTargetedAcquisition : Bool

open RegisteredSTIBoundary public

canonicalRegisteredSTIBoundary : RegisteredSTIBoundary
canonicalRegisteredSTIBoundary = registered-sti-boundary false false false true
