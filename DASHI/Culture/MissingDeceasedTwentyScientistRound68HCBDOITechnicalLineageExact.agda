module DASHI.Culture.MissingDeceasedTwentyScientistRound68HCBDOITechnicalLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.MissingDeceasedTwentyScientistRound67HCBMediaClaimSourceDependenceExact as R67

------------------------------------------------------------------------
-- ROUND 68: DOI-BEARING HCB TECHNICAL LINEAGE
--
-- A 2020 AIAA retrospective gives the exact HCB programme a DOI-bearing
-- technical carrier and explicitly places the AFRL-developed Mondaloy alloy
-- inside the programme's development/test history.  The acquired bibliographic
-- surface identifies six authors: Robert J. Jensen, Edward Coy, Phuoc Hai Tran,
-- Jamie Malak, Alan Sutton and Robert Bernstein.
--
-- This pays technical lineage and Mondaloy-within-HCB.  It does not pay a
-- McCasland personal programme-management, funding, review or task role; he is
-- not on the acquired author surface.  That bounded author-surface absence is
-- not a universal non-participation claim.
------------------------------------------------------------------------

hcbRetrospectiveDOI : String
hcbRetrospectiveDOI = "10.2514/6.2020-3833"

hcbRetrospective : Attribution.AttributedSource
hcbRetrospective = Attribution.mkDOISource
  "Robert J. Jensen; Edward Coy; Phuoc Hai Tran; Jamie Malak; Alan Sutton; Robert Bernstein"
  "Key Achievements of Hydrocarbon Boost Technology Demonstrator Program"
  "AIAA Propulsion and Energy 2020 Forum / AIAA Conference Proceedings"
  "2020"
  hcbRetrospectiveDOI
  "https://doi.org/10.2514/6.2020-3833"
  Attribution.academicArticleSource
  "Pays a DOI-bearing HCB retrospective, named technical authors, the 13-year HCB technical-development lineage, and explicit Mondaloy demonstration within HCB; does not identify William N. McCasland as an author, programme manager, reviewer or funding decision-maker."
  Attribution.publicAttribution

jglobalHCBMirror : Attribution.AttributedSource
jglobalHCBMirror = Attribution.mkNoDOISource
  "JST J-GLOBAL"
  "Key Achievements of Hydrocarbon Boost Technology Demonstrator Program — bibliographic record"
  "J-GLOBAL scientific and technical literature index; JGLOBAL_ID 202002211808756155"
  "2020"
  "https://jglobal.jst.go.jp/detail?JGLOBAL_ID=202002211808756155"
  (Attribution.namedSourceKind "independent bibliographic index")
  "Independently mirrors title, six-author list, venue and HCB/Mondaloy abstract metadata; does not create independent experimental confirmation or a McCasland role."
  Attribution.publicAttribution

hcbRetrospectiveAuthorCount : Nat
hcbRetrospectiveAuthorCount = 6

hcbRetrospectivePaysMondaloyWithinHCB : Bool
hcbRetrospectivePaysMondaloyWithinHCB = true

hcbRetrospectivePaysThirteenYearTechnicalLineage : Bool
hcbRetrospectivePaysThirteenYearTechnicalLineage = true

hcbRetrospectiveNamesMcCaslandPaid : Bool
hcbRetrospectiveNamesMcCaslandPaid = false

hcbRetrospectiveNamesRezaPaid : Bool
hcbRetrospectiveNamesRezaPaid = false

jglobalIndependentBibliographicMirrorPaid : Bool
jglobalIndependentBibliographicMirrorPaid = true

technicalLineageDoesNotPayManagementRole : Bool
technicalLineageDoesNotPayManagementRole = true

doiCarrierDoesNotCreateMissingAuthor : Bool
doiCarrierDoesNotCreateMissingAuthor = true

authorSurfaceNoHitDoesNotPayUniversalNonParticipation : Bool
authorSurfaceNoHitDoesNotPayUniversalNonParticipation = true

primaryTechnicalAuthorsDoNotTransferProgrammeManagement : Bool
primaryTechnicalAuthorsDoNotTransferProgrammeManagement = true

hcbExactObjectNowStronglyIdentified : Bool
hcbExactObjectNowStronglyIdentified = true

mccaslandIdentityBearingManagementCarrierStillRequired : Bool
mccaslandIdentityBearingManagementCarrierStillRequired = true

round68H2PaidCount : Nat
round68H2PaidCount = 0

round68H3PaidCount : Nat
round68H3PaidCount = 0

round68Reading : String
round68Reading = "The HCB branch now has a DOI-bearing exact technical retrospective: AIAA 2020-3833 / DOI 10.2514/6.2020-3833. It explicitly places AFRL-developed Mondaloy inside the 13-year HCB technical-development history and identifies six technical authors. William N. McCasland and Monica Jacinto/Reza are not named on the acquired author surface. That bounded absence does not prove non-participation, but it confirms that programme existence, Mondaloy lineage and technical authorship are no longer the live debt. The remaining H2-critical debt is an identity-bearing management/task/review/funding carrier naming McCasland on the exact HCB/Mondaloy object."
