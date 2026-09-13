module DASHI.Culture.MaiwaldSURPActionSpectroscopyManifestationSuccessionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- JPL SURP PROJECT MANIFESTATION / PI-SURFACE SUCCESSION
--
-- Same project title and poster number family are useful continuity clues, but
-- each yearly JPL manifestation has its own displayed personnel. Project-title
-- continuity is not raw-data custody, role handover, authorship inheritance or
-- same-byte identity.
------------------------------------------------------------------------

record SURPManifestation : Set where
  constructor surp-manifestation
  field
    year : String
    title : String
    displayedPI : String
    displayedCollaborators : String
    posterURL : String
    publicManifestationPaid : Bool

open SURPManifestation public

surp2023Maiwald : SURPManifestation
surp2023Maiwald = surp-manifestation
  "2023"
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  "Frank W. Maiwald"
  "Robert P. Hodyss; Mathias Weber; Lane Terry"
  "https://www.jpl.nasa.gov/site/research/media/posters/2023/SP23012p.pdf"
  true

surp2024Nemchick : SURPManifestation
surp2024Nemchick = surp-manifestation
  "2024"
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  "Deacon J. Nemchick"
  "Robert P. Hodyss; Mathias Weber; graduate participants Lane Terry and Maddie Klumb"
  "https://www.jpl.nasa.gov/site/research/media/posters/2024/SP23012p.pdf"
  true

surp2025Nemchick : SURPManifestation
surp2025Nemchick = surp-manifestation
  "2025"
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  "Deacon J. Nemchick"
  "Robert P. Hodyss; Mathias Weber"
  "https://www.jpl.nasa.gov/site/research/media/posters/2025/SP23012p.pdf"
  true

jplSURPIndexSource : Source.AttributedSource
jplSURPIndexSource = Source.mkNoDOISource
  "NASA Jet Propulsion Laboratory"
  "Strategic University Research Partnerships posters"
  "JPL Research Collaborations poster index"
  "2023-2025 manifestations"
  "https://www.jpl.nasa.gov/site/research/programs/posters/"
  Source.institutionalSource
  "Pays the year-specific displayed project title and personnel surfaces. The index shows Frank Maiwald as PI in 2023 and Deacon J. Nemchick as PI in 2024 and 2025. It does not by itself identify the administrative handover date, raw-data custody, grant reassignment, or causal reason for the personnel change."
  Source.publicAttribution

jplFY23PosterSource : Source.AttributedSource
jplFY23PosterSource = Source.mkNoDOISource
  "NASA Jet Propulsion Laboratory / Frank Maiwald et al."
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  "FY23 SURP poster SP23012; CL#23-5018; RPC#sp23012"
  "2023"
  "https://www.jpl.nasa.gov/site/research/media/posters/2023/SP23012p.pdf"
  Source.institutionalSource
  "Pays Maiwald as PI, named collaborators, active cryogenic ion-action-spectroscopy apparatus, operating ranges and the public biomarker/isomer-discrimination objective. It does not pay bulk-crystal structural imaging, NHI sample analysis or classified deployment."
  Source.publicAttribution

jplFY24PosterSource : Source.AttributedSource
jplFY24PosterSource = Source.mkNoDOISource
  "NASA Jet Propulsion Laboratory / Deacon J. Nemchick et al."
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  "FY24 SURP poster SP23012"
  "2024"
  "https://www.jpl.nasa.gov/site/research/media/posters/2024/SP23012p.pdf"
  Source.institutionalSource
  "Pays Nemchick as PI in the FY24 manifestation, Hodyss/Weber collaboration, continued cryogenic action-spectroscopy work and listed 2024 publication output including Frank Maiwald as coauthor. It does not prove exact raw-data or calibration custody transfer from Maiwald."
  Source.publicAttribution

sameProjectTitleAcrossYears : Bool
sameProjectTitleAcrossYears = true

piSurfaceChangesAfter2023 : Bool
piSurfaceChangesAfter2023 = true

piSurfaceChangePaysFormalRoleHandover : Bool
piSurfaceChangePaysFormalRoleHandover = false

projectContinuityPaysRawDataCustody : Bool
projectContinuityPaysRawDataCustody = false

postLossContinuationMayNominateSuccessionSearch : Bool
postLossContinuationMayNominateSuccessionSearch = true

record MaiwaldSURPSuccessionBoundary : Set where
  constructor maiwald-surp-succession-boundary
  field
    sameTitleEqualsSameBytes : Bool
    laterPIRewritesEarlierPI : Bool
    programmeContinuationEqualsRoleSuccessionReceipt : Bool
    laterPublicationMaySupportScientificContinuation : Bool
    exactHandoverStillRequiresAdministrativeOrCustodyRecord : Bool

canonicalMaiwaldSURPSuccessionBoundary : MaiwaldSURPSuccessionBoundary
canonicalMaiwaldSURPSuccessionBoundary =
  maiwald-surp-succession-boundary false false false true true
