module DASHI.Culture.PowersPlantationParadiseMethodologySourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- SURROUNDING METHODOLOGY / SOTA SOURCE ATLAS
--
-- These sources extend the research method around the Powers lane.  They are
-- not retroactively attributed to Powers and do not create historical facts by
-- themselves.
------------------------------------------------------------------------

prest2023PublicTheatreSource : Source.AttributedSource
prest2023PublicTheatreSource =
  Source.mkDOISource
    "Julia Prest"
    "Public Theatre and the Enslaved People of Colonial Saint-Domingue"
    "Palgrave Macmillan"
    "2023"
    "10.1007/978-3-031-22691-5"
    "https://doi.org/10.1007/978-3-031-22691-5"
    Source.academicBookSource
    "book-length same-domain source for mitigated spectatorship, theatre-maker slave ownership, concealed enslaved contribution to theatre-making, and shifting revolutionary-era roles"
    Source.publicAttribution

prest2023MethodologySource : Source.AttributedSource
prest2023MethodologySource =
  Source.mkDOISource
    "Julia Prest, editor"
    "Colonial-Era Caribbean Theatre: Issues in Research, Writing and Methodology"
    "Liverpool University Press / JSTOR"
    "2023"
    "10.2307/jj.1866834"
    "https://doi.org/10.2307/jj.1866834"
    Source.academicBookSource
    "methodological source for archival gaps, travelling performers, military and non-theatre records, multilingual and trans-colonial work, and runaway-advertisement research; used as method guidance rather than Powers authority"
    Source.publicAttribution

prest2024ResponseSource : Source.AttributedSource
prest2024ResponseSource =
  Source.mkNoDOISource
    "Julia Prest"
    "Response to H-France Forum reviews of Public Theatre and the Enslaved People of Colonial Saint-Domingue"
    "H-France Forum 19(5)"
    "2024"
    "https://h-france.net/wp-content/uploads/2024/06/HFranceForum2024_Prest_5Response.pdf"
    Source.academicArticleSource
    "author response on archive silence, reading along and against the grain, scraps of trace evidence, and explicit modal language separating certain, probable, possible and informed speculation"
    Source.publicAttribution

row2024ReviewSource : Source.AttributedSource
row2024ReviewSource =
  Source.mkNoDOISource
    "Jennifer E. Row"
    "Review essay on Public Theatre and the Enslaved People of Colonial Saint-Domingue"
    "H-France Forum 19(5)"
    "2024"
    "https://h-france.net/wp-content/uploads/2024/05/HFranceForum2024_Prest_4Row.pdf"
    Source.academicArticleSource
    "review-level methodological prompt toward bodily capacity, disability, skill and the relation between exceptional ability and commodification; not primary Saint-Domingue evidence"
    Source.publicAttribution

sabee2024ReviewSource : Source.AttributedSource
sabee2024ReviewSource =
  Source.mkNoDOISource
    "Olivia Sabee"
    "Review essay on Public Theatre and the Enslaved People of Colonial Saint-Domingue"
    "H-France Forum 19(5)"
    "2024"
    "https://h-france.net/wp-content/uploads/2024/05/HFranceForum2024_Prest_2Sabee.pdf"
    Source.academicArticleSource
    "review-level source highlighting mitigated aural/visual spectatorship, revolutionary change and post-Saint-Domingue comparison to New Orleans and Charleston; comparative prompt, not automatic transport authority"
    Source.publicAttribution

prest2025DisabilitySource : Source.AttributedSource
prest2025DisabilitySource =
  Source.mkDOISource
    "Julia Prest"
    "Performing Disability in French Court Ballet"
    "Early Modern French Studies 47(1), 70-96"
    "2025"
    "10.1080/20563035.2025.2481036"
    "https://doi.org/10.1080/20563035.2025.2481036"
    Source.academicArticleSource
    "peer-reviewed methodological authority for Disability Studies questions in early-modern French performance, including sensory/physical disability, ableist performance conventions and embodied knowledge; seventeenth-century French court ballet, not Saint-Domingue evidence"
    Source.publicAttribution

freedomOnTheMoveSource : Source.AttributedSource
freedomOnTheMoveSource =
  Source.mkNoDOISource
    "Freedom on the Move project"
    "Freedom on the Move"
    "Cornell University and partner institutions"
    "2010s-2020s"
    "https://freedomonthemove.org/"
    Source.institutionalSource
    "digital-history methodological precedent for source-first transcription, advertiser/source separation, controlled metadata extraction, duplicate grouping and aggregate plus individual analysis of coercive newspaper advertisements; North-American precedent only, not Saint-Domingue evidence"
    Source.publicAttribution

allPowersMethodologySources : List Source.AttributedSource
allPowersMethodologySources =
  prest2023PublicTheatreSource
  ∷ prest2023MethodologySource
  ∷ prest2024ResponseSource
  ∷ row2024ReviewSource
  ∷ sabee2024ReviewSource
  ∷ prest2025DisabilitySource
  ∷ freedomOnTheMoveSource
  ∷ []

powersMethodologySourceAtlas : Source.AttributedSourceAtlas
powersMethodologySourceAtlas =
  Source.mkSourceAtlas
    "Powers empirical-methodology and digital-history source atlas"
    "DASHI.Culture.PowersPlantationParadiseMethodologySourceAtlasExact"
    allPowersMethodologySources
    "bounded method/source roles for archive reconstruction, enslaved-theatre research, sensory access, disability questions, trans-colonial comparison and coercive-advertisement data modelling"

powersMethodologySourceAtlasReceipt : Receipt.GenericReceipt
powersMethodologySourceAtlasReceipt =
  Source.attributedSourceAtlasReceipt
    powersMethodologySourceAtlas
    "agda -i . DASHI/Culture/PowersPlantationParadiseMethodologySourceAtlasExact.agda"

powersMethodologySourceAtlasNonPromoting :
  Receipt.promotesClaim powersMethodologySourceAtlasReceipt ≡ false
powersMethodologySourceAtlasNonPromoting = refl

record PowersMethodologySourceBoundary : Set where
  constructor powers-methodology-source-boundary
  field
    laterScholarshipRetroactivelyBecomesPowersClaim : Bool
    laterScholarshipRetroactivelyBecomesPowersClaimIsFalse :
      laterScholarshipRetroactivelyBecomesPowersClaim ≡ false
    methodologicalPrecedentCreatesSaintDomingueFact : Bool
    methodologicalPrecedentCreatesSaintDomingueFactIsFalse :
      methodologicalPrecedentCreatesSaintDomingueFact ≡ false
    disabilityMethodCreatesSaintDomingueAccessFact : Bool
    disabilityMethodCreatesSaintDomingueAccessFactIsFalse :
      disabilityMethodCreatesSaintDomingueAccessFact ≡ false
    coerciveAdvertisementEqualsNeutralBiography : Bool
    coerciveAdvertisementEqualsNeutralBiographyIsFalse :
      coerciveAdvertisementEqualsNeutralBiography ≡ false
    modalReconstructionMayPreserveUncertainty : Bool
    modalReconstructionMayPreserveUncertaintyIsTrue :
      modalReconstructionMayPreserveUncertainty ≡ true

canonicalPowersMethodologySourceBoundary : PowersMethodologySourceBoundary
canonicalPowersMethodologySourceBoundary =
  powers-methodology-source-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
