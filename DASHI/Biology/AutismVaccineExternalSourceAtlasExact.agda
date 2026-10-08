module DASHI.Biology.AutismVaccineExternalSourceAtlasExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- ATTRIBUTED SOURCE ATLAS
--
-- Transcript ownership, quoted historical claims, investigative reporting and
-- independent scientific evidence remain separate source objects.  Atlas
-- membership records provenance only; it does not import theorem truth,
-- agreement, causal authority or clinical recommendation.
------------------------------------------------------------------------

oct2026TranscriptSource : Source.AttributedSource
oct2026TranscriptSource =
  Source.mkNoDOISource
    "unidentified speaker in user-supplied transcript"
    "transcript-2026-10-03.srt"
    "user-supplied SRT transcript"
    "2026"
    ""
    Source.archivalSource
    "Primary source for the October-2026 claims. Speaker identity is not inferred."
    Source.existenceOnlyAttribution

hbomberguyMeasuredResponseSource : Source.AttributedSource
hbomberguyMeasuredResponseSource =
  Source.mkNoDOISource
    "Hbomberguy (Harry Brewis)"
    "Vaccines and Autism: A Measured Response"
    "user-supplied transcript of published video essay"
    "2021"
    ""
    Source.archivalSource
    "Primary source for Hbomberguy's narration and for quotations embedded in the supplied transcript. Quoted speakers retain their own claim ownership."
    Source.publicAttribution

hviid2019Source : Source.AttributedSource
hviid2019Source =
  Source.mkDOISource
    "Anders Hviid; Jørgen Vinsløv Hansen; Morten Frisch; Mads Melbye"
    "Measles, Mumps, Rubella Vaccination and Autism: A Nationwide Cohort Study"
    "Annals of Internal Medicine 170(8):513-520"
    "2019"
    "10.7326/M18-2101"
    "https://doi.org/10.7326/M18-2101"
    Source.academicArticleSource
    "Pays the nationwide Danish cohort no-association result for MMR vaccination and autism within the studied population/design. It does not create a universal zero-risk theorem for every vaccine/outcome."
    Source.publicAttribution

cochrane2020Source : Source.AttributedSource
cochrane2020Source =
  Source.mkDOISource
    "Vittorio Demicheli; Alessandro Rivetti; Maria Grazia Debalini; Carlo Di Pietrantonj"
    "Vaccines for measles, mumps, rubella, and varicella in children"
    "Cochrane Database of Systematic Reviews"
    "2020"
    "10.1002/14651858.CD004407.pub4"
    "https://doi.org/10.1002/14651858.CD004407.pub4"
    Source.academicArticleSource
    "Pays review-level vaccine effectiveness/safety findings, including no evidence of increased autism risk in the included MMR evidence. Scope remains review- and outcome-specific."
    Source.publicAttribution

bmjRetractionReport2010Source : Source.AttributedSource
bmjRetractionReport2010Source =
  Source.mkDOISource
    "Clare Dyer"
    "Lancet retracts Wakefield's MMR paper"
    "BMJ 340:c696"
    "2010"
    "10.1136/bmj.c696"
    "https://doi.org/10.1136/bmj.c696"
    Source.academicArticleSource
    "Pays the reported 2010 Lancet retraction and GMC-context record. Retraction status is not itself the population causal estimate."
    Source.publicAttribution

bmjFraud2011Source : Source.AttributedSource
bmjFraud2011Source =
  Source.mkDOISource
    "Fiona Godlee; Jane Smith; Harvey Marcovitch"
    "Wakefield's article linking MMR vaccine and autism was fraudulent"
    "BMJ 342:c7452"
    "2011"
    "10.1136/bmj.c7452"
    "https://doi.org/10.1136/bmj.c7452"
    Source.academicArticleSource
    "Pays BMJ's fraud characterization and the distinction between scientific/ethical defects and later investigative evidence. It does not substitute for epidemiologic no-association evidence."
    Source.publicAttribution

nyhan2014Source : Source.AttributedSource
nyhan2014Source =
  Source.mkDOISource
    "Brendan Nyhan; Jason Reifler; Sean Richey; Gary L Freed"
    "Effective messages in vaccine promotion: a randomized trial"
    "Pediatrics 133(4):e835-e842"
    "2014"
    "10.1542/peds.2013-2365"
    "https://doi.org/10.1542/peds.2013-2365"
    Source.academicArticleSource
    "Pays the 1,759-parent randomized survey experiment and its message-specific outcomes. It does not establish a universal misinformation-backfire law."
    Source.publicAttribution

swireThompson2022Source : Source.AttributedSource
swireThompson2022Source =
  Source.mkDOISource
    "Briony Swire-Thompson; Nicholas Miklaucic; John P Wihbey; David Lazer; Joseph DeGutis"
    "The backfire effect after correcting misinformation is strongly associated with reliability"
    "Journal of Experimental Psychology: General 151(7):1655-1665"
    "2022"
    "10.1037/xge0001131"
    "https://doi.org/10.1037/xge0001131"
    Source.academicArticleSource
    "Pays evidence against a general correction-backfire effect in the tested items/designs, while retaining reliability/context qualifications."
    Source.publicAttribution

canonicalAutismVaccineSources : List Source.AttributedSource
canonicalAutismVaccineSources =
  oct2026TranscriptSource ∷ hbomberguyMeasuredResponseSource ∷
  hviid2019Source ∷ cochrane2020Source ∷ bmjRetractionReport2010Source ∷
  bmjFraud2011Source ∷ nyhan2014Source ∷ swireThompson2022Source ∷ []

canonicalAutismVaccineSourceAtlas : Source.AttributedSourceAtlas
canonicalAutismVaccineSourceAtlas =
  Source.mkSourceAtlas
    "Autism / vaccine / persuasion attributed source atlas"
    "DASHI.Biology.AutismVaccineExternalSourceAtlasExact"
    canonicalAutismVaccineSources
    "Claim-relative provenance for the two user-supplied transcripts and independent corroborating sources. Attribution never promotes a source claim into truth, causality, diagnosis or recommendation."

canonicalAtlasDoesNotCreateAuthority :
  Source.atlasCreatesAuthority canonicalAutismVaccineSourceAtlas ≡ false
canonicalAtlasDoesNotCreateAuthority = refl
