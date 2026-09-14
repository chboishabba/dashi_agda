module DASHI.Law.SensibLawTasmanianColonialGenocideSourceBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.InstitutionalNormProductionExact as Norm

------------------------------------------------------------------------
-- TASMANIAN COLONIAL GENOCIDE — SOURCE BOUNDARY
--
-- Historical source fixture only.  It binds named scholarly/institutional
-- propositions without turning scholarship into a court judgment, collapsing
-- genocide into total biological extinction, or identifying this history with
-- Mabo/native-title doctrine or another colonial history merely because a
-- naturalisation mechanism can be compared structurally.
------------------------------------------------------------------------

rebeTaylorGenocideChapter : Source.AttributedSource
rebeTaylorGenocideChapter = Source.mkDOISource
  "Rebe Taylor"
  "Genocide in Van Diemen's Land (Tasmania), 1803–1871"
  "The Cambridge World History of Genocide, pp. 481–507"
  "2023"
  "10.1017/9781108765480.021"
  "https://www.cambridge.org/core/books/cambridge-world-history-of-genocide/genocide-in-van-diemens-land-tasmania-18031871/ED82A107B2C76801551EB3F51CA6179D"
  Source.academicChapterSource
  "Scholarly source whose published summary concludes that the British committed genocide in Tasmania with intent and identifies killings, child removals and conditions unconducive to sustaining life as acts meeting the 1948 Genocide Convention categories. This is historical scholarship, not a judicial finding in a litigated case."
  Source.publicAttribution

utasGenocideExplainer : Source.AttributedSource
utasGenocideExplainer = Source.mkNoDOISource
  "Kristyn Harman"
  "Explainer: the evidence for the Tasmanian genocide"
  "University of Tasmania"
  "2018"
  "https://www.utas.edu.au/about/news-and-stories/articles/2018/513-explainer-the-evidence-for-the-tasmanian-genocide"
  Source.institutionalSource
  "University historical explainer locating archival and historiographical evidence for genocide in Van Diemen's Land, including Lemkin's use of Tasmania as a case study and colonial military/paramilitary campaigns. Used as a scholarly locator and bounded secondary synthesis."
  Source.publicAttribution

utasWybalennaSource : Source.AttributedSource
utasWybalennaSource = Source.mkNoDOISource
  "University of Tasmania — Companion to Tasmanian History"
  "Wybalenna"
  "Companion to Tasmanian History"
  "2006"
  "https://www.utas.edu.au/library/companion_to_tasmanian_history/W/Wybalenna.htm"
  Source.institutionalSource
  "Historical reference for Wybalenna and the explicit correction that Truganini was wrongly recorded as the last Tasmanian Aborigine. Used only to block the colonial extinction narrative from being treated as proof that Palawa people ceased to exist."
  Source.publicAttribution

tasmanianColonialGenocideSources : List Source.AttributedSource
tasmanianColonialGenocideSources =
  rebeTaylorGenocideChapter ∷
  utasGenocideExplainer ∷
  utasWybalennaSource ∷
  []

tasmanianColonialGenocideAtlas : Source.AttributedSourceAtlas
tasmanianColonialGenocideAtlas = Source.mkSourceAtlas
  "Tasmanian colonial genocide source atlas"
  "DASHI.Law.SensibLawTasmanianColonialGenocideSourceBoundaryExact"
  tasmanianColonialGenocideSources
  "Named scholarship and University of Tasmania historical sources. Genocide scholarship, population survival, legal doctrine and cross-domain naturalisation remain separate source/query coordinates."

parentNormProductionBoundary : Norm.InstitutionalNormProductionBoundary
parentNormProductionBoundary = Norm.canonicalInstitutionalNormProductionBoundary

record TasmanianColonialGenocideBoundary : Set where
  constructor tasmanianColonialGenocideBoundary
  field
    parentNormProductionReused : Bool
    cambridgeGenocideScholarshipPaid : Bool
    utasHistoricalGenocideLocatorPaid : Bool
    truganiniLastTasmanianNarrativeCorrectedBySource : Bool
    genocideAutomaticallyRequiresTotalBiologicalExtinction : Bool
    colonialExtinctionNarrativeAutomaticallyProvesNoPalawaSurvivors : Bool
    historicalScholarshipAutomaticallyJudicialGenocideFinding : Bool
    genocideScholarshipAutomaticallyDeterminesIndividualCulpability : Bool
    tasmanianGenocideHistoryAutomaticallySameObjectAsMaboNativeTitleDoctrine : Bool
    tasmanianGenocideAutomaticallySameHistoricalEventAsOtherColonialGenocides : Bool
    citationAutomaticallyCreatesHistoricalAuthorityBeyondSource : Bool

open TasmanianColonialGenocideBoundary public

canonicalTasmanianColonialGenocideBoundary : TasmanianColonialGenocideBoundary
canonicalTasmanianColonialGenocideBoundary =
  tasmanianColonialGenocideBoundary
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false

data GenocideRequiresTotalBiologicalExtinction : Set where
data ExtinctionNarrativeProvesNoPalawaSurvivors : Set where
data HistoricalScholarshipIsJudicialFinding : Set where

genocideDoesNotRequireTotalBiologicalExtinction :
  GenocideRequiresTotalBiologicalExtinction → ⊥
genocideDoesNotRequireTotalBiologicalExtinction ()

extinctionNarrativeDoesNotProveNoPalawaSurvivors :
  ExtinctionNarrativeProvesNoPalawaSurvivors → ⊥
extinctionNarrativeDoesNotProveNoPalawaSurvivors ()

historicalScholarshipDoesNotBecomeJudicialFinding :
  HistoricalScholarshipIsJudicialFinding → ⊥
historicalScholarshipDoesNotBecomeJudicialFinding ()
