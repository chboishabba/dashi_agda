module DASHI.Education.DigitalESDTilburySourceRoleExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr

-- The 2002 case collection and the 2004 five-theme handbook are distinct
-- works. A thematic description of the first does not create individual
-- chapter-level evidence, and the latter's five themes must not be
-- retroactively attributed to every chapter of the first.
tilbury2002 : Attr.AttributedSource
tilbury2002 = Attr.mkNoDOISource
  "Daniella Tilbury; Robert B. Stevenson; John Fien; Danie Schreuder (editors)"
  "Education and Sustainability: Responding to the Global Challenge"
  "IUCN Commission on Education and Communication; ISBN 2-8317-0623-8"
  "2002"
  "https://iucn.org/resources/publication/education-and-sustainability-responding-global-challenge"
  Attr.academicBookSource
  "Edited case-study collection: multiple educational and community pathways. Book-level description is not chapter-specific outcome evidence."
  Attr.publicAttribution

tilburyWortman2004 : Attr.AttributedSource
tilburyWortman2004 = Attr.mkNoDOISource
  "Daniella Tilbury; David Wortman"
  "Engaging People in Sustainability"
  "IUCN Publication Services; ISBN 2831708230"
  "2004"
  "https://researchers.mq.edu.au/en/publications/engaging-people-in-sustainability/"
  Attr.academicBookSource
  "Explicit five-theme practice framework: imagining a better future; critical thinking/reflection; participation in decision-making; partnerships; systemic thinking."
  Attr.publicAttribution

data TilburyPractice2004 : Set where
  envisionFuture : TilburyPractice2004
  criticalReflect : TilburyPractice2004
  participatoryDecision : TilburyPractice2004
  partnerships : TilburyPractice2004
  systemicThinking : TilburyPractice2004

fiveThemes2004 : List TilburyPractice2004
fiveThemes2004 =
  envisionFuture ∷ criticalReflect ∷ participatoryDecision ∷
  partnerships ∷ systemicThinking ∷ []

-- The collection is intentionally open-ended: no universal method lookup.
data CasePathwayDeterminesUniversalIntervention : Set where
data BookDescriptionEstablishesChapterEffect : Set where
data Tilbury2004FrameworkIsTilbury2002ChapterResult : Set where

noUniversalPathway : CasePathwayDeterminesUniversalIntervention → ⊥
noUniversalPathway ()
noBookLevelEffectPromotion : BookDescriptionEstablishesChapterEffect → ⊥
noBookLevelEffectPromotion ()
noRetroactiveFrameworkAttribution : Tilbury2004FrameworkIsTilbury2002ChapterResult → ⊥
noRetroactiveFrameworkAttribution ()


tilburyEfSSourceAtlas : Attr.AttributedSourceAtlas
tilburyEfSSourceAtlas = Attr.mkSourceAtlas
  "Tilbury / IUCN Education for Sustainability historical sources"
  "DASHI.Education.DigitalESDTilburySourceRoleExact"
  (tilbury2002 ∷ tilburyWortman2004 ∷ [])
  "The 2002 IUCN collection provides book-level plural case pathways; the 2004 IUCN guide explicitly names five educational practice themes. Chapter-specific claims require separately acquired and reviewed spans; neither source establishes universal efficacy."
