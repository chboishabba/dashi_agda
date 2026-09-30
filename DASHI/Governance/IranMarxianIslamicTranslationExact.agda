module DASHI.Governance.IranMarxianIslamicTranslationExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- IRANIAN MARXIAN / ISLAMIC REVOLUTIONARY TRANSLATION
--
-- Source genealogy:
--   * contemporary scholarship describes Ali Shariati as combining Marxist,
--     existentialist, Islamic and nationalist traditions;
--   * 2026 Iranian Studies describes Islamic-Republic ideology as blending
--     socialism, nationalism and Third Worldism and highlights mostazafin as
--     a global anti-colonial / anti-imperialist category.
--
-- Structural correspondence is not ideological identity.
------------------------------------------------------------------------

shariatiGlobalMarxism2026 : Source.AttributedSource
shariatiGlobalMarxism2026 = Source.mkDOISource
  "Simin Fadaee"
  "Ali Shariati: an international fighter"
  "Global Marxism: Decolonisation and revolutionary politics, chapter 8"
  "2026"
  "10.7765/9781526178008.00011"
  "https://www.cambridge.org/core/books/abs/global-marxism/ali-shariati-an-international-fighter/F164F29530633FA2183FEE7480ACD400"
  Source.academicChapterSource
  "source for the scholarly characterisation of Shariati's combination of Marxist, existentialist, Islamic and nationalist thought and a Marxian historical frame"
  Source.publicAttribution

glombitzaIranPalestine2026 : Source.AttributedSource
glombitzaIranPalestine2026 = Source.mkDOISource
  "Olivia Glombitza"
  "Continuity and Change in the Islamic Republic's Vision of Regional Order: The Palestinian Cause in Iranian Foreign Policy"
  "Iranian Studies 59(2)"
  "2026"
  "10.1017/irn.2025.10134"
  "https://www.cambridge.org/core/journals/iranian-studies/article/continuity-and-change-in-the-islamic-republics-vision-of-regional-order-the-palestinian-cause-in-iranian-foreign-policy/0CBFF61998C6010732B57A803DF3D9C9"
  Source.academicArticleSource
  "source for the scholarly account of Islamic-Republic ideology as a modern blend involving socialism, nationalism and Third Worldism, and for mostazafin/mostakberin anti-imperialist framing"
  Source.publicAttribution

shariatiSnowball : Snowball.SourceRoleSnowballReceipt shariatiGlobalMarxism2026
shariatiSnowball = Snowball.canonicalSourceRoleSnowballReceipt shariatiGlobalMarxism2026

glombitzaSnowball : Snowball.SourceRoleSnowballReceipt glombitzaIranPalestine2026
glombitzaSnowball = Snowball.canonicalSourceRoleSnowballReceipt glombitzaIranPalestine2026

data MarxianRole : Set where
  proletariatRole : MarxianRole
  capitalistClassRole : MarxianRole
  classSolidarityRole : MarxianRole
  imperialismRole : MarxianRole
  revolutionaryTransformationRole : MarxianRole

data IranianIslamicRole : Set where
  mostazafinRole : IranianIslamicRole
  mostakberinRole : IranianIslamicRole
  oppressedSolidarityRole : IranianIslamicRole
  estekbarHegemonyRole : IranianIslamicRole
  islamicRevolutionRole : IranianIslamicRole

data TranslationRelation : Set where
  homologousAntagonism : TranslationRelation
  translatedSolidarity : TranslationRelation
  translatedAntiImperialism : TranslationRelation
  transformedRevolutionarySubject : TranslationRelation

record StructuralTranslation : Set where
  constructor structural-translation
  field
    marxianSourceRole : MarxianRole
    iranianTargetRole : IranianIslamicRole
    relation : TranslationRelation
    sourceReceipt : String
    structuralCorrespondence : Bool
    ideologicalIdentity : Bool
    genealogicalDirectInfluenceProved : Bool

open StructuralTranslation public

proletariatToMostazafin : StructuralTranslation
proletariatToMostazafin = structural-translation
  proletariatRole mostazafinRole transformedRevolutionarySubject
  "Shariati / Islamic-Republic scholarly genealogy; correspondence is partial and historically mediated"
  true false false

capitalClassToMostakberin : StructuralTranslation
capitalClassToMostakberin = structural-translation
  capitalistClassRole mostakberinRole homologousAntagonism
  "oppressor-role analogy; mostakberin is theological-political and exceeds a Marxian ownership class"
  true false false

classSolidarityToOppressedSolidarity : StructuralTranslation
classSolidarityToOppressedSolidarity = structural-translation
  classSolidarityRole oppressedSolidarityRole translatedSolidarity
  "global solidarity of the oppressed is not definitionally proletarian internationalism"
  true false false

imperialismToEstekbar : StructuralTranslation
imperialismToEstekbar = structural-translation
  imperialismRole estekbarHegemonyRole translatedAntiImperialism
  "anti-imperialist structural resemblance with different normative ontology"
  true false false

data SameGrammarImpliesSameOntology : Set where
data StructuralCorrespondenceProvesDirectInfluence : Set where
data MostazafinEqualsProletariat : Set where
data MostakberinEqualsBourgeoisie : Set where

sameGrammarDoesNotForceSameOntology :
  SameGrammarImpliesSameOntology → ⊥
sameGrammarDoesNotForceSameOntology ()

correspondenceDoesNotProveDirectInfluence :
  StructuralCorrespondenceProvesDirectInfluence → ⊥
correspondenceDoesNotProveDirectInfluence ()

mostazafinNotDefinitionallyProletariat :
  MostazafinEqualsProletariat → ⊥
mostazafinNotDefinitionallyProletariat ()

mostakberinNotDefinitionallyBourgeoisie :
  MostakberinEqualsBourgeoisie → ⊥
mostakberinNotDefinitionallyBourgeoisie ()
