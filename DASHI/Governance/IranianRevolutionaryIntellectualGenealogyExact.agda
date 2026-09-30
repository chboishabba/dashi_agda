module DASHI.Governance.IranianRevolutionaryIntellectualGenealogyExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- IRANIAN REVOLUTIONARY INTELLECTUAL GENEALOGY
--
-- Stronger than lexical analogy, weaker than invented person-to-person
-- influence.  Edges below are typed by what the cited historical scholarship
-- actually supports.
------------------------------------------------------------------------

matinAsgari2018 : Source.AttributedSource
matinAsgari2018 = Source.mkDOISource
  "Afshin Matin-Asgari"
  "Both Eastern and Western: An Intellectual History of Iranian Modernity"
  "Cambridge University Press"
  "2018"
  "10.1017/9781108552844"
  "https://www.cambridge.org/core/books/both-eastern-and-western/0100CFAFFDCE8B0F57E261AEFBC4ADCB"
  Source.academicBookSource
  "intellectual-history source for socialist hegemony, political Shi'ism, Islamic Marxism and the globally interactive formation of modern Iranian thought"
  Source.publicAttribution

boroujerdiModernizingIslam : Source.AttributedSource
boroujerdiModernizingIslam = Source.mkDOISource
  "Mehrzad Boroujerdi"
  "Islam as a modernizing ideology: Al-e Ahmad and Shari'ati"
  "Intellectual Discourse and the Politics of Modernization: Negotiating Modernity in Iran, chapter 4"
  "2000"
  "10.1017/CBO9780511489242.005"
  "https://www.cambridge.org/core/books/abs/intellectual-discourse-and-the-politics-of-modernization/islam-as-a-modernizing-ideology-ale-ahmad-and-shariati/7AB233BCA3B40A7E7A7EB4655C37B916"
  Source.academicChapterSource
  "supports that Shariati drew liberally from Marxism to construct a populist activist Islam within a project of Iranian national liberation"
  Source.publicAttribution

gouldFanonShariati2024 : Source.AttributedSource
gouldFanonShariati2024 = Source.mkNoDOISource
  "Rebecca Ruth Gould"
  "Religion and Revolution: Ali Shariati's Recreation of Fanon for an Iranian Audience"
  "POMEPS Studies 53: Frantz Fanon in the Middle East"
  "2024"
  "https://pomeps.org/religion-and-revolution-ali-shariatis-recreation-of-fanon-for-an-iranian-audience"
  Source.academicChapterSource
  "supports Fanon as a major inspiration and template in Shariati's anti-colonial self-conception while preserving uncertainty around claimed personal correspondence and translation provenance"
  Source.publicAttribution

saffariBeyondShariati2017 : Source.AttributedSource
saffariBeyondShariati2017 = Source.mkNoDOISource
  "Siavash Saffari"
  "Beyond Shariati: Modernity, Cosmopolitanism, and Islam in Iranian Political Thought"
  "Cambridge University Press"
  "2017"
  "https://www.cambridge.org/core/books/beyond-shariati/450299E58ECC483475FD8EA829F02B59"
  Source.academicBookSource
  "supports Shariati's combination of Islamic political thought and left-leaning ideology and his influence on many members of the revolutionary generation"
  Source.publicAttribution

khomeiniWest2014 : Source.AttributedSource
khomeiniWest2014 = Source.mkNoDOISource
  "Mehran Kamrava"
  "Khomeini and the West"
  "A Critical Introduction to Khomeini, chapter 6"
  "2014"
  "https://www.cambridge.org/core/books/abs/critical-introduction-to-khomeini/khomeini-and-the-west/41E5A25E505AC13DC5B78BC9676BC01E"
  Source.academicChapterSource
  "supports that Khomeini's anti-West discourse was not a radical departure from the Iranian Left's existing view of Western neocolonial domination and the Third World"
  Source.publicAttribution

hansonWestoxication1983 : Source.AttributedSource
hansonWestoxication1983 = Source.mkNoDOISource
  "Brad Hanson"
  "The Westoxication of Iran: Depictions and Reactions of Behrangi, Al-e Ahmad, and Shariati"
  "International Journal of Middle East Studies 15(1):1-23"
  "1983"
  "https://www.jstor.org/stable/162924"
  Source.academicArticleSource
  "supports Al-e Ahmad/Shariati Westoxication critique and its relation to Third-World dependency-style analysis; not a proof that Iranian thought copied one named dependency theorist"
  Source.publicAttribution

data GenealogyNode : Set where
  marxianLeftField : GenealogyNode
  fanonianAnticolonialField : GenealogyNode
  iranianThirdWorldistField : GenealogyNode
  alEAhmadWestoxicationField : GenealogyNode
  shariatiIslamicRevolutionarySynthesis : GenealogyNode
  iranianRevolutionaryGeneration : GenealogyNode
  khomeiniAntiWestRevolutionaryDiscourse : GenealogyNode
  islamicRepublicRevolutionaryGrammar : GenealogyNode

data EdgeStrength : Set where
  directTextualInfluence : EdgeStrength
  documentedIntellectualInfluence : EdgeStrength
  fieldLevelContinuity : EdgeStrength
  structuralConvergence : EdgeStrength

record GenealogyEdge : Set where
  constructor genealogy-edge
  field
    from : GenealogyNode
    to : GenealogyNode
    strength : EdgeStrength
    source : Source.AttributedSource
    receipt : String
    establishesPersonalInfluence : Bool
    establishesExactConceptIdentity : Bool

open GenealogyEdge public

fanonToShariati : GenealogyEdge
fanonToShariati = genealogy-edge
  fanonianAnticolonialField
  shariatiIslamicRevolutionarySynthesis
  documentedIntellectualInfluence
  gouldFanonShariati2024
  "Fanon functioned as a major inspiration/template for Shariati; disputed personal-correspondence details remain outside the edge"
  false false

marxianFieldToShariati : GenealogyEdge
marxianFieldToShariati = genealogy-edge
  marxianLeftField
  shariatiIslamicRevolutionarySynthesis
  documentedIntellectualInfluence
  boroujerdiModernizingIslam
  "Shariati drew liberally from Marxism in constructing activist Islam"
  false false

thirdWorldismToShariati : GenealogyEdge
thirdWorldismToShariati = genealogy-edge
  iranianThirdWorldistField
  shariatiIslamicRevolutionarySynthesis
  fieldLevelContinuity
  matinAsgari2018
  "Shariati is situated inside the wider Iranian socialist / Third-Worldist / Islamic-Marxist intellectual field"
  false false

shariatiToRevolutionaryGeneration : GenealogyEdge
shariatiToRevolutionaryGeneration = genealogy-edge
  shariatiIslamicRevolutionarySynthesis
  iranianRevolutionaryGeneration
  documentedIntellectualInfluence
  saffariBeyondShariati2017
  "Shariati inspired many in the revolutionary generation"
  false false

iranianLeftToKhomeiniWestGrammar : GenealogyEdge
iranianLeftToKhomeiniWestGrammar = genealogy-edge
  marxianLeftField
  khomeiniAntiWestRevolutionaryDiscourse
  fieldLevelContinuity
  khomeiniWest2014
  "Khomeini's West/neocolonial grammar substantially overlapped an already established Iranian-left discourse"
  false false

westoxicationToThirdWorldistField : GenealogyEdge
westoxicationToThirdWorldistField = genealogy-edge
  alEAhmadWestoxicationField
  iranianThirdWorldistField
  structuralConvergence
  hansonWestoxication1983
  "Westoxication scholarship places the Iranian critique in a Third-World/dependency-style problem field without identifying one direct dependency-theory source"
  false false

canonicalFieldEdges : List GenealogyEdge
canonicalFieldEdges =
  fanonToShariati
  ∷ marxianFieldToShariati
  ∷ thirdWorldismToShariati
  ∷ shariatiToRevolutionaryGeneration
  ∷ iranianLeftToKhomeiniWestGrammar
  ∷ westoxicationToThirdWorldistField
  ∷ []

data ShariatiDirectlyDeterminesKhomeiniThought : Set where
data SharedRevolutionaryFieldImpliesPersonalInfluence : Set where
data WestoxicationEqualsDependencyTheory : Set where
data FanonShariatiCorrespondenceProvedByInfluence : Set where

shariatiDoesNotAutomaticallyDetermineKhomeini :
  ShariatiDirectlyDeterminesKhomeiniThought → ⊥
shariatiDoesNotAutomaticallyDetermineKhomeini ()

fieldContinuityDoesNotCreatePersonalInfluence :
  SharedRevolutionaryFieldImpliesPersonalInfluence → ⊥
fieldContinuityDoesNotCreatePersonalInfluence ()

westoxicationDoesNotDefinitionallyEqualDependencyTheory :
  WestoxicationEqualsDependencyTheory → ⊥
westoxicationDoesNotDefinitionallyEqualDependencyTheory ()

fanonInfluenceDoesNotProveDisputedCorrespondence :
  FanonShariatiCorrespondenceProvedByInfluence → ⊥
fanonInfluenceDoesNotProveDisputedCorrespondence ()

allGenealogySourcesSnowball :
  List (Snowball.SourceRoleSnowballReceipt boroujerdiModernizingIslam)
allGenealogySourcesSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt boroujerdiModernizingIslam ∷ []
