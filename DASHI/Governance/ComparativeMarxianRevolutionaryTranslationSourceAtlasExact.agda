module DASHI.Governance.ComparativeMarxianRevolutionaryTranslationSourceAtlasExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- COMPARATIVE MARXIAN REVOLUTIONARY TRANSLATION SOURCE ATLAS
--
-- Cases are source-bounded examples of Marxian/Leninist concepts being
-- translated through anti-colonial, national, agrarian, religious, racial and
-- state-building conditions.  The atlas does not rank revolutions, equate
-- tactics, or make one case normative for another.
------------------------------------------------------------------------

vietnamGlobalMarxism2026 : Source.AttributedSource
vietnamGlobalMarxism2026 = Source.mkDOISource
  "Simin Fadaee"
  "Ho Chi Minh: always truly uncle"
  "Global Marxism: Decolonisation and revolutionary politics, chapter 2"
  "2026"
  "10.7765/9781526178008.00005"
  "https://www.cambridge.org/core/books/abs/global-marxism/ho-chi-minh-always-truly-uncle/DF5113088A1E805AB292B69BE07715D1"
  Source.academicChapterSource
  "supports Ho Chi Minh's Leninist two-stage revolutionary path together with national independence, coalition-building and a fundamental peasant role in Vietnamese conditions"
  Source.publicAttribution

vietnamRedInternationalism2023 : Source.AttributedSource
vietnamRedInternationalism2023 = Source.mkDOISource
  "Vanh Nguyen-Marshall"
  "Overture"
  "Red Internationalism: Anti-Imperialism and Human Rights in the Global Sixties and Seventies"
  "2023"
  "10.1017/9781009076128.002"
  "https://www.cambridge.org/core/books/abs/red-internationalism/overture/94012D64F151773BFE002D1E162D67B5"
  Source.academicChapterSource
  "supports Vietnam as a major test case for Leninist national self-determination and its tension between nation-building and universal communist emancipation"
  Source.publicAttribution

vietnamPluralMarxism2010 : Source.AttributedSource
vietnamPluralMarxism2010 = Source.mkDOISource
  "Shawn McHale"
  "Vietnamese Marxism, Dissent, and the Politics of Postcolonial Memory: Tran Duc Thao, 1946-1993"
  "The Journal of Asian Studies 69(1)"
  "2010"
  "10.1017/S0021911809991596"
  "https://www.cambridge.org/core/journals/journal-of-asian-studies/article/vietnamese-marxism-dissent-and-the-politics-of-postcolonial-memory-tran-duc-thao-19461993/6A2F287E8C7D2F023461D97A2B73ED0B"
  Source.academicArticleSource
  "supports a non-monolithic account of Vietnamese communism and Marxism, retaining dissent, contingency and plural postcolonial intellectual positions"
  Source.publicAttribution

chinaSinification2009 : Source.AttributedSource
chinaSinification2009 = Source.mkDOISource
  "Raymond F. Wylie"
  "Mao Tse-tung, Ch'en Po-ta and the Sinification of Marxism, 1936-38"
  "The China Quarterly"
  "2009 online publication of historical article"
  "10.1017/S0305741000015137"
  "https://www.cambridge.org/core/journals/china-quarterly/article/abs/mao-tsetung-chen-pota-and-the-sinification-of-marxism-193638/B2F4BFD41909DC913AA3A4B9195A8059"
  Source.academicArticleSource
  "supports the explicit programme of adapting Marxism-Leninism to Chinese historical conditions including weak capitalist development and a central rural peasantry"
  Source.publicAttribution

chinaPeasantRevolution : Source.AttributedSource
chinaPeasantRevolution = Source.mkNoDOISource
  "Lucien Bianco and Janet Lloyd"
  "Peasant movements"
  "The Cambridge History of China"
  "2008 online publication"
  "https://www.cambridge.org/core/books/abs/cambridge-history-of-china/peasant-movements/DE80886B0A7AFD76DEE639A7894599E6"
  Source.academicChapterSource
  "supports the centrality of peasant mobilisation to the Chinese Revolution while distinguishing spontaneous rural unrest from Communist revolutionary organisation"
  Source.publicAttribution

algeriaRevolutionaryThought2023 : Source.AttributedSource
algeriaRevolutionaryThought2023 = Source.mkDOISource
  "Emma Stone Mackinnon"
  "The Right to Rebel: History and Universality in the Political Thought of the Algerian Revolution"
  "Time, History, and Political Thought, chapter 13"
  "2023"
  "10.1017/9781009289399.014"
  "https://www.cambridge.org/core/books/abs/time-history-and-political-thought/right-to-rebel-history-and-universality-in-the-political-thought-of-the-algerian-revolution/7FF0FAE9CD3A6EF18DA1FE569A8592C6"
  Source.academicChapterSource
  "supports Algerian revolutionary thinkers, including Fanon, reworking inherited universal/revolutionary concepts rather than merely receiving a European model unchanged"
  Source.publicAttribution

nicaraguaPluralRevolution2021 : Source.AttributedSource
nicaraguaPluralRevolution2021 = Source.mkDOISource
  "Mateo Jarquín"
  "Internationalizing Revolution: The Nicaraguan Revolution and the World, 1977-1990"
  "The Americas 78(4)"
  "2021"
  "10.1017/tam.2021.93"
  "https://www.cambridge.org/core/journals/americas/article/internationalizing-revolution-the-nicaraguan-revolution-and-the-world-19771990/E27B6B2468CFA2931372E7B5E35BF56D"
  Source.academicArticleSource
  "supports the Nicaraguan revolutionary field as ideologically plural, combining strands from social democracy through liberation theology to Marxism-Leninism, with internal disagreement about Marxism's local applicability"
  Source.publicAttribution

southAfricaANCMarxism : Source.AttributedSource
southAfricaANCMarxism = Source.mkNoDOISource
  "Dale T. McKinley"
  "Critical reflections on the crisis and limits of ANC Marxism"
  "Marxisms in the 21st Century, chapter 10"
  "2017"
  "https://www.cambridge.org/core/books/abs/marxisms-in-the-21st-century/critical-reflections-on-the-crisis-and-limits-of-anc-marxism/A05127E583302CC1B3D438DA4BFDB5E6"
  Source.academicChapterSource
  "supports ANC use of Marxist analysis of racialised capitalism and colonialism-of-a-special-type within a multi-class national-democratic liberation strategy rather than an automatic transition to socialism"
  Source.publicAttribution

canonicalSources : List Source.AttributedSource
canonicalSources =
  vietnamGlobalMarxism2026
  ∷ vietnamRedInternationalism2023
  ∷ vietnamPluralMarxism2010
  ∷ chinaSinification2009
  ∷ chinaPeasantRevolution
  ∷ algeriaRevolutionaryThought2023
  ∷ nicaraguaPluralRevolution2021
  ∷ southAfricaANCMarxism
  ∷ []

vietnamSnowball : Snowball.SourceRoleSnowballReceipt vietnamGlobalMarxism2026
vietnamSnowball = Snowball.canonicalSourceRoleSnowballReceipt vietnamGlobalMarxism2026
