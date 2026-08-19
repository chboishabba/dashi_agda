module DASHI.Education.EarlyLearningComparativeEvidenceRound2SourceRegistry where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Education.EarlyLearningComparativeEvidenceSourceRegistry as Sources

------------------------------------------------------------------------
-- ROUND-2 COMPARATIVE EVIDENCE SOURCES
--
-- These references sharpen four boundaries already present in the early-
-- learning comparative architecture:
--
--   * policy effects are heterogeneous relative to family counterfactuals;
--   * home-care allowances are not automatically protective alternatives;
--   * ECEC quality is multidimensional and workforce/process dependent;
--   * Nordic policy architectures are historically variable/hybrid rather
--     than permanent country essences.
--
-- None of the references below authorises a universal route ranking.
------------------------------------------------------------------------

cornelissenDustmannRauteSchonberg2018 : Sources.ComparativeReference
cornelissenDustmannRauteSchonberg2018 =
  Sources.comparativeReference
    "germany-universal-childcare-marginal-returns-2018"
    "Who Benefits from Universal Child Care? Estimating Marginal Returns to Early Child Care Attendance"
    ("Thomas Cornelissen" ∷ "Christian Dustmann" ∷ "Anna Raute" ∷ "Uta Schoenberg" ∷ [])
    2018
    "Journal of Political Economy 126(6), 2356-2409"
    "10.1086/699979"
    "Estimates heterogeneous treatment effects of universal child-care attendance in Germany and finds larger gains for disadvantaged children whose counterfactual non-attendance outcomes are worse."
    "The study supports counterfactual-relative heterogeneity; it does not provide a deterministic demographic routing rule or prove that every disadvantaged child benefits from every ECEC setting."
    true refl

duvanderEllingsaeter2016 : Sources.ComparativeReference
duvanderEllingsaeter2016 =
  Sources.comparativeReference
    "nordic-cash-childcare-diverse-paths-2016"
    "Cash for childcare schemes in the Nordic welfare states: diverse paths, diverse outcomes"
    ("Ann-Zofie Duvander" ∷ "Anne Lise Ellingsaeter" ∷ [])
    2016
    "European Societies 18(1), 70-90"
    "10.1080/14616696.2015.1124903"
    "Compares cash-for-childcare schemes across the five Nordic countries and emphasizes policy hybridisation, different reform paths, opportunity structures and heterogeneous parental responses."
    "The comparison supports architecture-level distinctions but rules against treating a Nordic country label as a timeless policy type or inferring one universal cash-for-care effect."
    true refl

sipilaKorpinen1998 : Sources.ComparativeReference
sipilaKorpinen1998 =
  Sources.comparativeReference
    "finland-cash-versus-childcare-services-1998"
    "Cash versus Child Care Services in Finland"
    ("Jorma Sipila" ∷ "Johanna Korpinen" ∷ [])
    1998
    "Social Policy & Administration 32(3), 263-277"
    "10.1111/1467-9515.00102"
    "Documents the Finnish political settlement combining a legal guarantee of day-care access for young children with state subsidies for home care."
    "The Finnish institutional history is a concrete hybrid-policy example; it does not establish that the same combination has identical effects in another country or period."
    true refl

gruberKosonenHuttunen2025 : Sources.ComparativeReference
gruberKosonenHuttunen2025 =
  Sources.comparativeReference
    "finland-home-care-allowance-2025"
    "Paying moms to stay home: Short and long run effects on parents and children"
    ("Jonathan Gruber" ∷ "Tuomas Kosonen" ∷ "Kristiina Huttunen" ∷ [])
    2025
    "Journal of Public Economics 251, 105496"
    "10.1016/j.jpubeco.2025.105496"
    "Uses variation in Finnish Home Care Allowance incentives and reports lower maternal employment together with adverse measured child outcomes; a daycare-fee reform provides an opposite-incentive check."
    "This is evidence against treating cash-for-home-care as automatically protective. It does not prove that family care itself is harmful or that all home-care allowance designs have the same effects."
    true refl

laaninen2025 : Sources.ComparativeReference
laaninen2025 =
  Sources.comparativeReference
    "finland-home-care-duration-school-success-2025"
    "Duration of child home care allowance period and school success: Differences by parental education level and ethnic origins"
    ("Markus Laaninen" ∷ [])
    2025
    "Research in Social Stratification and Mobility 98, 101063"
    "10.1016/j.rssm.2025.101063"
    "Finnish register analysis associates longer home-care-allowance periods with lower school success particularly for children of less-educated mothers and children with immigrant backgrounds."
    "Association and family-fixed-effects evidence does not identify a universal individual treatment rule; it strengthens the requirement to retain stratified counterfactual and uptake coordinates."
    true refl

oecdStartingStrongVI2021 : Sources.ComparativeReference
oecdStartingStrongVI2021 =
  Sources.comparativeReference
    "oecd-starting-strong-vi-2021"
    "Starting Strong VI: Supporting Meaningful Interactions in Early Childhood Education and Care"
    ("OECD" ∷ [])
    2021
    "OECD Publishing"
    "10.1787/f47a06ae-en"
    "Treats process quality - children's daily interactions with staff, peers, families and environments - as a proximal driver of learning, development and well-being, and analyses curriculum/pedagogy and workforce development as policy levers."
    "Process-quality evidence does not imply that professional presence or enrolment alone guarantees a beneficial outcome; quality must remain an explicit coordinate."
    true refl

oecdTalisStartingStrong2019 : Sources.ComparativeReference
oecdTalisStartingStrong2019 =
  Sources.comparativeReference
    "oecd-providing-quality-ecec-2019"
    "Providing Quality Early Childhood Education and Care: Results from the Starting Strong Survey 2018"
    ("OECD" ∷ [])
    2019
    "OECD Publishing"
    "10.1787/301005d1-en"
    "International ECEC workforce and process-quality evidence distinguishing staff preparation, professional development, working conditions, structural resources and interaction quality."
    "Cross-country survey evidence does not establish one universal quality threshold or identify setting type with quality."
    true refl

canonicalRound2ComparativeSources : List Sources.ComparativeReference
canonicalRound2ComparativeSources =
  cornelissenDustmannRauteSchonberg2018
  ∷ duvanderEllingsaeter2016
  ∷ sipilaKorpinen1998
  ∷ gruberKosonenHuttunen2025
  ∷ laaninen2025
  ∷ oecdStartingStrongVI2021
  ∷ oecdTalisStartingStrong2019
  ∷ []
