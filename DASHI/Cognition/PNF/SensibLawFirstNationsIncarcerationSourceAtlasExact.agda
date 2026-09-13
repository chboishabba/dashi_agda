module DASHI.Cognition.PNF.SensibLawFirstNationsIncarcerationSourceAtlasExact where

------------------------------------------------------------------------
-- FIRST NATIONS INCARCERATION SOURCE ATLAS
--
-- Source metadata only.  Statistical observations, target assessments, health
-- syntheses and downstream critical/operational interpretations remain separate.
-- No source object creates causality, private intent, legal authority, community
-- authority or DASHI theorem authority by being cited here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source

absCorrectiveServicesMarch2026 : Source.AttributedSource
absCorrectiveServicesMarch2026 = Source.mkNoDOISource
  "Australian Bureau of Statistics"
  "Corrective Services, Australia, March Quarter 2026"
  "Australian Bureau of Statistics"
  "2026"
  "https://www.abs.gov.au/statistics/people/crime-and-justice/corrective-services-australia/latest-release"
  Source.governmentSource
  "Primary official quarterly administrative statistics. Reports an average daily 18,272 Aboriginal and Torres Strait Islander adults in custody in March quarter 2026, 37% of custody, and an imprisonment rate of 2,701 per 100,000 Aboriginal and Torres Strait Islander adults. These observations do not identify a causal mechanism or subjective institutional intent."
  Source.publicAttribution

absPrisonersAustralia2025 : Source.AttributedSource
absPrisonersAustralia2025 = Source.mkNoDOISource
  "Australian Bureau of Statistics"
  "Prisoners in Australia, 2025"
  "Australian Bureau of Statistics"
  "2025"
  "https://www.abs.gov.au/statistics/people/crime-and-justice/prisoners-australia/2025"
  Source.governmentSource
  "Primary official annual prisoner statistics for the 30 June 2025 reference date. Downstream age-standardised trend/rate calculations may be reported by ABS or other identified sources and remain separately attributed."
  Source.publicAttribution

productivityCommissionTarget10March2026 : Source.AttributedSource
productivityCommissionTarget10March2026 = Source.mkNoDOISource
  "Productivity Commission"
  "Socio-economic outcome area 10 - Aboriginal and Torres Strait Islander adults are not overrepresented in the criminal justice system"
  "Closing the Gap Dashboard, Australian Government Productivity Commission"
  "2026"
  "https://www.pc.gov.au/closing-the-gap-data/dashboard/outcome-area/criminal-justice/"
  Source.governmentSource
  "Primary official Target 10 assessment. Target: by 2031 reduce the adult Aboriginal and Torres Strait Islander incarceration rate by at least 15%. March 2026 dashboard records 1,925.4 per 100,000 in the 2019 baseline, 2,318.4 in 2024 and 2,500.2 in 2025 and assesses the national target as worsening with high confidence. Target declaration and realised trajectory remain distinct coordinates."
  Source.publicAttribution

productivityCommissionADCR2026 : Source.AttributedSource
productivityCommissionADCR2026 = Source.mkNoDOISource
  "Productivity Commission"
  "Closing the Gap Annual Data Compilation Report July 2026"
  "Australian Government Productivity Commission"
  "2026"
  "https://www.pc.gov.au/closing-the-gap-data/annual-data-report/2026/"
  Source.governmentSource
  "Primary official annual Closing the Gap compilation. Adult imprisonment Target 10 is reported as worsening; youth detention Target 11 is reported as showing no change from baseline. These target states do not themselves identify causes, intent, community-defined adequacy or remedy."
  Source.publicAttribution

aihwPrisonHealth2025 : Source.AttributedSource
aihwPrisonHealth2025 = Source.mkDOISource
  "Australian Institute of Health and Welfare"
  "The health of people in Australia's prisons 2025"
  "Australian Institute of Health and Welfare, Australian Government"
  "2026"
  "10.25816/j025-0377"
  "https://www.aihw.gov.au/reports/prisoners/health-of-people-in-australias-prisons-2025"
  Source.governmentSource
  "Official national prison-health synthesis. Reports complex health/welfare burdens in prison populations; First Nations imprisonment-rate disparities; employment and other social-determinant observations. Reported associations and literature synthesis are not silently promoted to a single causal explanation of incarceration or every health gap."
  Source.publicAttribution

aihwYouthJustice2024_25 : Source.AttributedSource
aihwYouthJustice2024_25 = Source.mkNoDOISource
  "Australian Institute of Health and Welfare"
  "Youth justice in Australia 2024-25"
  "Australian Institute of Health and Welfare, Australian Government"
  "2026"
  "https://www.aihw.gov.au/reports/youth-justice/youth-justice-in-australia-2024-25"
  Source.governmentSource
  "Official youth-justice statistical report. Reports that First Nations young people are 6.2% of people aged 10-17 but 56% of those under youth-justice supervision on an average day in 2024-25; 62% of 10-17-year-olds in detention were First Nations and the detention rate ratio was about 23. Adult and youth rates remain separate statistical populations."
  Source.publicAttribution

allSources : List Source.AttributedSource
allSources =
  absCorrectiveServicesMarch2026
  ∷ absPrisonersAustralia2025
  ∷ productivityCommissionTarget10March2026
  ∷ productivityCommissionADCR2026
  ∷ aihwPrisonHealth2025
  ∷ aihwYouthJustice2024_25
  ∷ []

atlas : Source.AttributedSourceAtlas
atlas = Source.mkSourceAtlas
  "SensibLaw First Nations incarceration / operational justice sources"
  "DASHI.Cognition.PNF.SensibLawFirstNationsIncarcerationSourceAtlasExact"
  allSources
  "Official descriptive statistics, Closing the Gap target assessments and government health/youth-justice syntheses. The atlas preserves authorship, source role and causal limits and does not transfer affected-community authority to the reporting institution."

sourceCountIsSix : Source.sourceCount allSources ≡ 6
sourceCountIsSix = refl

atlasDoesNotCreateAuthority : Source.atlasCreatesAuthority atlas ≡ false
atlasDoesNotCreateAuthority = refl
