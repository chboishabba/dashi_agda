module DASHI.Biology.Agriculture.AustralianGrasslandSuccessionRegenerationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution

scottMorgan2012DOI : String
scottMorgan2012DOI = "10.1016/j.jaridenv.2011.08.014"

standish2007DOI : String
standish2007DOI = "10.1111/j.1365-2664.2006.01262.x"

fensham2016DOI : String
fensham2016DOI = "10.1111/1365-2664.12551"

parkhurst2022DOI : String
parkhurst2022DOI = "10.1002/eap.2547"

parkhurst2022PMID : String
parkhurst2022PMID = "35080806"

scottMorgan2012 : Attribution.AttributedSource
scottMorgan2012 = Attribution.mkDOISource
  "Andrea J. Scott; John W. Morgan"
  "Recovery of soil and vegetation in semi-arid Australian old fields"
  "Journal of Arid Environments 76:61-71"
  "2012" scottMorgan2012DOI "https://doi.org/10.1016/j.jaridenv.2011.08.014"
  Attribution.academicArticleSource
  "South-eastern Australian semi-arid old-field chronosequence showing long-horizon vegetation and soil recovery. Trajectory convergence does not imply instantaneous or universal recovery."
  Attribution.publicAttribution

standishEtAl2007 : Attribution.AttributedSource
standishEtAl2007 = Attribution.mkDOISource
  "Rachel J. Standish; Viki A. Cramer; Suzanne L. Wild; Richard J. Hobbs"
  "Seed dispersal and recruitment limitation are barriers to native recolonization of old-fields in western Australia"
  "Journal of Applied Ecology 44:435-445"
  "2007" standish2007DOI "https://doi.org/10.1111/j.1365-2664.2006.01262.x"
  Attribution.academicArticleSource
  "Western Australian wheatbelt old-field source. Native recolonisation remained limited by seed availability/dispersal and recruitment, with non-native annual grasses often dominating."
  Attribution.publicAttribution

fenshamEtAl2016 : Attribution.AttributedSource
fenshamEtAl2016 = Attribution.mkDOISource
  "Rod J. Fensham; Don W. Butler; Russell J. Fairfax; Amy R. Quintin; John M. Dwyer"
  "Passive restoration of subtropical grassland after abandonment of cultivation"
  "Journal of Applied Ecology 53(1):274-283"
  "2016" fensham2016DOI "https://doi.org/10.1111/1365-2664.12551"
  Attribution.academicArticleSource
  "Queensland subtropical-grassland chronosequence. Passive recovery depends on nearby remnant seed sources, dispersal and avoiding deflected succession/exotic monopoly; abandonment is not itself a recovery receipt."
  Attribution.publicAttribution

parkhurstEtAl2022 : Attribution.AttributedSource
parkhurstEtAl2022 = Attribution.mkDOISource
  "Tina Parkhurst; Rachel J. Standish; Suzanne M. Prober"
  "P is for persistence: Soil phosphorus remains elevated for more than a decade after old field restoration"
  "Ecological Applications 32(3):e2547"
  "2022" parkhurst2022DOI "https://pubmed.ncbi.nlm.nih.gov/35080806/"
  Attribution.academicArticleSource
  "Semi-arid Western Australian restored old fields retained elevated available phosphorus relative to reference woodland more than a decade after planting. Present vegetation does not erase agricultural nutrient history."
  Attribution.publicAttribution

record GrasslandSuccessionBoundary : Set where
  constructor grassland-succession-boundary
  field
    soilRecoveryImpliesFloristicRecovery : Bool
    abandonmentImpliesReferenceCommunityRecovery : Bool
    seedSourceDispersalAndRecruitmentMustRemainIndexed : Bool
    nearbyRemnantContextMayBeDropped : Bool
    speciesRichnessRecoveryImpliesReferenceComposition : Bool
    presentVegetationErasesAgriculturalPLegacy : Bool
    oldFieldAgeAloneDeterminesTrajectory : Bool
    exoticCompetitionMayBeDropped : Bool
    passiveSuccessionCreatesDeploymentAuthority : Bool
open GrasslandSuccessionBoundary public

canonicalGrasslandBoundary : GrasslandSuccessionBoundary
canonicalGrasslandBoundary = grassland-succession-boundary
  false false true false false false false false false

attributionRule : String
attributionRule =
  "Scott & Morgan 2012 owns its south-eastern Australian old-field chronosequence; Standish et al. 2007 owns its WA dispersal/recruitment observations; Fensham et al. 2016 owns its Queensland subtropical-grassland passive-restoration trajectory; Parkhurst/Standish/Prober 2022 (DOI 10.1002/eap.2547; PMID 35080806) owns its persistent soil-P legacy observations. DASHI owns only the typed separation among soil recovery, floristic recovery, dispersal/recruitment constraints and agricultural legacy."
