module DASHI.Biology.KitzerowBH4NeuralContextSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- PRIMARY NEURAL/DEVELOPMENTAL/REDOX-SPATIAL BH4 CONTEXT SOURCES
--
-- These sources constrain current-pool versus developmental/state-history,
-- redox-regeneration, cell-topology, uptake and route-of-exposure
-- interpretations. They do not inherit DASHI's causal synthesis or
-- Kitzerow-model attribution.
------------------------------------------------------------------------

anastasiadisKuhnLevine1994Uptake : Source.AttributedSource
anastasiadisKuhnLevine1994Uptake =
  Source.mkDOISource
    "P. Z. Anastasiadis; D. M. Kuhn; R. A. Levine"
    "Tetrahydrobiopterin uptake into rat brain synaptosomes, cultured PC12 cells, and rat striatum"
    "Brain Research 665(1):77-84"
    "1994"
    "10.1016/0006-8993(94)91154-1"
    "https://pubmed.ncbi.nlm.nih.gov/7882022/"
    Source.academicArticleSource
    "Primary uptake study. Pays linear concentration-dependent intracellular accumulation of exogenous BH4 in rat brain synaptosomes and PC12 cells plus uptake into rat striatum after peripheral administration. In the studied systems uptake was not sodium/glucose dependent and was interpreted as not requiring a specific membrane carrier. It does not quantify physiological intercellular donor-to-recipient BH4 flux."
    Source.publicAttribution

hylandEtAl1996Hph1 : Source.AttributedSource
hylandEtAl1996Hph1 =
  Source.mkDOISource
    "Keith Hyland; R. S. Gunasekera; T. Engle; L. A. Arnold"
    "Tetrahydrobiopterin and Biogenic Amine Metabolism in the hph-1 Mouse"
    "Journal of Neurochemistry 67(2):752-759"
    "1996"
    "10.1046/j.1471-4159.1996.67020752.x"
    "https://pubmed.ncbi.nlm.nih.gov/8764604/"
    Source.academicArticleSource
    "Primary hph-1 mouse study of GTP cyclohydrolase-I/BH4 deficiency, brain monoamine metabolism and chronic BH4 supplementation. Pays source-bounded findings that BH4 deficiency co-occurs with reduced dopamine/norepinephrine/serotonin and reduced in-vivo TH/TPH activities, while chronic BH4 raises brain BH4 above control without restoring monoamine metabolism. It does not prove the whole DASHI/Kitzerow causal architecture."
    Source.publicAttribution

hwangEtAl1998Localization : Source.AttributedSource
hwangEtAl1998Localization =
  Source.mkDOISource
    "O. Hwang; H. Baker; S. S. Gross; T. H. Joh"
    "Localization of GTP cyclohydrolase in monoaminergic but not nitric oxide-producing cells"
    "Synapse 28(2):140-153"
    "1998"
    "10.1002/(SICI)1098-2396(199802)28:2<140::AID-SYN4>3.0.CO;2-B"
    "https://pubmed.ncbi.nlm.nih.gov/9450514/"
    Source.academicArticleSource
    "Primary rat-brain/adrenal immunohistochemistry and in-situ-hybridization study. Pays colocalization of GTPCH with TH/TPH monoaminergic cells and lack of GTPCH colocalization with nNOS-positive cells in the studied regions. The authors propose possible intercellular/extracellular biopterin supply to nNOS cells; that proposed transfer route is not itself a directly measured BH4 flux."
    Source.publicAttribution

liangKaufman1998Striatum : Source.AttributedSource
liangKaufman1998Striatum =
  Source.mkDOISource
    "L. P. Liang; Seymour Kaufman"
    "The regulation of dopamine release from striatum slices by tetrahydrobiopterin and L-arginine-derived nitric oxide"
    "Brain Research 800(2):181-186"
    "1998"
    "10.1016/S0006-8993(98)00452-1"
    "https://pubmed.ncbi.nlm.nih.gov/9685635/"
    Source.academicArticleSource
    "Primary rat-striatum-slice superfusion study. Pays source-conditioned evidence that arginine-driven dopamine release is reduced by NOS or BH4-synthesis inhibition and substantially restored after intracellular BH4 repletion, while direct extracellular BH4 evokes a much larger dopamine-release effect that is largely insensitive to TH/NOS inhibition and strongly reduced by superoxide dismutase/catalase. Route and compartment therefore remain mechanistically distinct."
    Source.publicAttribution

witteveenGiovanelliKaufman1999NOSRedox : Source.AttributedSource
witteveenGiovanelliKaufman1999NOSRedox =
  Source.mkDOISource
    "C. F. Witteveen; J. Giovanelli; Seymour Kaufman"
    "Reactivity of tetrahydrobiopterin bound to nitric-oxide synthase"
    "Journal of Biological Chemistry 274(42):29755-29762"
    "1999"
    "10.1074/jbc.274.42.29755"
    "https://pubmed.ncbi.nlm.nih.gov/10514451/"
    Source.academicArticleSource
    "Primary NOS-bound BH4 turnover study. Pays a source-bounded redox-regeneration coordinate: NOS-bound BH4 is dynamically oxidized and regenerated across turnover, with the measured steady redox state depending on oxidation conditions and reductive regeneration in an NADPH-regenerating system. It does not provide a whole-cell NADPH-to-multi-branch flux map."
    Source.publicAttribution

sumiIchinoseEtAl2001PtsKO : Source.AttributedSource
sumiIchinoseEtAl2001PtsKO =
  Source.mkDOISource
    "C. Sumi-Ichinose; F. Urano; R. Kuroda; T. Ohye; M. Kojima; M. Tazawa; H. Shiraishi; Y. Hagino; T. Nagatsu; T. Nomura; H. Ichinose"
    "Catecholamines and Serotonin Are Differently Regulated by Tetrahydrobiopterin: A Study from 6-Pyruvoyltetrahydropterin Synthase Knockout Mice"
    "Journal of Biological Chemistry 276(44):41150-41160"
    "2001"
    "10.1074/jbc.M102237200"
    "https://pubmed.ncbi.nlm.nih.gov/11517215/"
    Source.academicArticleSource
    "Primary PTS-knockout mouse study paying severe neonatal brain BH4/biopterin deficiency with markedly reduced catecholamines and serotonin, plus differential BH4 dependence across catecholaminergic, serotonergic and NO systems and BH4-dependent TH protein abundance. It does not establish uniform branch allocation or human disease causation."
    Source.publicAttribution

choiEtAl2003HumanNnosUptake : Source.AttributedSource
choiEtAl2003HumanNnosUptake =
  Source.mkDOISource
    "Hyun Jin Choi; Seong Who Kim; Joo Hyuk Im; Seong-Gene Lee; MiJung Kim; Onyou Hwang"
    "Utilization of exogenous tetrahydrobiopterin in nitric oxide synthesis in human neuroblastoma cell line"
    "Neuroscience Letters 352(2):89-92"
    "2003"
    "10.1016/j.neulet.2003.08.032"
    "https://pubmed.ncbi.nlm.nih.gov/14625030/"
    Source.academicArticleSource
    "Primary human nNOS-expressing neuroblastoma study. Pays linear dose-dependent uptake of exogenous BH4 with increased NO production and a functional coculture result in which catecholaminergic CATH.a cells increase NO production in the nNOS-expressing cells. This supports extracellular/intercellular BH4 supply as a functional route in that model but does not directly quantify donor-to-recipient BH4 molecular flux in vivo."
    Source.publicAttribution

jiangEtAl2024Gch1Therapy : Source.AttributedSource
jiangEtAl2024Gch1Therapy =
  Source.mkDOISource
    "Xiaoling Jiang; Yongxian Shao; Yongqiang Liao; Xiaoning Zheng; Minzhi Peng; Yanna Cai; Meiyi Wang; Huazhen Liu; Chunhua Zeng; Yunting Lin; Wen Zhang; Li Liu"
    "Mechanisms underlying the efficacy and limitation of dopa and tetrahydrobiopterin therapies for the deficiency of GTP cyclohydrolase 1 revealed in a novel mouse model"
    "European Journal of Pharmacology 967:176379"
    "2024"
    "10.1016/j.ejphar.2024.176379"
    "https://pubmed.ncbi.nlm.nih.gov/38342361/"
    Source.academicArticleSource
    "Primary Gch1 knock-in mouse therapy study paying source-bounded liver-versus-brain transcriptional differences, developmental-stage dependence of BH4 rescue, restoration of total brain BH4 without restoration of brain dopamine, and persistent near-absence of striatal TH despite increased total-brain TH. It supports regional/state-history constraints, not a universal BH4 allocator theorem."
    Source.publicAttribution

canonicalNeuralContextSources : List Source.AttributedSource
canonicalNeuralContextSources =
  anastasiadisKuhnLevine1994Uptake
  ∷ hylandEtAl1996Hph1
  ∷ hwangEtAl1998Localization
  ∷ liangKaufman1998Striatum
  ∷ witteveenGiovanelliKaufman1999NOSRedox
  ∷ sumiIchinoseEtAl2001PtsKO
  ∷ choiEtAl2003HumanNnosUptake
  ∷ jiangEtAl2024Gch1Therapy
  ∷ []

canonicalNeuralContextSourceAtlas : Source.AttributedSourceAtlas
canonicalNeuralContextSourceAtlas =
  Source.mkSourceAtlas
    "Kitzerow BH4 neural/developmental/redox-spatial context source atlas"
    "DASHI.Biology.KitzerowBH4NeuralContextSourceAtlasExact"
    canonicalNeuralContextSources
    "External sources retain experimental authorship. DASHI owns only the cross-study causal-alternative projection: present BH4 pool, developmental history, enzyme abundance, region, cell topology, cellular uptake, exposure route, redox regeneration and branch context remain distinct coordinates."

canonicalNeuralContextAtlasNonPromoting :
  Source.atlasCreatesAuthority canonicalNeuralContextSourceAtlas ≡ false
canonicalNeuralContextAtlasNonPromoting =
  Source.atlasCreatesAuthorityIsFalse canonicalNeuralContextSourceAtlas
