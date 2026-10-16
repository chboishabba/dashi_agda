module DASHI.Biology.KitzerowBH4NeuralContextSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- PRIMARY NEURAL/DEVELOPMENTAL BH4 CONTEXT SOURCES
--
-- These sources constrain current-pool versus developmental/state-history
-- interpretations of BH4 deficiency and rescue. They do not inherit DASHI's
-- causal synthesis or Kitzerow-model attribution.
------------------------------------------------------------------------

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
  hylandEtAl1996Hph1 ∷ sumiIchinoseEtAl2001PtsKO ∷ jiangEtAl2024Gch1Therapy ∷ []

canonicalNeuralContextSourceAtlas : Source.AttributedSourceAtlas
canonicalNeuralContextSourceAtlas =
  Source.mkSourceAtlas
    "Kitzerow BH4 neural/developmental context source atlas"
    "DASHI.Biology.KitzerowBH4NeuralContextSourceAtlasExact"
    canonicalNeuralContextSources
    "External sources retain experimental authorship. DASHI owns only the cross-study causal-alternative projection: present BH4 pool, developmental history, enzyme abundance, region and branch context remain distinct coordinates."

canonicalNeuralContextAtlasNonPromoting :
  Source.atlasCreatesAuthority canonicalNeuralContextSourceAtlas ≡ false
canonicalNeuralContextAtlasNonPromoting =
  Source.atlasCreatesAuthorityIsFalse canonicalNeuralContextSourceAtlas
