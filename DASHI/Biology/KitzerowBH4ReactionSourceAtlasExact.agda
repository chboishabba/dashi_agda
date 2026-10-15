module DASHI.Biology.KitzerowBH4ReactionSourceAtlasExact where

open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source

bRENDAgch1 : Source.AttributedSource
bRENDAgch1 =
  Source.mkNoDOISource
    "BRENDA Enzyme Database"
    "EC 3.5.4.16 GTP cyclohydrolase I"
    "BRENDA release 2026.1"
    "2026"
    "https://www.brenda-enzymes.org/enzyme.php?ecno=3.5.4.16"
    Source.institutionalSource
    "reaction identity GTP + H2O -> formate + 7,8-dihydroneopterin 3'-triphosphate; source identity does not promote kinetics or autism mechanism"
    Source.publicAttribution

bRENDAptps : Source.AttributedSource
bRENDAptps =
  Source.mkNoDOISource
    "BRENDA Enzyme Database"
    "EC 4.2.3.12 6-pyruvoyltetrahydropterin synthase"
    "BRENDA release 2026.1"
    "2026"
    "https://www.brenda-enzymes.org/enzyme.php?ecno=4.2.3.12"
    Source.institutionalSource
    "reaction identity dihydroneopterin triphosphate -> 6-pyruvoyltetrahydropterin + triphosphate"
    Source.publicAttribution

bRENDAspr : Source.AttributedSource
bRENDAspr =
  Source.mkNoDOISource
    "BRENDA Enzyme Database"
    "EC 1.1.1.153 sepiapterin reductase"
    "BRENDA release 2026.1"
    "2026"
    "https://www.brenda-enzymes.org/enzyme.php?ecno=1.1.1.153"
    Source.institutionalSource
    "de-novo BH4-forming reduction from 6-pyruvoyltetrahydropterin with NADPH; quantitative species/condition authority remains assay-specific"
    Source.publicAttribution

bRENDApcd : Source.AttributedSource
bRENDApcd =
  Source.mkNoDOISource
    "BRENDA Enzyme Database"
    "EC 4.2.1.96 4a-hydroxytetrahydrobiopterin dehydratase"
    "BRENDA release 2026.1"
    "2026"
    "https://www.brenda-enzymes.org/enzyme.php?ecno=4.2.1.96"
    Source.institutionalSource
    "hydroxylase-cycle dehydration to dihydrobiopterin + H2O"
    Source.publicAttribution

nosReview : Source.AttributedSource
nosReview =
  Source.mkDOISource
    "U. Förstermann; W. C. Sessa"
    "Nitric oxide synthases: regulation and function"
    "European Heart Journal"
    "2012"
    "10.1093/eurheartj/ehr304"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC3345541/"
    Source.academicArticleSource
    "NOS reactants/cofactors, coupled NO/citrulline production and uncoupling boundary; not an autism-specific source"
    Source.publicAttribution

agmoReview : Source.AttributedSource
agmoReview =
  Source.mkDOISource
    "Ernst R. Werner et al."
    "Alkylglycerol Monooxygenase"
    "IUBMB Life 65(4):366-372"
    "2013"
    "10.1002/iub.1143"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC3617469/"
    Source.academicArticleSource
    "AGMO BH4-dependent ether-lipid cleavage chemistry and approximately 1:1 pterin oxidation/ether-lipid cleavage; physiological autism role not established"
    Source.publicAttribution

aromaticHydroxylaseReview : Source.AttributedSource
aromaticHydroxylaseReview =
  Source.mkDOISource
    "Kenneth M. Roberts; Paul F. Fitzpatrick"
    "Mechanisms of Tryptophan and Tyrosine Hydroxylase"
    "IUBMB Life 65(4):350-357"
    "2013"
    "10.1002/iub.1144"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC4270200/"
    Source.academicArticleSource
    "BH4/oxygen/non-heme-iron aromatic amino-acid hydroxylation mechanism; pathway-to-autism inference excluded"
    Source.publicAttribution

canonicalBH4ReactionSourceAtlas : Source.AttributedSourceAtlas
canonicalBH4ReactionSourceAtlas =
  Source.mkSourceAtlas
    "BH4 literal reaction chemistry source atlas"
    "DASHI.Biology.KitzerowBH4ReactionSourceAtlasExact"
    (bRENDAgch1 ∷ bRENDAptps ∷ bRENDAspr ∷ bRENDApcd ∷ nosReview ∷ agmoReview ∷ aromaticHydroxylaseReview ∷ [])
    "Sources paying reaction identity/mechanism coordinates only; no source row creates Kitzerow priority, autism causation, kinetic calibration, clinical authority or whole-model confirmation."
