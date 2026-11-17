module DASHI.Biology.KitzerowBH4SourceAtlasExact where

open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- Attributed sources.  These rows identify provenance and bounded relevance;
-- by AttributedSourceCore construction they import neither proof nor authority.
------------------------------------------------------------------------

kitzerow2024BH4 : Source.AttributedSource
kitzerow2024BH4 =
  Source.mkDOISource
    "Kimberly Kitzerow"
    "Autism & the Comorbidities Along the BH4 Pathway"
    "ResearchGate preprint"
    "2024"
    "10.13140/RG.2.2.23124.37761/1"
    "https://www.researchgate.net/publication/377205476_Autism_the_Comorbidities_Along_the_BH4_Pathway"
    Source.academicArticleSource
    "primary Kitzerow source for BH4/autism/comorbidity synthesis; source identity does not establish correctness"
    Source.publicAttribution

kitzerow2024Allostasis : Source.AttributedSource
kitzerow2024Allostasis =
  Source.mkDOISource
    "Kimberly Kitzerow"
    "The BH4 Pathway as an Allostatic Mechanism in the Pathology of Autism and Systemic Comorbidities"
    "ResearchGate preprint"
    "2024"
    "10.13140/RG.2.2.18927.96167"
    "https://www.researchgate.net/publication/383021907_The_BH4_Pathway_as_an_Allostatic_Mechanism_in_the_Pathology_of_Autism_and_Systemic_Comorbidities"
    Source.academicArticleSource
    "primary source for proposed allostatic BH4-resource-reallocation architecture; not empirical closure of the cascade"
    Source.publicAttribution

eichwald2023BH4 : Source.AttributedSource
eichwald2023BH4 =
  Source.mkDOISource
    "Tuany Eichwald et al."
    "Tetrahydrobiopterin: Beyond Its Traditional Role as a Cofactor"
    "Antioxidants 12(5):1037"
    "2023"
    "10.3390/antiox12051037"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC10215290/"
    Source.academicArticleSource
    "pre-Kitzerow BH4 prior art for cytoprotective, mitochondrial, oxidative-stress, inflammatory and cofactor roles; does not supply Kitzerow's autism-cascade priority"
    Source.publicAttribution

colpani2025ASDReview : Source.AttributedSource
colpani2025ASDReview =
  Source.mkDOISource
    "Clovis Colpani Filho et al."
    "Tetrahydrobiopterin and Autism Spectrum Disorder: A Systematic Review of a Promising Therapeutic Pathway"
    "Brain Sciences 15(2):151"
    "2025"
    "10.3390/brainsci15020151"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC11853471/"
    Source.academicArticleSource
    "systematic-review support for BH4-pathway relevance in ASD; does not establish a central resource-allocation shunt or whole-cascade causation"
    Source.publicAttribution

jang2025ReticularThalamus : Source.AttributedSource
jang2025ReticularThalamus =
  Source.mkDOISource
    "Sung-Soo Jang; Fuga Takahashi; John R. Huguenard et al."
    "Reticular thalamic hyperexcitability drives autism spectrum disorder behaviors in the Cntnap2 model of autism"
    "Science Advances 11(34):eadw4682"
    "2025"
    "10.1126/sciadv.adw4682"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC12366697/"
    Source.academicArticleSource
    "direct circuit-level intervention evidence in Cntnap2 mice; upstream BH4/AAAH provenance is not established by this experiment"
    Source.publicAttribution

ojha2026NOTSC2MTOR : Source.AttributedSource
ojha2026NOTSC2MTOR =
  Source.mkDOISource
    "Shashank Kumar Ojha et al."
    "Nitric Oxide-Mediated S-Nitrosylation of TSC2 Drives mTOR dysregulation across Shank3 and Cntnap2 Models of Autism Spectrum Disorder"
    "Molecular Psychiatry 31:3710-3725"
    "2026"
    "10.1038/s41380-026-03514-6"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC13269142/"
    Source.academicArticleSource
    "direct mechanistic evidence for an NO/S-nitrosylation/TSC2/mTOR edge in two autism mouse models plus clinical samples; does not by itself establish upstream BH4 resource reallocation"
    Source.publicAttribution

nomura2025CNV : Source.AttributedSource
nomura2025CNV =
  Source.mkDOISource
    "Nomura et al."
    "ESC models of autism with copy-number variations reveal cell-type-specific translational vulnerability"
    "Cell Genomics 5(6):100877"
    "2025"
    "10.1016/j.xgen.2025.100877"
    "https://doi.org/10.1016/j.xgen.2025.100877"
    Source.academicArticleSource
    "cell-type-specific translational-vulnerability evidence; a reported 2022 preprint chronology makes it an independence control for later Kitzerow synthesis"
    Source.publicAttribution

kitzerowPrimarySources : List Source.AttributedSource
kitzerowPrimarySources = kitzerow2024BH4 ∷ kitzerow2024Allostasis ∷ []

inheritedPriorArtSources : List Source.AttributedSource
inheritedPriorArtSources = eichwald2023BH4 ∷ []

comparisonExperimentalSources : List Source.AttributedSource
comparisonExperimentalSources =
  colpani2025ASDReview
  ∷ jang2025ReticularThalamus
  ∷ ojha2026NOTSC2MTOR
  ∷ nomura2025CNV
  ∷ []

canonicalKitzerowBH4SourceAtlas : Source.AttributedSourceAtlas
canonicalKitzerowBH4SourceAtlas =
  Source.mkSourceAtlas
    "Kitzerow BH4 / autism convergence source atlas"
    "DASHI.Biology.KitzerowBH4SourceAtlasExact"
    (kitzerow2024BH4
      ∷ kitzerow2024Allostasis
      ∷ eichwald2023BH4
      ∷ colpani2025ASDReview
      ∷ jang2025ReticularThalamus
      ∷ ojha2026NOTSC2MTOR
      ∷ nomura2025CNV
      ∷ [])
    "Primary Kitzerow work, inherited BH4 prior art and bounded later comparison studies; citation does not import proof, priority, derivation, clinical authority or legal conclusion."
