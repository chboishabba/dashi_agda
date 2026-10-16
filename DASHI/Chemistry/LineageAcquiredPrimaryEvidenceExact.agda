module DASHI.Chemistry.LineageAcquiredPrimaryEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- PRIMARY / DIRECTLY INSPECTED EVIDENCE ACQUIRED FOR THE LINEAGE MAX-CUT
------------------------------------------------------------------------

pahOxygenLineage1985 : Source.AttributedSource
pahOxygenLineage1985 =
  Source.mkDOISource
    "T. A. Dix; G. E. Bollag; P. L. Domanico; S. J. Benkovic"
    "Phenylalanine hydroxylase: absolute configuration and source of oxygen of the 4a-hydroxytetrahydropterin species"
    "Biochemistry 24(12):2955-2958"
    "1985"
    "10.1021/bi00333a022"
    "https://pubmed.ncbi.nlm.nih.gov/4016080/"
    Source.academicArticleSource
    "Primary rat-liver PAH 18O2/[4a-13C] pterin experiment; pays molecular-O2 origin of the measured 4a-hydroxy oxygen, not a complete atom map, human kinetic calibration or in-vivo flux theorem."
    Source.publicAttribution

pahHumanKinetics1996 : Source.AttributedSource
pahHumanKinetics1996 =
  Source.mkDOISource
    "Devanand Kowlessur; Bruce A. Citron; Seymour Kaufman"
    "Recombinant human phenylalanine hydroxylase: novel regulatory and structural properties"
    "Archives of Biochemistry and Biophysics 333(1):85-95"
    "1996"
    "10.1006/abbi.1996.0367"
    "https://pubmed.ncbi.nlm.nih.gov/8806757/"
    Source.academicArticleSource
    "Primary recombinant-human PAH study paying source-bounded kinetic/regulatory values in the stated in-vitro context; not in-vivo branch flux or portable cross-assay calibration."
    Source.publicAttribution

pahCatalyticDomainBH4Structure2001 : Source.AttributedSource
pahCatalyticDomainBH4Structure2001 =
  Source.mkDOISource
    "Ole Andreas Andersen; Torgeir Flatmark; Edward Hough"
    "High resolution crystal structures of the catalytic domain of human phenylalanine hydroxylase in its catalytically active Fe(II) form and binary complex with tetrahydrobiopterin"
    "Journal of Molecular Biology 314(2):279-291"
    "2001"
    "10.1006/jmbi.2001.5061"
    "https://pubmed.ncbi.nlm.nih.gov/11718561/"
    Source.academicArticleSource
    "Primary structural authority for catalytically competent human PAH catalytic domain Fe(II) and BH4 binary complex at 1.7/1.5 A; pays source-conditioned active-site geometry, not a numerical electronic wavefunction or catalytic trajectory."
    Source.publicAttribution

pahCatalyticDomainBH4PDB1J8U : Source.AttributedSource
pahCatalyticDomainBH4PDB1J8U =
  Source.mkDOISource
    "Ole Andreas Andersen; Torgeir Flatmark; Edward Hough"
    "PDB 1J8U: Catalytic Domain of Human Phenylalanine Hydroxylase Fe(II) in Complex with Tetrahydrobiopterin"
    "Worldwide Protein Data Bank released coordinate artifact"
    "2002"
    "10.2210/pdb1J8U/pdb"
    "https://www.rcsb.org/structure/1J8U"
    (Source.namedSourceKind "author-deposited structural data artifact")
    "Released 1.50-A structural-coordinate carrier for the source PAH catalytic-domain/BH4 complex; artifact identity/coordinates do not become DASHI authorship, independent replication or a Hamiltonian solution."
    Source.publicAttribution

pahFullLengthBH4Structure2019 : Source.AttributedSource
pahFullLengthBH4Structure2019 =
  Source.mkDOISource
    "Marte Innselset Flydal; Martin Alcorlo-Pages; Fredrik Gullaksen Johannessen; Siseth Martinez-Caballero; Lars Skjaerven; Rafael Fernandez-Leiro; Aurora Martinez; Juan A. Hermoso"
    "Structure of full-length human phenylalanine hydroxylase in complex with tetrahydrobiopterin"
    "Proceedings of the National Academy of Sciences 116(23):11229-11234"
    "2019"
    "10.1073/pnas.1902639116"
    "https://pubmed.ncbi.nlm.nih.gov/31118288/"
    Source.academicArticleSource
    "Primary full-length human PAH structural authority for unbound/BH4-bound precatalytic states and BH4-linked tetramer/allosteric effects; not authority for the downstream chemical reaction path or tissue flux allocation."
    Source.publicAttribution

pahFullLengthBH4PDB6HYC : Source.AttributedSource
pahFullLengthBH4PDB6HYC =
  Source.mkDOISource
    "Martin Alcorlo Pages; Marte Innselset Flydal et al."
    "PDB 6HYC: full-length human phenylalanine hydroxylase in complex with tetrahydrobiopterin"
    "Worldwide Protein Data Bank released coordinate/diffraction artifact"
    "2019"
    "10.2210/pdb6HYC/pdb"
    "https://www.rcsb.org/structure/6HYC"
    (Source.namedSourceKind "author-deposited structural data artifact")
    "Released same-object full-length hPAH:BH4 structural carrier (versioned by wwPDB); not independent scientific authority, a real-space electronic wavefunction or DASHI authorship."
    Source.publicAttribution

pahQMMPES2004 : Source.AttributedSource
pahQMMPES2004 =
  Source.mkDOISource
    "Kazunari Ishida et al."
    "QM/MM Study of the Mononuclear Non-Heme Iron Active Site of Phenylalanine Hydroxylase"
    "Journal of Physical Chemistry B 108(44):17226-17237"
    "2004"
    "10.1021/jp048001r"
    "https://doi.org/10.1021/jp048001r"
    Source.academicArticleSource
    "Primary computational study analysing the phenylalanine-to-tyrosine reaction pathway and energetics with QM/MM and QM models on a 5176-atom catalytic-domain model; pays a source-backed mechanistic PES/energetics model, not an exact physical Hamiltonian or released matrix artifact."
    Source.publicAttribution

pahSingleTurnoverMechanism2013 : Source.AttributedSource
pahSingleTurnoverMechanism2013 =
  Source.mkDOISource
    "Paul F. Fitzpatrick and coauthors"
    "The Kinetic Mechanism of Phenylalanine Hydroxylase: Intrinsic Binding and Rate Constants from Single Turnover Experiments"
    "Biochemistry 52 (2013)"
    "2013"
    "10.1021/bi301675e"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC3572726/"
    Source.academicArticleSource
    "Primary single-turnover study on PheHDelta117 paying ordered substrate-binding/intermediate/product-release kinetic mechanism and source-conditioned intrinsic constants; truncated enzyme context does not become full-length human in-vivo flux."
    Source.publicAttribution

pahFerrylIntermediate2011 : Source.AttributedSource
pahFerrylIntermediate2011 =
  Source.mkDOISource
    "Aram Joel Panay; Michael Lee; Carsten Krebs; J. Martin Bollinger Jr.; Paul F. Fitzpatrick"
    "Evidence for a High-Spin Fe(IV) Species in the Catalytic Cycle of a Bacterial Phenylalanine Hydroxylase"
    "Biochemistry 50(11):1928-1933"
    "2011"
    "10.1021/bi1019868"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC3059337/"
    Source.academicArticleSource
    "Primary rapid-freeze-quench/Mossbauer study of Chromobacterium violaceum PheH; pays a kinetically competent high-spin Fe(IV) catalytic intermediate and source-conditioned rate constants, not identity with full-length human PAH electronic states or a released Hamiltonian/eigenvector."
    Source.publicAttribution

bh4HepaticCompetition1996 : Source.AttributedSource
bh4HepaticCompetition1996 =
  Source.mkDOISource
    "Catherine M. Pastor; Debra Williams; Toshie Yoneyama; Kazuyuki Hatakeyama; Scott Singleton; Edwin Naylor; Timothy R. Billiar"
    "Competition for Tetrahydrobiopterin between Phenylalanine Hydroxylase and Nitric Oxide Synthase in Rat Liver"
    "Journal of Biological Chemistry 271(40):24534-24538"
    "1996"
    "10.1074/jbc.271.40.24534"
    "https://www.sciencedirect.com/science/article/pii/S0021925818400373"
    Source.academicArticleSource
    "Primary same-system rat-hepatocyte/perfused-liver experiment explicitly testing BH4 competition between PAH and induced NOS. It pays source-conditioned PAH output, NOx output, cellular BH4/biopterin measurements and perturbations of phenylalanine, arginine, DAHP and exogenous BH4. It constrains a hepatic PAH-iNOS allocator hypothesis but does not settle TH/TPH/AGMO, human neurobiology, autism causation or a universal BH4 allocator model."
    Source.publicAttribution

pbCaCalmodulin2000 : Source.AttributedSource
pbCaCalmodulin2000 =
  Source.mkNoDOISource
    "M. Kern; M. Wisniewski; L. Cabell; G. Audesirk"
    "Inorganic lead and calcium interact positively in activation of calmodulin"
    "NeuroToxicology 21(3):353-363; PMID 10894125"
    "2000"
    "https://pubmed.ncbi.nlm.nih.gov/10894125/"
    Source.academicArticleSource
    "Primary calmodulin experiment reporting source-conditioned free-ion activation values and mixed-ion effects; no universal Pb/Ca ordering."
    Source.publicAttribution

pbCaCalmodulinESIMS2009 : Source.AttributedSource
pbCaCalmodulinESIMS2009 =
  Source.mkDOISource
    "Sally L. Shirran; Perdita E. Barran"
    "The use of ESI-MS to probe the binding of divalent cations to calmodulin"
    "Journal of the American Society for Mass Spectrometry 20(6):1159-1171"
    "2009"
    "10.1016/j.jasms.2009.02.008"
    "https://pubmed.ncbi.nlm.nih.gov/19297189/"
    Source.academicArticleSource
    "Primary ESI-MS calmodulin competition study; pays source-bounded target recognition, not whole-organism equivalence."
    Source.publicAttribution

siliconBiochemistryAssessment2020 : Source.AttributedSource
siliconBiochemistryAssessment2020 =
  Source.mkDOISource
    "Janusz Jurand Petkowski; William Bains; Sara Seager"
    "On the Potential of Silicon as a Building Block for Life"
    "Life 10(6):84"
    "2020"
    "10.3390/life10060084"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC7345352/"
    Source.academicArticleSource
    "Comparative assessment of carbon-versus-silicon chemistry across candidate solvents; not carbon uniqueness or abiogenesis proof."
    Source.publicAttribution

biologicalCarbonSiliconBond2016 : Source.AttributedSource
biologicalCarbonSiliconBond2016 =
  Source.mkDOISource
    "S. B. Jennifer Kan; Russell D. Lewis; Kai Chen; Frances H. Arnold"
    "Directed evolution of cytochrome c for carbon-silicon bond formation: Bringing silicon to life"
    "Science 354(6315):1048-1051"
    "2016"
    "10.1126/science.aah6219"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC5243118/"
    Source.academicArticleSource
    "Primary biocatalysis experiment demonstrating C-Si bond formation under reported conditions; not silicon-primary-backbone viability."
    Source.publicAttribution

kitzerowTimelinePublicRecord : Source.AttributedSource
kitzerowTimelinePublicRecord =
  Source.mkNoDOISource
    "Kimberly Kitzerow / Kimberly's Educational Resources"
    "Kitzerow Documented Timeline: Framework Development and Source Record"
    "Public originator-maintained timeline"
    "2026"
    "https://www.kimberlyedu.org/kitzerow-documented-timeline"
    Source.archivalSource
    "Originator-maintained public record; supporting links pay discoverability only unless underlying artifacts are independently inspected/authenticated."
    Source.publicAttribution

canonicalAcquiredPrimarySources : List Source.AttributedSource
canonicalAcquiredPrimarySources =
  pahOxygenLineage1985
  ∷ pahHumanKinetics1996
  ∷ pahCatalyticDomainBH4Structure2001
  ∷ pahCatalyticDomainBH4PDB1J8U
  ∷ pahFullLengthBH4Structure2019
  ∷ pahFullLengthBH4PDB6HYC
  ∷ pahQMMPES2004
  ∷ pahSingleTurnoverMechanism2013
  ∷ pahFerrylIntermediate2011
  ∷ bh4HepaticCompetition1996
  ∷ pbCaCalmodulin2000
  ∷ pbCaCalmodulinESIMS2009
  ∷ siliconBiochemistryAssessment2020
  ∷ biologicalCarbonSiliconBond2016
  ∷ kitzerowTimelinePublicRecord
  ∷ []

canonicalAcquiredPrimarySourceAtlas : Source.AttributedSourceAtlas
canonicalAcquiredPrimarySourceAtlas =
  Source.mkSourceAtlas
    "lineage max-cut acquired primary/direct evidence atlas"
    "DASHI.Chemistry.LineageAcquiredPrimaryEvidenceExact"
    canonicalAcquiredPrimarySources
    "Acquired sources retain external authorship and pay only explicitly declared source-bounded coordinates. DASHI composition, cross-source synthesis, causal promotion, priority, plagiarism and legal conclusions remain independent obligations."

canonicalAcquiredAtlasNonPromoting :
  Source.atlasCreatesAuthority canonicalAcquiredPrimarySourceAtlas ≡ false
canonicalAcquiredAtlasNonPromoting =
  Source.atlasCreatesAuthorityIsFalse canonicalAcquiredPrimarySourceAtlas
