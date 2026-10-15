module DASHI.Chemistry.LineageAcquiredPrimaryEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- PRIMARY / DIRECTLY INSPECTED EVIDENCE ACQUIRED FOR THE LINEAGE MAX-CUT
--
-- Source identity and authorship remain external. DASHI owns only the formal
-- projection from these source-bounded observations into its typed consumers.
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
    "Primary rat-liver PAH experiment using 18O2/[4a-13C] pterin and NMR/spectroscopic analysis; pays the source of the 4a-hydroxy oxygen as molecular O2 in the studied intermediate, not a complete atom map, human kinetic calibration, or in-vivo flux theorem."
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
    "Primary recombinant-human-liver PAH study; pays source-bounded kinetic/regulatory values reported for the expressed enzyme, including phenylalanine and 7-BH4 apparent Km values in the stated in-vitro context; does not pay in-vivo branch flux or portability across assay conditions."
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
    "Primary calmodulin experiment reporting free-ion thresholds/EC50 values for Ca2+ and Pb2+ in fluorescence and calmodulin-stimulated PDE assays and additive mixed-ion effects. These values are target/assay conditioned and do not establish a universal Pb/Ca ordering."
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
    "Primary ESI-MS competition study on calmodulin; pays source-bounded metal-binding/competition ordering and the observation that Pb2+, like Ca2+, supported a CaM:4M:nNOS-target-peptide complex under the studied conditions. It does not license whole-organism functional equivalence."
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
    "Systematic comparative assessment of carbon-versus-silicon chemical diversity/reactivity across candidate solvents, including original thermodynamic analysis. It pays comparative chemistry constraints, not a theorem that carbon is the unique possible substrate or that carbon-rich chemistry implies abiogenesis."
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
    "Primary biocatalysis experiment demonstrating heme-protein catalysis of C-Si bond formation in vitro and in vivo under the reported conditions. It disproves any blanket exclusion of silicon chemistry from biological catalysis but does not establish silicon as a viable primary life backbone."
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
    "Originator-maintained public record. The 27 Nov 2023 Stanford entry exposes a direct Adobe link labelled 'View Email Screenshot'. This pays only public discoverability of an asserted supporting artifact; the linked artifact contents were not retrievable in the present acquisition environment and therefore remain uninspected/unverified."
    Source.publicAttribution

canonicalAcquiredPrimarySources : List Source.AttributedSource
canonicalAcquiredPrimarySources =
  pahOxygenLineage1985
  ∷ pahHumanKinetics1996
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
