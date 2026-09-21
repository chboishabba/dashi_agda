module DASHI.Biology.KluverLogPolar5HT2ASourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION
--
-- This atlas follows Docs/SourceAttributionPolicy.md:
--
--   external source claim / datum
--     != DASHI formal reconstruction
--     != DASHI cross-source inference
--     != new DASHI theorem / extension
--     != promotion / external adjudication
--
-- The source rows below pay only the roles named in each
-- formalisationRelationship field.  Citation does not import proof and does
-- not authorize stronger mechanistic or phenomenological claims.
------------------------------------------------------------------------


pubChemSerotonin : Source.AttributedSource
pubChemSerotonin =
  Source.mkNoDOISource
    "PubChem"
    "Serotonin"
    "PubChem CID 5202"
    "current database record"
    "https://pubchem.ncbi.nlm.nih.gov/compound/5202"
    Source.institutionalSource
    "Pays molecular identity coordinates for serotonin/5-hydroxytryptamine, including CID 5202 and molecular formula C10H12N2O; it does not establish receptor mechanism or psychedelic phenomenology."
    Source.publicAttribution

pubChemLSD : Source.AttributedSource
pubChemLSD =
  Source.mkNoDOISource
    "PubChem"
    "Lysergic acid diethylamide"
    "PubChem CID 5761"
    "current database record"
    "https://pubchem.ncbi.nlm.nih.gov/compound/5761"
    Source.institutionalSource
    "Pays molecular identity coordinates for LSD/lysergide, including CID 5761 and molecular formula C20H25N3O; it does not establish receptor selectivity, dose-response, or subjective effect."
    Source.publicAttribution

pubChemKetanserin : Source.AttributedSource
pubChemKetanserin =
  Source.mkNoDOISource
    "PubChem"
    "Ketanserin"
    "PubChem CID 3822"
    "current database record"
    "https://pubchem.ncbi.nlm.nih.gov/compound/3822"
    Source.institutionalSource
    "Pays molecular identity coordinates for ketanserin, including CID 3822 and molecular formula C22H22FN3O3; pharmacological interpretation remains separately source-bound."
    Source.publicAttribution

wackerEtAl2017 : Source.AttributedSource
wackerEtAl2017 =
  Source.mkDOISource
    "Daniel Wacker; Sheng Wang; John D. McCorvy; Robin M. Betz; A. J. Venkatakrishnan; Anat Levit; Katherine Lansu; Zachary L. Schools; Tao Che; David E. Nichols; Brian K. Shoichet; Ron O. Dror; Bryan L. Roth"
    "Crystal Structure of an LSD-Bound Human Serotonin Receptor"
    "Cell 168(3):377-389.e12"
    "2017"
    "10.1016/j.cell.2016.12.033"
    "https://doi.org/10.1016/j.cell.2016.12.033"
    Source.academicArticleSource
    "Pays an LSD-bound 5-HT2B crystal structure plus slow LSD dissociation and kinetic/signaling observations involving 5-HT2A; it must not be misattributed as a 5-HT2A crystal structure."
    Source.publicAttribution

kimEtAl2020 : Source.AttributedSource
kimEtAl2020 =
  Source.mkDOISource
    "Kyungsoo Kim; Tao Che; Ouliana Panova; Jeffrey F. DiBerto; Jiankun Lyu; Brian E. Krumm; Daniel Wacker; Michael J. Robertson; Anne B. Seven; David E. Nichols; Brian K. Shoichet; Georgios Skiniotis; Bryan L. Roth"
    "Structure of a Hallucinogen-Activated Gq-Coupled 5-HT2A Serotonin Receptor"
    "Cell 182(6):1574-1588.e19"
    "2020"
    "10.1016/j.cell.2020.08.024"
    "https://doi.org/10.1016/j.cell.2020.08.024"
    Source.academicArticleSource
    "Pays direct structural evidence for hallucinogen-activated human 5-HT2A receptor states, including a 5-HT2A/LSD structural result and Gq-coupled receptor-state context; it does not by itself determine systems-level phenomenology."
    Source.publicAttribution


wallachEtAl2023 : Source.AttributedSource
wallachEtAl2023 =
  Source.mkDOISource
    "Jason Wallach; John D. McCorvy; Alexander M. Sherwood; Hamilton Morris; and collaborators"
    "Identification of 5-HT2A receptor signaling pathways associated with psychedelic potential"
    "Nature Communications 14:8221"
    "2023"
    "10.1038/s41467-023-44016-1"
    "https://doi.org/10.1038/s41467-023-44016-1"
    Source.academicArticleSource
    "Reports that, in the tested ligand series and male-mouse head-twitch paradigm, 5-HT2A Gq efficacy and Gq-PLC disruption track psychedelic-like HTR whereas beta-arrestin2 recruitment does not; this is assay/model-conditioned evidence, not a universal human phenomenology theorem."
    Source.publicAttribution

xuEtAl2026 : Source.AttributedSource
xuEtAl2026 =
  Source.mkDOISource
    "Zheng Xu; Hongshuang Wang; Jingjing Yu; Yue Deng; Xiaowen Tian; and collaborators"
    "Psychedelics elicit their effects by 5-HT2A receptor-mediated Gi signalling"
    "Nature 651:829-837"
    "2026"
    "10.1038/s41586-025-10061-7"
    "https://doi.org/10.1038/s41586-025-10061-7"
    Source.academicArticleSource
    "Reports non-canonical 5-HT2A-mediated Gi signaling as essential in the authors' hallucinogenic-effect assays and provides five 5-HT2A-Gi/Gq cryo-EM structures; this does not erase Gq/PLC evidence from other assays or establish a single universal human mechanism."
    Source.publicAttribution

gumpperEtAl2025 : Source.AttributedSource
gumpperEtAl2025 =
  Source.mkDOISource
    "Ryan H. Gumpper; John F. Fay; Bryan L. Roth; and collaborators"
    "The structural diversity of psychedelic drug actions revealed"
    "Nature Communications"
    "2025"
    "10.1038/s41467-025-57956-7"
    "https://doi.org/10.1038/s41467-025-57956-7"
    Source.academicArticleSource
    "Pays a comparative active-state 5-HT2A cryo-EM structure set across multiple ligands including 5-HT and LSD, supporting ligand-dependent receptor-state comparison without equating structure with subjective effect."
    Source.publicAttribution

pdb9AS4 : Source.AttributedSource
pdb9AS4 =
  Source.mkDOISource
    "RCSB Protein Data Bank; deposition authors R. H. Gumpper; J. F. Fay; B. L. Roth"
    "5-HT2AR bound to LSD in complex with mini-Gq and scFv16, global cryo-EM reconstruction"
    "RCSB PDB 9AS4"
    "2025 release"
    "10.2210/pdb9AS4/pdb"
    "https://www.rcsb.org/structure/9AS4"
    Source.institutionalSource
    "Pays a recoverable experimental structure identifier for an LSD-bound human 5-HT2A receptor complex; the deposited construct and experimental conditions do not imply an in-vivo brain state or percept."
    Source.publicAttribution

ermentroutCowan1979 : Source.AttributedSource
ermentroutCowan1979 =
  Source.mkDOISource
    "G. Bard Ermentrout; Jack D. Cowan"
    "A mathematical theory of visual hallucination patterns"
    "Biological Cybernetics 34:137-150"
    "1979"
    "10.1007/BF00336965"
    "https://doi.org/10.1007/BF00336965"
    Source.academicArticleSource
    "Motivates neural-field instability and symmetry-selected visual-pattern families; does not state the finite DASHI witnesses or prove that every hallucination is generated by this mechanism."
    Source.publicAttribution

schwartz1980 : Source.AttributedSource
schwartz1980 =
  Source.mkDOISource
    "Eric L. Schwartz"
    "Computational anatomy and functional architecture of striate cortex: a spatial mapping approach to perceptual coding"
    "Vision Research"
    "1980"
    "10.1016/0042-6989(80)90090-5"
    "https://doi.org/10.1016/0042-6989(80)90090-5"
    Source.academicArticleSource
    "Motivates the complex-log / log-polar retinocortical approximation under which multiplicative radial scale and rotation become cortical translations; does not make the finite DASHI chart an exact human V1 atlas."
    Source.publicAttribution

grusser1995 : Source.AttributedSource
grusser1995 =
  Source.mkDOISource
    "O. J. Grusser"
    "Migraine phosphenes and the retino-cortical magnification factor"
    "Vision Research 35(8):1125-1134"
    "1995"
    "10.1016/0042-6989(94)00187-Q"
    "https://doi.org/10.1016/0042-6989(94)00187-Q"
    Source.academicArticleSource
    "Supports the source-side relation between retinocortical magnification, approximately constant cortical propagation, and nonuniform visual-field aura motion; the finite DASHI step theorem is a new synthetic analogue."
    Source.publicAttribution

bressloffEtAl2001 : Source.AttributedSource
bressloffEtAl2001 =
  Source.mkDOISource
    "Paul C. Bressloff; Jack D. Cowan; Martin Golubitsky; Peter J. Thomas; Matthew C. Wiener"
    "Geometric visual hallucinations, Euclidean symmetry and the functional architecture of striate cortex"
    "Philosophical Transactions of the Royal Society B 356:299-330"
    "2001"
    "10.1098/rstb.2000.0769"
    "https://doi.org/10.1098/rstb.2000.0769"
    Source.academicArticleSource
    "Motivates cortical symmetry/mode families and their retinotopic projection into recurring geometric hallucination classes; does not state the DASHI relation constructors or MDL extensions."
    Source.publicAttribution

hadjikhaniEtAl2001 : Source.AttributedSource
hadjikhaniEtAl2001 =
  Source.mkDOISource
    "Nouchine Hadjikhani; M. Sanchez Del Rio; O. Wu; D. Schwartz; D. Bakker; B. Fischl; K. K. Kwong; F. M. Cutrer; B. R. Rosen; R. B. Tootell; A. G. Sorensen; M. A. Moskowitz"
    "Mechanisms of migraine aura revealed by functional MRI in human visual cortex"
    "Proceedings of the National Academy of Sciences 98(8):4687-4692"
    "2001"
    "10.1073/pnas.071582498"
    "https://doi.org/10.1073/pnas.071582498"
    Source.academicArticleSource
    "Provides human fMRI evidence of a slowly propagating occipital BOLD change congruent with aura retinotopy; it does not prove that psychedelic form constants and migraine aura share one unique mechanism."
    Source.publicAttribution


vanDyckEtAl2000 : Source.AttributedSource
vanDyckEtAl2000 =
  Source.mkNoDOISource
    "C. H. van Dyck; P. Z. Tan; R. M. Baldwin; L. A. Amici; P. K. Garg; C. K. Ng; R. Soufer; D. S. Charney; R. B. Innis"
    "PET quantification of 5-HT2A receptors in the human brain: a constant infusion paradigm with [18F]altanserin"
    "Journal of Nuclear Medicine 41(2):234-241"
    "2000"
    "https://pubmed.ncbi.nlm.nih.gov/10688105/"
    Source.academicArticleSource
    "Reports measurable human 5-HT2A binding with an anterior-cingulate region of interest in healthy volunteers; this pays an ACC receptor-availability coordinate only, not a psychedelic attention or meaning mechanism."
    Source.publicAttribution

beliveauEtAl2017 : Source.AttributedSource
beliveauEtAl2017 =
  Source.mkDOISource
    "Vincent Beliveau; Melanie Ganz; Ling Feng; Benedicte Ozenne; Liselotte Hojgaard; Peter M. Fisher; Claus Svarer; Douglas N. Greve; Gitte M. Knudsen"
    "A High-Resolution In Vivo Atlas of the Human Brain's Serotonin System"
    "Journal of Neuroscience 37(1):120-128"
    "2017"
    "10.1523/JNEUROSCI.2830-16.2016"
    "https://doi.org/10.1523/JNEUROSCI.2830-16.2016"
    Source.academicArticleSource
    "Supports a distributed human 5-HT receptor atlas including 5-HT2A; receptor availability is an anatomical observation and does not itself establish psychedelic causal flow or phenomenological meaning."
    Source.publicAttribution

prellerEtAl2017 : Source.AttributedSource
prellerEtAl2017 =
  Source.mkDOISource
    "Katrin H. Preller; Marcus Herdener; Thomas Pokorny; Amanda Planzer; Rainer Kraehenmann; Philipp Stampfli; Matthias E. Liechti; Erich Seifritz; Franz X. Vollenweider"
    "The Fabric of Meaning and Subjective Effects in LSD-Induced States Depend on Serotonin 2A Receptor Activation"
    "Current Biology 27(3):451-457"
    "2017"
    "10.1016/j.cub.2016.12.030"
    "https://doi.org/10.1016/j.cub.2016.12.030"
    Source.academicArticleSource
    "Supports a 5-HT2A-dependent component of LSD-induced subjective effects and altered personal-relevance processing in a ketanserin-blockade paradigm; it does not prove an ACC-specific imperative-attention mechanism."
    Source.publicAttribution

prellerEtAl2018 : Source.AttributedSource
prellerEtAl2018 =
  Source.mkDOISource
    "Katrin H. Preller; Joshua B. Burt; Jie Lisa Ji; Charles H. Schleifer; Brendan D. Adkinson; Philipp Stampfli; Erich Seifritz; Grega Repovs; John H. Krystal; John D. Murray; Franz X. Vollenweider; Alan Anticevic"
    "Changes in global and thalamic brain connectivity in LSD-induced altered states of consciousness are attributable to the 5-HT2A receptor"
    "eLife 7:e35082"
    "2018"
    "10.7554/eLife.35082"
    "https://doi.org/10.7554/eLife.35082"
    Source.academicArticleSource
    "Supports a 5-HT2A-dependent component of LSD-related global/thalamic connectivity changes under ketanserin blockade; it does not make one region or one receptor sufficient for the total experience."
    Source.publicAttribution


barzanEtAl2024 : Source.AttributedSource
barzanEtAl2024 =
  Source.mkDOISource
    "Ruxandra Barzan; Beyza Bozkurt; Mohammadreza M. Nejad; Sandra T. Suess; Tatjana Surdin; and collaborators"
    "Gain control of sensory input across polysynaptic circuitries in mouse visual cortex by a single G protein-coupled receptor type (5-HT2A)"
    "Nature Communications 15:8078"
    "2024"
    "10.1038/s41467-024-51861-1"
    "https://doi.org/10.1038/s41467-024-51861-1"
    Source.academicArticleSource
    "Reports cell-type-specific 5-HT2A-pathway manipulation in mouse V1, calcium/Gq-PLC validation, pyramidal/PV firing effects, and polysynaptic visual-gain modulation; it does not establish psychedelic phenomenology or a direct receptor-to-Kluever-form law."
    Source.publicAttribution

whiteEtAl2026 : Source.AttributedSource
whiteEtAl2026 =
  Source.mkDOISource
    "Callum M. White; Zohre Azimi; Robert Staadt; Chenchen Song; Thomas Knoepfel; Dirk Jancke"
    "Psychedelic 5-HT2A agonist increases spontaneous and evoked 5-Hz oscillations in visual and retrosplenial cortex"
    "Communications Biology 9:216"
    "2026"
    "10.1038/s42003-025-09492-9"
    "https://doi.org/10.1038/s42003-025-09492-9"
    Source.academicArticleSource
    "Reports a psychedelic 5-HT2A agonist-associated change in spontaneous and evoked approximately 5-Hz cortical oscillatory activity including visual cortex; it supplies a circuit-dynamics coordinate, not a Kluever-form identity or human perceptual mechanism."
    Source.publicAttribution

solerEtAl2026 : Source.AttributedSource
solerEtAl2026 =
  Source.mkNoDOISource
    "Systematic-review authors indexed by PubMed PMID 41862146"
    "Electrophysiological mechanisms of psychedelic drugs: A systematic review"
    "Neuroscience and Biobehavioral Reviews"
    "2026"
    "https://pubmed.ncbi.nlm.nih.gov/41862146/"
    Source.academicArticleSource
    "Synthesizes heterogeneous in-vitro and in-vivo psychedelic electrophysiology and explicitly cautions against a uniform-excitation account; used only as a review-level heterogeneity boundary, not as primary evidence for any individual current or circuit effect."
    Source.publicAttribution

hamEtAl2013 : Source.AttributedSource
hamEtAl2013 =
  Source.mkDOISource
    "Timothy Ham; Alex Leff; Xavier de Boissezon; Anna Joffe; David J. Sharp"
    "Cognitive control and the salience network: an investigation of error processing and effective connectivity"
    "Journal of Neuroscience 33(16):7091-7098"
    "2013"
    "10.1523/JNEUROSCI.4692-12.2013"
    "https://doi.org/10.1523/JNEUROSCI.4692-12.2013"
    Source.academicArticleSource
    "Supports dorsal anterior cingulate and bilateral insula as nodes used in a salience-network account; it does not establish that psychedelic salience or entity-like communication originates in dACC."
    Source.publicAttribution

cipolottiEtAl2025 : Source.AttributedSource
cipolottiEtAl2025 =
  Source.mkDOISource
    "Lisa Cipolotti; Joe Mole; James K. Ruffle; Amy Nelson; Robert Gray; Parashkev Nachev"
    "Cognitive control and the anterior cingulate cortex: Necessity and coherence"
    "Cortex 182:87-99"
    "2025"
    "10.1016/j.cortex.2024.11.010"
    "https://doi.org/10.1016/j.cortex.2024.11.010"
    Source.academicArticleSource
    "Provides a recent source-side caution against treating medial frontal/ACC activation as a simple necessary controller across canonical conflict tasks; used here as an anti-overclaim boundary."
    Source.publicAttribution

canonicalKluverLogPolar5HT2ASources : List Source.AttributedSource
canonicalKluverLogPolar5HT2ASources =
  pubChemSerotonin
  ∷ pubChemLSD
  ∷ pubChemKetanserin
  ∷ wackerEtAl2017
  ∷ kimEtAl2020
  ∷ wallachEtAl2023
  ∷ xuEtAl2026
  ∷ gumpperEtAl2025
  ∷ pdb9AS4
  ∷ ermentroutCowan1979
  ∷ schwartz1980
  ∷ grusser1995
  ∷ bressloffEtAl2001
  ∷ hadjikhaniEtAl2001
  ∷ vanDyckEtAl2000
  ∷ beliveauEtAl2017
  ∷ prellerEtAl2017
  ∷ prellerEtAl2018
  ∷ barzanEtAl2024
  ∷ whiteEtAl2026
  ∷ solerEtAl2026
  ∷ hamEtAl2013
  ∷ cipolottiEtAl2025
  ∷ []

canonicalKluverLogPolar5HT2AAtlas : Source.AttributedSourceAtlas
canonicalKluverLogPolar5HT2AAtlas =
  Source.mkSourceAtlas
    "Kluver/log-polar/5-HT2A source atlas"
    "DASHI.Biology.KluverLogPolar5HT2ASourceAtlasExact"
    canonicalKluverLogPolar5HT2ASources
    "Source-bounded support for neural-field form constants, log-polar retinotopy, migraine propagation geometry, human 5-HT2A mapping, pharmacological blockade, and ACC/salience context. DASHI composition theorems remain repo-native."

canonicalKluverLogPolar5HT2AAtlasIsNonPromoting :
  Source.atlasCreatesAuthority canonicalKluverLogPolar5HT2AAtlas ≡ false
canonicalKluverLogPolar5HT2AAtlasIsNonPromoting =
  Source.atlasCreatesAuthorityIsFalse canonicalKluverLogPolar5HT2AAtlas
