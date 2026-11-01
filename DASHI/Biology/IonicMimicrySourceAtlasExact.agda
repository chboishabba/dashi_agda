module DASHI.Biology.IonicMimicrySourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- IONIC / MOLECULAR MIMICRY SOURCE ATLAS
--
-- Attribution discipline:
-- external observation != DASHI geometry model != general toxicology theorem.
------------------------------------------------------------------------

habermannEtAl1983 : Source.AttributedSource
habermannEtAl1983 =
  Source.mkDOISource
    "E. Habermann; K. Crowell; P. Janicki"
    "Lead and other metals can substitute for Ca2+ in calmodulin"
    "Archives of Toxicology 54(1):61-70"
    "1983"
    "10.1007/BF00277816"
    "https://doi.org/10.1007/BF00277816"
    Source.academicArticleSource
    "Reports that Pb2+ can substitute for Ca2+ in several calmodulin-dependent assay contexts; this does not make Pb2+ chemically identical to Ca2+ or prove a universal substitution rule."
    Source.publicAttribution

kirbergerYang2008 : Source.AttributedSource
kirbergerYang2008 =
  Source.mkDOISource
    "Michael Kirberger; Jenny J. Yang"
    "Structural differences between Pb2+- and Ca2+-binding sites in proteins: implications with respect to toxicity"
    "Journal of Inorganic Biochemistry 102(10):1901-1909"
    "2008"
    "10.1016/j.jinorgbio.2008.06.014"
    "https://doi.org/10.1016/j.jinorgbio.2008.06.014"
    Source.academicArticleSource
    "Compares protein Pb2+ and Ca2+ coordination sites and reports shared oxygen-donor usage but different typical coordination numbers/geometries; supports adaptive rather than identity-level mimicry."
    Source.publicAttribution

moralesEtAl2011 : Source.AttributedSource
moralesEtAl2011 =
  Source.mkDOISource
    "Krystal A. Morales; Mauricio Lasagna; Alexey V. Gribenko; Youngdae Yoon; Gregory D. Reinhart; James C. Lee; Wonhwa Cho; Pingwei Li; Tatyana I. Igumenova"
    "Pb2+ as modulator of protein-membrane interactions"
    "Journal of the American Chemical Society 133(27):10599-10611"
    "2011"
    "10.1021/ja2032772"
    "https://doi.org/10.1021/ja2032772"
    Source.academicArticleSource
    "Reports Pb2+ binding to the PKCalpha C2 domain with higher affinity than Ca2+ under the studied conditions and coexistence of distinct Pb2+ coordination geometries; does not license a generic affinity ordering across all proteins."
    Source.publicAttribution

kumarEtAl2012 : Source.AttributedSource
kumarEtAl2012 =
  Source.mkDOISource
    "Shivesh Kumar; Ejaz Ahmad; Sanjeev Kumar; Rizwan Hasan Khan; Samudrala Gourinath"
    "Flexibility of EF-hand motifs: structural and thermodynamic studies of Calcium Binding Protein-1 from Entamoeba histolytica with Pb2+, Ba2+, and Sr2+"
    "BMC Biophysics 5:15"
    "2012"
    "10.1186/2046-1682-5-15"
    "https://doi.org/10.1186/2046-1682-5-15"
    Source.academicArticleSource
    "Provides crystallographic examples in which Pb2+, Sr2+, and Ba2+ occupy Ca2+-binding EF-hand motifs with related overall structures but metal-specific coordination details."
    Source.publicAttribution

dudevGrauffelLim2018 : Source.AttributedSource
dudevGrauffelLim2018 =
  Source.mkDOISource
    "Todor Dudev; Cedric Grauffel; Carmay Lim"
    "How Pb2+ Binds and Modulates Properties of Ca2+-Signaling Proteins"
    "Inorganic Chemistry 57(23):14798-14809"
    "2018"
    "10.1021/acs.inorgchem.8b02548"
    "https://doi.org/10.1021/acs.inorgchem.8b02548"
    Source.academicArticleSource
    "Reports model calculations across Ca2+-binding sites showing that site flexibility and ligand count can determine whether Pb2+ preserves native geometry and activates or deforms the site and disrupts function; this is site-class-conditioned, not universal."
    Source.publicAttribution

canonicalIonicMimicrySources : List Source.AttributedSource
canonicalIonicMimicrySources =
  habermannEtAl1983
  ∷ kirbergerYang2008
  ∷ moralesEtAl2011
  ∷ kumarEtAl2012
  ∷ dudevGrauffelLim2018
  ∷ []

canonicalIonicMimicrySourceAtlas : Source.AttributedSourceAtlas
canonicalIonicMimicrySourceAtlas =
  Source.mkSourceAtlas
    "Ca/Pb ionic mimicry and coordination-geometry source atlas"
    "DASHI.Biology.IonicMimicrySourceAtlasExact"
    canonicalIonicMimicrySources
    "Source-bounded evidence for ion substitution, coordination geometry, site flexibility and protein-state consequences. DASHI owns any general mimicry geometry constructed downstream."

canonicalIonicMimicryAtlasNonPromoting :
  Source.atlasCreatesAuthority canonicalIonicMimicrySourceAtlas ≡ false
canonicalIonicMimicryAtlasNonPromoting =
  Source.atlasCreatesAuthorityIsFalse canonicalIonicMimicrySourceAtlas
