module DASHI.Reasoning.StructuralMetaphorSourceRegistryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-BOUNDED METAPHOR / EPISTEMIC-BRAID REGISTRY
--
-- Attribution rule:
--   * bibliographic sources motivate only the role stated below;
--   * no cited author is credited with DASHI's factorisation/descent theorems;
--   * metaphor/network evidence is not promoted to braid-group topology;
--   * Indigenous-source interpretation is kept distinct from original formal
--     mathematics supplied by DASHI.
------------------------------------------------------------------------

data SourceKind : Set where
  peerReviewedArticle bookChapter book : SourceKind

data SourceRole : Set where
  metaphorNetworkStructure
  metaphorUnderstandingRepresentationChange
  twoEyedSeeingMathematics
  kimmererBraidingRelationalEpistemology
  boundedStructuralAnalogy
  methodologicalTransferLimit
  : SourceRole

record SourceReference : Set where
  constructor sourceReference
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    kind : SourceKind
    role : SourceRole
    boundedReading : String

open SourceReference public

teichLealJost2025 : SourceReference
teichLealJost2025 =
  sourceReference
    "Marie Teich; Wilmer Leal; Juergen Jost"
    "Diachronic data analysis supports and refines conceptual metaphor theory"
    "PLOS Complex Systems 2(8):e0000058"
    2025
    "DOI 10.1371/journal.pcsy.0000058"
    peerReviewedArticle
    metaphorNetworkStructure
    "Supports treating metaphor as an enduring cognitive/linguistic relational structure and studying reconceptualisation through topic relations; does not supply braid-group or DASHI descent theorems."

stuartWilkenfeld2022 : SourceReference
stuartWilkenfeld2022 =
  sourceReference
    "Michael T. Stuart; Daniel Wilkenfeld"
    "Understanding metaphorical understanding (literally)"
    "European Journal for Philosophy of Science 12:49"
    2022
    "DOI 10.1007/s13194-022-00479-5"
    peerReviewedArticle
    metaphorUnderstandingRepresentationChange
    "Supports an epistemic role for metaphor through changes to representation and processing; does not establish that any particular metaphor is literally true mathematics."

jungic2022 : SourceReference
jungic2022 =
  sourceReference
    "Veselin Jungic"
    "Two-Eyed Seeing: Mathematics and Indigenous Traditions and Cultures"
    "Maple Transactions 2(1)"
    2022
    "DOI 10.5206/mt.v2i1.15186"
    peerReviewedArticle
    twoEyedSeeingMathematics
    "Applies Two-Eyed Seeing to traditional and mathematical knowledge; motivates coordinated use of non-identical knowledge traditions without identifying them."

kimmerer2013 : SourceReference
kimmerer2013 =
  sourceReference
    "Robin Wall Kimmerer"
    "Braiding Sweetgrass: Indigenous Wisdom, Scientific Knowledge and the Teachings of Plants"
    "Milkweed Editions"
    2013
    "ISBN 9781571313560"
    book
    kimmererBraidingRelationalEpistemology
    "Primary conceptual source for braiding Indigenous knowledge, scientific knowledge and situated story under reciprocity; no braid-group, fibre-bundle or DASHI non-factorability theorem is attributed to the book."

fatima2026 : SourceReference
fatima2026 =
  sourceReference
    "Nusrat Fatima"
    "Continuity and Its Limits: Toward a Critical Theory of Literary Topology in Shakespeare"
    "Journal of Critical Studies in Language and Literature 7(2):1-8"
    2026
    "DOI 10.46809/jcsll.v7i2.430"
    peerReviewedArticle
    methodologicalTransferLimit
    "Supports a bounded structural-analogy reading: literary-topological vocabulary is useful where target relations remain recoverable through deformation and should be withdrawn where rupture makes that assumption incompatible. Does not prove DASHI metaphor fitness, mathematical topology of Shakespeare, or Kimmerer braid mathematics."

structuralMetaphorSources : List SourceReference
structuralMetaphorSources =
  teichLealJost2025
  ∷ stuartWilkenfeld2022
  ∷ jungic2022
  ∷ kimmerer2013
  ∷ fatima2026
  ∷ []

record StructuralMetaphorAttributionBoundary : Set where
  constructor structuralMetaphorAttributionBoundary
  field
    citedSourcesProveDASHINonFactorability : Bool
    citedSourcesProveDASHINonFactorabilityIsFalse :
      citedSourcesProveDASHINonFactorability ≡ false

    kimmererStatesBraidGroupTheory : Bool
    kimmererStatesBraidGroupTheoryIsFalse :
      kimmererStatesBraidGroupTheory ≡ false

    metaphorNetworkPaperProvesKimmererTopology : Bool
    metaphorNetworkPaperProvesKimmererTopologyIsFalse :
      metaphorNetworkPaperProvesKimmererTopology ≡ false

    fatimaProvesDASHIMetaphorFitness : Bool
    fatimaProvesDASHIMetaphorFitnessIsFalse :
      fatimaProvesDASHIMetaphorFitness ≡ false

    fatimaProvesKimmererBraidTopology : Bool
    fatimaProvesKimmererBraidTopologyIsFalse :
      fatimaProvesKimmererBraidTopology ≡ false

    dashiStructuralMetaphorFormalisationIsOriginalInterpretiveExtension : Bool
    dashiStructuralMetaphorFormalisationIsOriginalInterpretiveExtensionIsTrue :
      dashiStructuralMetaphorFormalisationIsOriginalInterpretiveExtension ≡ true

canonicalStructuralMetaphorAttributionBoundary :
  StructuralMetaphorAttributionBoundary
canonicalStructuralMetaphorAttributionBoundary =
  structuralMetaphorAttributionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
