module DASHI.Foundations.TernaryGolay.SourceAtlas where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.ExternalRepositoryProvenance as UBPProvenance

------------------------------------------------------------------------
-- Attributed source atlas for the ternary-Golay cross-pollination tranche.
--
-- Entries record provenance and the exact logical role assigned to a source.
-- A citation is not a proof import. In particular, the 1996 Calderbank-Sloane
-- claim is always paired with the authors' published correction.
------------------------------------------------------------------------

data SourceStatus : Set where
  externalRepository : SourceStatus
  standardReference : SourceStatus
  publishedClaimCorrected : SourceStatus
  publishedCorrection : SourceStatus
  externalTheoremAwaitingFormalImport : SourceStatus
  lectureNoteConstructionCalibration : SourceStatus
  locallyRecomputedExternalResult : SourceStatus

data DOIStatus : Set where
  doiRecorded : String → DOIStatus
  noDOIForRepository : DOIStatus
  noDOIRecordedHere : DOIStatus

record SourceEntry : Set where
  constructor sourceEntry
  field
    author : String
    title : String
    publication : String
    year : Nat
    doiStatus : DOIStatus
    canonicalURL : String
    status : SourceStatus
    formalRelationship : String

open SourceEntry public

sourceCount : List SourceEntry → Nat
sourceCount [] = zero
sourceCount (_ ∷ xs) = suc (sourceCount xs)

ubpRepositoryEntry : SourceEntry
ubpRepositoryEntry =
  sourceEntry
    UBPProvenance.ubpAuthorName
    UBPProvenance.ubpProjectName
    "GitHub research repository, owner DigitalEuan"
    2026
    noDOIForRepository
    UBPProvenance.ubpRepositoryURL
    externalRepository
    "external origin of TGIC, TAX, NRCI, OffBit, GLR, and the implementation studied; DASHI claims no original UBP authorship"

golayDigitalCodingEntry : SourceEntry
golayDigitalCodingEntry =
  sourceEntry
    "Marcel J. E. Golay"
    "Notes on Digital Coding"
    "Proceedings of the IRE 37, page 657"
    1949
    noDOIRecordedHere
    "https://ieeexplore.ieee.org/document/1698149"
    standardReference
    "historical source of the binary and ternary Golay-code programme"

macWilliamsSloaneEntry : SourceEntry
macWilliamsSloaneEntry =
  sourceEntry
    "F. Jessie MacWilliams and N. J. A. Sloane"
    "The Theory of Error-Correcting Codes"
    "North-Holland Mathematical Library 16"
    1977
    noDOIRecordedHere
    "https://www.sciencedirect.com/bookseries/north-holland-mathematical-library/vol/16"
    standardReference
    "reference for the ternary Golay code, puncturing, extension, weight distribution, and perfect-code background"

elkiesTernaryGolayEntry : SourceEntry
elkiesTernaryGolayEntry =
  sourceEntry
    "Noam D. Elkies"
    "The ternary Golay codes and related structures"
    "Harvard Math 256x: The Theory of Error-Correcting Codes, extended lecture notes"
    2013
    noDOIRecordedHere
    "https://people.math.harvard.edu/~elkies/M256.13/golay3.pdf"
    lectureNoteConstructionCalibration
    "source for the order-12 Hadamard presentation, reduction mod 3, exact weight enumerator, 132 support pairs, small Witt design, and M12/2.M12 discussion; the finite code and design are recomputed locally"

macWilliamsSystematicWeightEntry : SourceEntry
macWilliamsSystematicWeightEntry =
  sourceEntry
    "F. Jessie MacWilliams"
    "A Theorem on the Distribution of Weights in a Systematic Code"
    "Bell System Technical Journal 42(1), 79-94"
    1963
    (doiRecorded "10.1002/j.1538-7305.1963.tb04003.x")
    "https://doi.org/10.1002/j.1538-7305.1963.tb04003.x"
    externalTheoremAwaitingFormalImport
    "primary source for the MacWilliams weight-distribution identity; the q-ary coefficient interface is formalised without pretending the paper is a proof term"

macWilliamsMallowsSloaneGleasonEntry : SourceEntry
macWilliamsMallowsSloaneGleasonEntry =
  sourceEntry
    "F. Jessie MacWilliams, Colin L. Mallows, and N. J. A. Sloane"
    "Generalizations of Gleason's theorem on weight enumerators of self-dual codes"
    "IEEE Transactions on Information Theory 18(6), 794-805"
    1972
    (doiRecorded "10.1109/TIT.1972.1054898")
    "https://doi.org/10.1109/TIT.1972.1054898"
    externalTheoremAwaitingFormalImport
    "source for the Type III invariant-theory route to the ternary self-dual weight enumerator; the explicit 729-word code is enumerated independently in Agda"

plessGolayUniquenessEntry : SourceEntry
plessGolayUniquenessEntry =
  sourceEntry
    "Vera Pless"
    "More on the uniqueness of the Golay codes"
    "Discrete Mathematics 106-107, 391-398"
    1992
    (doiRecorded "10.1016/0012-365X(92)90569-2")
    "https://doi.org/10.1016/0012-365X(92)90569-2"
    locallyRecomputedExternalResult
    "source for uniqueness of the ternary Golay parameter sets and for the S(5,6,12) support theorem; the explicit code, 132 supports, and unique pentad incidence are recomputed locally"

calderbankSloaneClaimEntry : SourceEntry
calderbankSloaneClaimEntry =
  sourceEntry
    "A. R. Calderbank and N. J. A. Sloane"
    "The Ternary Golay Code, the Integers mod 9, and the Coxeter-Todd Lattice"
    "IEEE Transactions on Information Theory 42(2), 636-637"
    1996
    (doiRecorded "10.1109/18.485733")
    "https://doi.org/10.1109/18.485733"
    publishedClaimCorrected
    "historical Z9-lift claim; it must never be consumed without the correction entry below"

calderbankSloaneCorrectionEntry : SourceEntry
calderbankSloaneCorrectionEntry =
  sourceEntry
    "A. R. Calderbank and N. J. A. Sloane"
    "Correction to: The Ternary Golay Code, the Integers Mod 9 and the Coxeter-Todd Lattice"
    "IEEE Transactions on Information Theory 49(1), page 347"
    2003
    (doiRecorded "10.1109/TIT.2002.806139")
    "https://doi.org/10.1109/TIT.2002.806139"
    publishedCorrection
    "withdraws the K12 identification, corrects the determinant to 3^12, and rules out the stated block-9I generator family"

sloaneCoxeterToddEntry : SourceEntry
sloaneCoxeterToddEntry =
  sourceEntry
    "N. J. A. Sloane"
    "The Coxeter-Todd Lattice, the Mitchell Group and Related Sphere Packings"
    "Mathematical Proceedings of the Cambridge Philosophical Society 93(3)"
    1983
    (doiRecorded "10.1017/S0305004100060746")
    "https://doi.org/10.1017/S0305004100060746"
    standardReference
    "reference for K12, the Mitchell group, the Eisenstein description, and related packing data"

conwaySloaneEntry : SourceEntry
conwaySloaneEntry =
  sourceEntry
    "J. H. Conway and N. J. A. Sloane"
    "Sphere Packings, Lattices and Groups, Third Edition"
    "Springer, Grundlehren der mathematischen Wissenschaften 290"
    1999
    (doiRecorded "10.1007/978-1-4757-6568-7")
    "https://doi.org/10.1007/978-1-4757-6568-7"
    standardReference
    "reference for the Leech lattice, Coxeter-Todd lattice, fixed-sublattice and code/lattice constructions; theorem import remains explicit"

curtisM24Entry : SourceEntry
curtisM24Entry =
  sourceEntry
    "Robert T. Curtis"
    "The Maximal Subgroups of M24"
    "Chapter 8 of The Art of Working with the Mathieu Group M24"
    2024
    (doiRecorded "10.1017/9781009405683.010")
    "https://doi.org/10.1017/9781009405683.010"
    externalTheoremAwaitingFormalImport
    "source for octads, trios, dodecads, stabilizers, and their M24 actions"

canonicalTernaryGolaySources : List SourceEntry
canonicalTernaryGolaySources =
  ubpRepositoryEntry
  ∷ golayDigitalCodingEntry
  ∷ macWilliamsSloaneEntry
  ∷ elkiesTernaryGolayEntry
  ∷ macWilliamsSystematicWeightEntry
  ∷ macWilliamsMallowsSloaneGleasonEntry
  ∷ plessGolayUniquenessEntry
  ∷ calderbankSloaneClaimEntry
  ∷ calderbankSloaneCorrectionEntry
  ∷ sloaneCoxeterToddEntry
  ∷ conwaySloaneEntry
  ∷ curtisM24Entry
  ∷ []

canonicalTernaryGolaySourceCount : Nat
canonicalTernaryGolaySourceCount = sourceCount canonicalTernaryGolaySources

canonicalTernaryGolaySourceCountIsTwelve :
  canonicalTernaryGolaySourceCount ≡ 12
canonicalTernaryGolaySourceCountIsTwelve = refl

sourceAtlasReceipt : GenericReceipt.GenericReceipt
sourceAtlasReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "ternary Golay source atlas"
    "DASHI.Foundations.TernaryGolay.SourceAtlas"
    "canonicalTernaryGolaySources"
    "UBP authorship and the explicit ternary-code, MacWilliams, Type III Gleason, Golay uniqueness, Z9-correction, Coxeter-Todd, Eisenstein, Mathieu, and lattice references are attached with authors, titles, URLs and DOIs where available"
    "citations do not import theorem proofs; locally recomputed finite results, external theorem boundaries, and corrected claims remain distinguished"
    "agda -i . DASHI/Foundations/TernaryGolay/SourceAtlas.agda"

sourceAtlasReceiptNonPromoting :
  GenericReceipt.promotesClaim sourceAtlasReceipt ≡ false
sourceAtlasReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse sourceAtlasReceipt
