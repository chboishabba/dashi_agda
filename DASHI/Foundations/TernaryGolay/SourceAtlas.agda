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
-- A citation is not a proof import.  In particular, the 1996 Calderbank–Sloane
-- claim is always paired with the authors' published correction.
------------------------------------------------------------------------

data SourceStatus : Set where
  externalRepository : SourceStatus
  standardReference : SourceStatus
  publishedClaimCorrected : SourceStatus
  publishedCorrection : SourceStatus
  externalTheoremAwaitingFormalImport : SourceStatus

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
  ∷ calderbankSloaneClaimEntry
  ∷ calderbankSloaneCorrectionEntry
  ∷ sloaneCoxeterToddEntry
  ∷ conwaySloaneEntry
  ∷ curtisM24Entry
  ∷ []

canonicalTernaryGolaySourceCount : Nat
canonicalTernaryGolaySourceCount = sourceCount canonicalTernaryGolaySources

canonicalTernaryGolaySourceCountIsEight :
  canonicalTernaryGolaySourceCount ≡ 8
canonicalTernaryGolaySourceCountIsEight = refl

sourceAtlasReceipt : GenericReceipt.GenericReceipt
sourceAtlasReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "ternary Golay source atlas"
    "DASHI.Foundations.TernaryGolay.SourceAtlas"
    "canonicalTernaryGolaySources"
    "UBP repository authorship and the ternary-Golay, Z9-correction, Coxeter-Todd, Eisenstein, Mathieu, and lattice references are explicitly attached"
    "citations do not import theorem proofs; corrected and retracted claims remain distinguished"
    "agda -i . DASHI/Foundations/TernaryGolay/SourceAtlas.agda"

sourceAtlasReceiptNonPromoting :
  GenericReceipt.promotesClaim sourceAtlasReceipt ≡ false
sourceAtlasReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse sourceAtlasReceipt
