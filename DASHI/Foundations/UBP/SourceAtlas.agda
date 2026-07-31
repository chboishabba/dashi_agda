module DASHI.Foundations.UBP.SourceAtlas where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Attributed sources used by the UBP boundary formalisation.
--
-- A bibliographic entry is provenance and calibration only.  Importing a
-- title, author, or DOI does not import the cited theorem into Agda and does
-- not promote any UBP physical or semantic interpretation.

data DOIStatus : Set where
  doiRecorded :
    String →
    DOIStatus

  noDOIRecordedInAtlas :
    DOIStatus

data SourceRelationship : Set where
  historicalCodingSource :
    SourceRelationship

  mogAndMathieuSource :
    SourceRelationship

  leechLatticeSource :
    SourceRelationship

  latticeReferenceSource :
    SourceRelationship

  grayMapSource :
    SourceRelationship

  verifiedIntervalArithmeticSource :
    SourceRelationship

  dimensionTwentyFourOptimalitySource :
    SourceRelationship

record SourceEntry : Set where
  constructor sourceEntry
  field
    author :
      String

    title :
      String

    publication :
      String

    year :
      Nat

    doiStatus :
      DOIStatus

    relationship :
      SourceRelationship

    relationshipReading :
      String

open SourceEntry public

sourceCount :
  List SourceEntry →
  Nat
sourceCount [] =
  zero
sourceCount (_ ∷ entries) =
  suc (sourceCount entries)

------------------------------------------------------------------------
-- Canonical attributed entries.

golayNotesOnDigitalCoding :
  SourceEntry
golayNotesOnDigitalCoding =
  sourceEntry
    "Marcel J. E. Golay"
    "Notes on Digital Coding"
    "Proceedings of the IRE 37, page 657"
    1949
    noDOIRecordedInAtlas
    historicalCodingSource
    "historical source for the binary and ternary Golay-code programme; this atlas does not treat the citation as a machine-checked construction"

curtisM24 :
  SourceEntry
curtisM24 =
  sourceEntry
    "R. T. Curtis"
    "A new combinatorial approach to M24"
    "Mathematical Proceedings of the Cambridge Philosophical Society 79(1), 25-42"
    1976
    (doiRecorded "10.1017/S0305004100052075")
    mogAndMathieuSource
    "source for the Miracle Octad Generator and the combinatorial M24 presentation; it does not identify a chosen MOG coordinate labelling with physical meaning"

leechNotesOnSpherePackings :
  SourceEntry
leechNotesOnSpherePackings =
  sourceEntry
    "John Leech"
    "Notes on Sphere Packings"
    "Canadian Journal of Mathematics 19, 251-267"
    1967
    (doiRecorded "10.4153/CJM-1967-017-0")
    leechLatticeSource
    "historical lattice source; the UBP boundary uses the rootless minimum-norm distinction only through an explicit witness"

conwaySloaneSpherePackings :
  SourceEntry
conwaySloaneSpherePackings =
  sourceEntry
    "J. H. Conway and N. J. A. Sloane"
    "Sphere Packings, Lattices and Groups, Third Edition"
    "Springer, Grundlehren der mathematischen Wissenschaften 290"
    1999
    (doiRecorded "10.1007/978-1-4757-6568-7")
    latticeReferenceSource
    "reference for Golay, MOG, Hexacode, Construction A, Leech-lattice and sporadic-group background; citation is not proof import"

hammonsKumarCalderbankSloaneSoleGrayMap :
  SourceEntry
hammonsKumarCalderbankSloaneSoleGrayMap =
  sourceEntry
    "A. Roger Hammons, P. Vijay Kumar, A. R. Calderbank, N. J. A. Sloane, and Patrick Sole"
    "The Z4-Linearity of Kerdock, Preparata, Goethals, and Related Codes"
    "IEEE Transactions on Information Theory 40(2), 301-319"
    1994
    (doiRecorded "10.1109/18.312154")
    grayMapSource
    "source for the Z4 Gray-map metric interface; Lee-Hamming isometry does not itself construct a semantic metric embedding"

daumasLesterMunozIntervalArithmetic :
  SourceEntry
daumasLesterMunozIntervalArithmetic =
  sourceEntry
    "Marc Daumas, David Lester, and Cesar Munoz"
    "Verified Real Number Calculations: A Library for Interval Arithmetic"
    "IEEE Transactions on Computers 58(2), 226-237"
    2009
    (doiRecorded "10.1109/TC.2008.213")
    verifiedIntervalArithmeticSource
    "source for rational interval certification of irrational real calculations; exact rational execution is separated from exact irrational representation"

cohnKumarMillerRadchenkoViazovskaDimension24 :
  SourceEntry
cohnKumarMillerRadchenkoViazovskaDimension24 =
  sourceEntry
    "Henry Cohn, Abhinav Kumar, Stephen D. Miller, Danylo Radchenko, and Maryna Viazovska"
    "The sphere packing problem in dimension 24"
    "Annals of Mathematics 185(3), 1017-1033"
    2017
    (doiRecorded "10.4007/annals.2017.185.3.8")
    dimensionTwentyFourOptimalitySource
    "source for optimality and uniqueness of the Leech packing in dimension 24; it supplies no UBP mass, vacuum, semantic, or manifestation interpretation"

canonicalUBPSources :
  List SourceEntry
canonicalUBPSources =
  golayNotesOnDigitalCoding
  ∷ curtisM24
  ∷ leechNotesOnSpherePackings
  ∷ conwaySloaneSpherePackings
  ∷ hammonsKumarCalderbankSloaneSoleGrayMap
  ∷ daumasLesterMunozIntervalArithmetic
  ∷ cohnKumarMillerRadchenkoViazovskaDimension24
  ∷ []

canonicalUBPSourceCount :
  Nat
canonicalUBPSourceCount =
  sourceCount canonicalUBPSources

canonicalUBPSourceCountIsSeven :
  canonicalUBPSourceCount ≡ 7
canonicalUBPSourceCountIsSeven =
  refl

canonicalUBPSourceReceipt :
  GenericReceipt.GenericReceipt
canonicalUBPSourceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "UBP mathematical source atlas"
    "DASHI.Foundations.UBP.SourceAtlas"
    "canonicalUBPSources"
    "authors, exact titles, publication contexts, DOI states, and formalisation relationships are attached to the UBP boundary tranche"
    "citations do not import external theorem proofs and do not promote physical, semantic, empirical, or metaphysical authority"
    "agda -i . DASHI/Foundations/UBP/SourceAtlas.agda"

canonicalUBPSourceReceiptNonPromoting :
  GenericReceipt.promotesClaim canonicalUBPSourceReceipt ≡ false
canonicalUBPSourceReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse canonicalUBPSourceReceipt
