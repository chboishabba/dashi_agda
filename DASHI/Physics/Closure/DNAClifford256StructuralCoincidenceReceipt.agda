module DASHI.Physics.Closure.DNAClifford256StructuralCoincidenceReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import Ontology.DNA.Supervoxel4Adic as DNA

------------------------------------------------------------------------
-- DNA / Clifford 256 structural coincidence receipt.
--
-- This answers the narrow "doesn't our DNA stuff have 256 too?" question in a
-- checked, non-promoting way.  The DNA side has a real 4-adic 256 carrier:
-- `DNA256` and `FlatDNA256`.  The Clifford side is recorded only as structural
-- arithmetic: `2^8 = 256`, and a 16-by-16 matrix has 256 entries.  This module
-- deliberately does not claim that DNA256 derives Clifford structure, that
-- Cl(7) has 256 basis blades, or that either lane proves physics.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

pow2 : Nat → Nat
pow2 zero =
  1
pow2 (suc n) =
  2 * pow2 n

pow4 : Nat → Nat
pow4 zero =
  1
pow4 (suc n) =
  4 * pow4 n

pow2-7-is-128 : pow2 7 ≡ 128
pow2-7-is-128 =
  refl

pow2-8-is-256 : pow2 8 ≡ 256
pow2-8-is-256 =
  refl

pow4-4-is-256 : pow4 4 ≡ 256
pow4-4-is-256 =
  refl

matrix16Entries256 : 16 * 16 ≡ 256
matrix16Entries256 =
  refl

------------------------------------------------------------------------
-- Structural rows.

data Structural256Lane : Set where
  dnaFourAdicLane :
    Structural256Lane

  codonCandidate256Lane :
    Structural256Lane

  cliffordArithmeticLane :
    Structural256Lane

  promotionBoundaryLane :
    Structural256Lane

laneLabel : Structural256Lane → String
laneLabel dnaFourAdicLane =
  "DNA 4-adic 256 carrier"
laneLabel codonCandidate256Lane =
  "64-codon to Candidate256 audit namespace"
laneLabel cliffordArithmeticLane =
  "Clifford 256 arithmetic surface"
laneLabel promotionBoundaryLane =
  "non-promotion boundary"

data Structural256EvidenceKind : Set where
  flatDNA256Carrier :
    Structural256EvidenceKind

  dna256NestedCarrier :
    Structural256EvidenceKind

  codon64InjectsIntoCandidate256 :
    Structural256EvidenceKind

  cliffordEightBasisCount256 :
    Structural256EvidenceKind

  cliffordSevenMatrixEntryCount256 :
    Structural256EvidenceKind

  coincidenceOnlyNoPhysicsPromotion :
    Structural256EvidenceKind

evidenceLabel : Structural256EvidenceKind → String
evidenceLabel flatDNA256Carrier =
  "FlatDNA256 = Vec Base 256"
evidenceLabel dna256NestedCarrier =
  "DNA256 = Vec DNA64 4"
evidenceLabel codon64InjectsIntoCandidate256 =
  "64 codon slots embed into first 64 Candidate256 slots"
evidenceLabel cliffordEightBasisCount256 =
  "2^8 = 256 Clifford basis-count arithmetic"
evidenceLabel cliffordSevenMatrixEntryCount256 =
  "16 x 16 = 256 matrix-entry arithmetic often adjacent to Cl(7) representations"
evidenceLabel coincidenceOnlyNoPhysicsPromotion =
  "256 match is structural coincidence/support only"

record Structural256Row : Set where
  field
    lane :
      Structural256Lane

    laneText :
      String

    laneTextIsCanonical :
      laneText ≡ laneLabel lane

    evidenceKind :
      Structural256EvidenceKind

    evidenceText :
      String

    evidenceTextIsCanonical :
      evidenceText ≡ evidenceLabel evidenceKind

    localOwner :
      String

    checkedContent :
      String

    supportsCrossLaneAnalogy :
      Bool

    supportsCrossLaneAnalogyIsTrue :
      supportsCrossLaneAnalogy ≡ true

    promotesPhysicsClaim :
      Bool

    promotesPhysicsClaimIsFalse :
      promotesPhysicsClaim ≡ false

open Structural256Row public

mkStructural256Row :
  Structural256Lane →
  Structural256EvidenceKind →
  String →
  String →
  Structural256Row
mkStructural256Row lane evidence owner content =
  record
    { lane =
        lane
    ; laneText =
        laneLabel lane
    ; laneTextIsCanonical =
        refl
    ; evidenceKind =
        evidence
    ; evidenceText =
        evidenceLabel evidence
    ; evidenceTextIsCanonical =
        refl
    ; localOwner =
        owner
    ; checkedContent =
        content
    ; supportsCrossLaneAnalogy =
        true
    ; supportsCrossLaneAnalogyIsTrue =
        refl
    ; promotesPhysicsClaim =
        false
    ; promotesPhysicsClaimIsFalse =
        refl
    }

canonicalStructural256Rows : List Structural256Row
canonicalStructural256Rows =
  mkStructural256Row
    dnaFourAdicLane
    flatDNA256Carrier
    "Ontology.DNA.Supervoxel4Adic"
    "FlatDNA256 is the flat 256-base carrier"
  ∷ mkStructural256Row
    dnaFourAdicLane
    dna256NestedCarrier
    "Ontology.DNA.Supervoxel4Adic"
    "DNA256 is the fourth level of the 4 -> 16 -> 64 -> 256 hierarchy"
  ∷ mkStructural256Row
    codonCandidate256Lane
    codon64InjectsIntoCandidate256
    "Docs.DrosophilaCodonWitnessToCandidate256Map"
    "64 codon counts are mapped into the first 64 Candidate256 audit slots with slots 64..255 zero-filled"
  ∷ mkStructural256Row
    cliffordArithmeticLane
    cliffordEightBasisCount256
    "DASHI Clifford bridge surfaces"
    "the arithmetic basis-count pattern 2^8 = 256 is recorded as structural support only"
  ∷ mkStructural256Row
    cliffordArithmeticLane
    cliffordSevenMatrixEntryCount256
    "DASHI Clifford bridge surfaces"
    "a 16-by-16 matrix has 256 entries; this is distinct from claiming Cl(7) basis dimension is 256"
  ∷ mkStructural256Row
    promotionBoundaryLane
    coincidenceOnlyNoPhysicsPromotion
    "DASHI.Physics.Closure.DNAClifford256StructuralCoincidenceReceipt"
    "DNA 256 and Clifford-adjacent 256 arithmetic are cross-lane structural coincidences, not physics promotion"
  ∷ []

------------------------------------------------------------------------
-- Canonical receipt.

record DNAClifford256StructuralCoincidenceReceipt : Set₁ where
  field
    dnaFlat256Carrier :
      Set

    dnaFlat256CarrierIsLocal :
      dnaFlat256Carrier ≡ DNA.FlatDNA256

    dnaNested256Carrier :
      Set

    dnaNested256CarrierIsLocal :
      dnaNested256Carrier ≡ DNA.DNA256

    dnaFourAdicLevelSize :
      Nat

    dnaFourAdicLevelSizeIs256 :
      dnaFourAdicLevelSize ≡ 256

    codonSlotCount :
      Nat

    codonSlotCountIs64 :
      codonSlotCount ≡ 64

    candidateAuditSlotCount :
      Nat

    candidateAuditSlotCountIs256 :
      candidateAuditSlotCount ≡ 256

    cliffordEightBasisArithmetic :
      Nat

    cliffordEightBasisArithmeticIs256 :
      cliffordEightBasisArithmetic ≡ 256

    cliffordSevenFullBasisArithmetic :
      Nat

    cliffordSevenFullBasisArithmeticIs128 :
      cliffordSevenFullBasisArithmetic ≡ 128

    sixteenBySixteenMatrixEntries :
      Nat

    sixteenBySixteenMatrixEntriesIs256 :
      sixteenBySixteenMatrixEntries ≡ 256

    structuralRows :
      List Structural256Row

    structuralRowsAreCanonical :
      structuralRows ≡ canonicalStructural256Rows

    structuralRowCount :
      Nat

    structuralRowCountIs6 :
      structuralRowCount ≡ 6

    crossLaneAnalogyRecorded :
      Bool

    crossLaneAnalogyRecordedIsTrue :
      crossLaneAnalogyRecorded ≡ true

    cl7BasisDimensionClaim256Accepted :
      Bool

    cl7BasisDimensionClaim256AcceptedIsFalse :
      cl7BasisDimensionClaim256Accepted ≡ false

    dnaToCliffordDerivationPromoted :
      Bool

    dnaToCliffordDerivationPromotedIsFalse :
      dnaToCliffordDerivationPromoted ≡ false

    biologyPromotion :
      Bool

    biologyPromotionIsFalse :
      biologyPromotion ≡ false

    physicsPromotion :
      Bool

    physicsPromotionIsFalse :
      physicsPromotion ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    boundary :
      List String

open DNAClifford256StructuralCoincidenceReceipt public

canonicalDNAClifford256StructuralCoincidenceReceipt :
  DNAClifford256StructuralCoincidenceReceipt
canonicalDNAClifford256StructuralCoincidenceReceipt =
  record
    { dnaFlat256Carrier =
        DNA.FlatDNA256
    ; dnaFlat256CarrierIsLocal =
        refl
    ; dnaNested256Carrier =
        DNA.DNA256
    ; dnaNested256CarrierIsLocal =
        refl
    ; dnaFourAdicLevelSize =
        pow4 4
    ; dnaFourAdicLevelSizeIs256 =
        pow4-4-is-256
    ; codonSlotCount =
        64
    ; codonSlotCountIs64 =
        refl
    ; candidateAuditSlotCount =
        256
    ; candidateAuditSlotCountIs256 =
        refl
    ; cliffordEightBasisArithmetic =
        pow2 8
    ; cliffordEightBasisArithmeticIs256 =
        pow2-8-is-256
    ; cliffordSevenFullBasisArithmetic =
        pow2 7
    ; cliffordSevenFullBasisArithmeticIs128 =
        pow2-7-is-128
    ; sixteenBySixteenMatrixEntries =
        16 * 16
    ; sixteenBySixteenMatrixEntriesIs256 =
        matrix16Entries256
    ; structuralRows =
        canonicalStructural256Rows
    ; structuralRowsAreCanonical =
        refl
    ; structuralRowCount =
        6
    ; structuralRowCountIs6 =
        refl
    ; crossLaneAnalogyRecorded =
        true
    ; crossLaneAnalogyRecordedIsTrue =
        refl
    ; cl7BasisDimensionClaim256Accepted =
        false
    ; cl7BasisDimensionClaim256AcceptedIsFalse =
        refl
    ; dnaToCliffordDerivationPromoted =
        false
    ; dnaToCliffordDerivationPromotedIsFalse =
        refl
    ; biologyPromotion =
        false
    ; biologyPromotionIsFalse =
        refl
    ; physicsPromotion =
        false
    ; physicsPromotionIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; boundary =
        "DNA has a checked FlatDNA256 and nested DNA256 carrier in Ontology.DNA.Supervoxel4Adic"
        ∷ "The Drosophila codon witness maps 64 codon slots into a Candidate256 audit namespace"
        ∷ "Clifford-adjacent 256 support is arithmetic only: 2^8 = 256 or 16 x 16 matrix entries"
        ∷ "The receipt explicitly rejects a local Cl(7) basis-dimension-is-256 promotion; 2^7 = 128 is separately recorded"
        ∷ "No DNA-to-Clifford derivation, biology promotion, physics promotion, or terminal promotion is made"
        ∷ []
    }

canonicalStructural256RowCountIs6 :
  listCount canonicalStructural256Rows ≡ 6
canonicalStructural256RowCountIs6 =
  refl

canonicalDNAClifford256RowCountIs6 :
  structuralRowCount canonicalDNAClifford256StructuralCoincidenceReceipt
  ≡
  6
canonicalDNAClifford256RowCountIs6 =
  refl

canonicalDNAClifford256FlatCarrierLocal :
  dnaFlat256Carrier canonicalDNAClifford256StructuralCoincidenceReceipt
  ≡
  DNA.FlatDNA256
canonicalDNAClifford256FlatCarrierLocal =
  refl

canonicalDNAClifford256RejectsCl7Basis256 :
  cl7BasisDimensionClaim256Accepted
    canonicalDNAClifford256StructuralCoincidenceReceipt
  ≡
  false
canonicalDNAClifford256RejectsCl7Basis256 =
  refl

canonicalDNAClifford256TerminalFalse :
  terminalPromotion canonicalDNAClifford256StructuralCoincidenceReceipt
  ≡
  false
canonicalDNAClifford256TerminalFalse =
  refl
