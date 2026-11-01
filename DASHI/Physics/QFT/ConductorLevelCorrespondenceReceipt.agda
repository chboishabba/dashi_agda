module DASHI.Physics.QFT.ConductorLevelCorrespondenceReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Conductor/level correspondence receipt.
--
-- This receipt records only the conductor-level table.  It does not promote
-- any row to an exact Standard Model identification and does not promote
-- G_DHR ~= G_SM.  The p5 line is kept as an explicit gap: SU(2)_7 has a
-- level-rank SU(7)_2 partner, but its physical role remains open.

data PrimeLane : Set where
  p2 :
    PrimeLane

  p3 :
    PrimeLane

  p5 :
    PrimeLane

data FundamentalDiscriminant : Set where
  discMinus4 :
    FundamentalDiscriminant

  discMinus3 :
    FundamentalDiscriminant

  discMinus7 :
    FundamentalDiscriminant

data ChernSimonsCandidate : Set where
  su2Level :
    Nat -> ChernSimonsCandidate

data LevelRankPartner : Set where
  noLevelRankPartnerRecorded :
    LevelRankPartner

  su3Level1 :
    LevelRankPartner

  su7Level2 :
    LevelRankPartner

data PhysicalRoleCandidate : Set where
  fermionicSpinCandidate :
    PhysicalRoleCandidate

  weakColourCandidate :
    PhysicalRoleCandidate

  physicalRoleOpen :
    PhysicalRoleCandidate

data CorrespondenceStatus : Set where
  conductorLevelCandidateOnly :
    CorrespondenceStatus

data P5Gap : Set where
  p5PhysicalRoleNotIdentified :
    P5Gap

  p5NoExactSMGaugeFactorAssigned :
    P5Gap

  p5NoExactGDHRToGSMPromotion :
    P5Gap

canonicalP5Gaps :
  List P5Gap
canonicalP5Gaps =
  p5PhysicalRoleNotIdentified
  ∷ p5NoExactSMGaugeFactorAssigned
  ∷ p5NoExactGDHRToGSMPromotion
  ∷ []

record ConductorLevelRow : Set where
  field
    primeLane :
      PrimeLane

    discriminant :
      FundamentalDiscriminant

    conductor :
      Nat

    csCandidate :
      ChernSimonsCandidate

    csLevel :
      Nat

    csCandidateMatchesLevel :
      csCandidate ≡ su2Level csLevel

    levelRankPartner :
      LevelRankPartner

    physicalRole :
      PhysicalRoleCandidate

    rowStatus :
      CorrespondenceStatus

open ConductorLevelRow public

p2ConductorLevelRow :
  ConductorLevelRow
p2ConductorLevelRow =
  record
    { primeLane =
        p2
    ; discriminant =
        discMinus4
    ; conductor =
        4
    ; csCandidate =
        su2Level 4
    ; csLevel =
        4
    ; csCandidateMatchesLevel =
        refl
    ; levelRankPartner =
        noLevelRankPartnerRecorded
    ; physicalRole =
        fermionicSpinCandidate
    ; rowStatus =
        conductorLevelCandidateOnly
    }

p3ConductorLevelRow :
  ConductorLevelRow
p3ConductorLevelRow =
  record
    { primeLane =
        p3
    ; discriminant =
        discMinus3
    ; conductor =
        3
    ; csCandidate =
        su2Level 3
    ; csLevel =
        3
    ; csCandidateMatchesLevel =
        refl
    ; levelRankPartner =
        su3Level1
    ; physicalRole =
        weakColourCandidate
    ; rowStatus =
        conductorLevelCandidateOnly
    }

p5ConductorLevelRow :
  ConductorLevelRow
p5ConductorLevelRow =
  record
    { primeLane =
        p5
    ; discriminant =
        discMinus7
    ; conductor =
        7
    ; csCandidate =
        su2Level 7
    ; csLevel =
        7
    ; csCandidateMatchesLevel =
        refl
    ; levelRankPartner =
        su7Level2
    ; physicalRole =
        physicalRoleOpen
    ; rowStatus =
        conductorLevelCandidateOnly
    }

canonicalConductorLevelRows :
  List ConductorLevelRow
canonicalConductorLevelRows =
  p2ConductorLevelRow
  ∷ p3ConductorLevelRow
  ∷ p5ConductorLevelRow
  ∷ []

p2TableLabel : String
p2TableLabel =
  "p2: disc -4, conductor 4, Chern-Simons level SU(2)_4, fermionic spin candidate"

p3TableLabel : String
p3TableLabel =
  "p3: disc -3, conductor 3, SU(2)_3 <-> SU(3)_1, weak/colour candidate"

p5TableLabel : String
p5TableLabel =
  "p5: disc -7, conductor 7, SU(2)_7 with level-rank SU(7)_2; physical role open"

p5GapLabel : String
p5GapLabel =
  "p5 gap: SU(2)_7 <-> SU(7)_2 is recorded, but no exact weak, colour, hypercharge, SM, or G_DHR ~= G_SM promotion is supplied"

record ConductorLevelCorrespondenceReceipt : Set where
  field
    status :
      CorrespondenceStatus

    rows :
      List ConductorLevelRow

    rowsAreCanonical :
      rows ≡ canonicalConductorLevelRows

    p2Row :
      ConductorLevelRow

    p2RowIsCanonical :
      p2Row ≡ p2ConductorLevelRow

    p2DiscriminantIsMinus4 :
      discriminant p2Row ≡ discMinus4

    p2ConductorIs4 :
      conductor p2Row ≡ 4

    p2CSLevelIs4 :
      csLevel p2Row ≡ 4

    p2PhysicalRoleIsFermionicSpinCandidate :
      physicalRole p2Row ≡ fermionicSpinCandidate

    p3Row :
      ConductorLevelRow

    p3RowIsCanonical :
      p3Row ≡ p3ConductorLevelRow

    p3DiscriminantIsMinus3 :
      discriminant p3Row ≡ discMinus3

    p3ConductorIs3 :
      conductor p3Row ≡ 3

    p3CSLevelIs3 :
      csLevel p3Row ≡ 3

    p3LevelRankPartnerIsSU3Level1 :
      levelRankPartner p3Row ≡ su3Level1

    p3PhysicalRoleIsWeakColourCandidate :
      physicalRole p3Row ≡ weakColourCandidate

    p5Row :
      ConductorLevelRow

    p5RowIsCanonical :
      p5Row ≡ p5ConductorLevelRow

    p5DiscriminantIsMinus7 :
      discriminant p5Row ≡ discMinus7

    p5ConductorIs7 :
      conductor p5Row ≡ 7

    p5CSLevelIs7 :
      csLevel p5Row ≡ 7

    p5LevelRankPartnerIsSU7Level2 :
      levelRankPartner p5Row ≡ su7Level2

    p5PhysicalRoleIsOpen :
      physicalRole p5Row ≡ physicalRoleOpen

    p5Gaps :
      List P5Gap

    p5GapsAreCanonical :
      p5Gaps ≡ canonicalP5Gaps

    p2Label :
      String

    p2LabelIsCanonical :
      p2Label ≡ p2TableLabel

    p3Label :
      String

    p3LabelIsCanonical :
      p3Label ≡ p3TableLabel

    p5Label :
      String

    p5LabelIsCanonical :
      p5Label ≡ p5TableLabel

    p5GapStatement :
      String

    p5GapStatementIsCanonical :
      p5GapStatement ≡ p5GapLabel

    exactSMGaugeFactorPromotion :
      Bool

    exactSMGaugeFactorPromotionIsFalse :
      exactSMGaugeFactorPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    receiptBoundary :
      List String

open ConductorLevelCorrespondenceReceipt public

canonicalConductorLevelCorrespondenceReceipt :
  ConductorLevelCorrespondenceReceipt
canonicalConductorLevelCorrespondenceReceipt =
  record
    { status =
        conductorLevelCandidateOnly
    ; rows =
        canonicalConductorLevelRows
    ; rowsAreCanonical =
        refl
    ; p2Row =
        p2ConductorLevelRow
    ; p2RowIsCanonical =
        refl
    ; p2DiscriminantIsMinus4 =
        refl
    ; p2ConductorIs4 =
        refl
    ; p2CSLevelIs4 =
        refl
    ; p2PhysicalRoleIsFermionicSpinCandidate =
        refl
    ; p3Row =
        p3ConductorLevelRow
    ; p3RowIsCanonical =
        refl
    ; p3DiscriminantIsMinus3 =
        refl
    ; p3ConductorIs3 =
        refl
    ; p3CSLevelIs3 =
        refl
    ; p3LevelRankPartnerIsSU3Level1 =
        refl
    ; p3PhysicalRoleIsWeakColourCandidate =
        refl
    ; p5Row =
        p5ConductorLevelRow
    ; p5RowIsCanonical =
        refl
    ; p5DiscriminantIsMinus7 =
        refl
    ; p5ConductorIs7 =
        refl
    ; p5CSLevelIs7 =
        refl
    ; p5LevelRankPartnerIsSU7Level2 =
        refl
    ; p5PhysicalRoleIsOpen =
        refl
    ; p5Gaps =
        canonicalP5Gaps
    ; p5GapsAreCanonical =
        refl
    ; p2Label =
        p2TableLabel
    ; p2LabelIsCanonical =
        refl
    ; p3Label =
        p3TableLabel
    ; p3LabelIsCanonical =
        refl
    ; p5Label =
        p5TableLabel
    ; p5LabelIsCanonical =
        refl
    ; p5GapStatement =
        p5GapLabel
    ; p5GapStatementIsCanonical =
        refl
    ; exactSMGaugeFactorPromotion =
        false
    ; exactSMGaugeFactorPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; receiptBoundary =
        p2TableLabel
        ∷ p3TableLabel
        ∷ p5TableLabel
        ∷ p5GapLabel
        ∷ "All rows are conductor-level candidates only; no exact SM or G_DHR ~= G_SM promotion is made"
        ∷ []
    }

conductorLevelP5PhysicalRoleOpen :
  p5PhysicalRoleIsOpen canonicalConductorLevelCorrespondenceReceipt
  ≡
  refl
conductorLevelP5PhysicalRoleOpen =
  refl

conductorLevelNoExactSMPromotion :
  exactSMGaugeFactorPromotion canonicalConductorLevelCorrespondenceReceipt
  ≡
  false
conductorLevelNoExactSMPromotion =
  refl

conductorLevelNoExactGDHRGSMPromotion :
  exactGDHREqualsGSMPromotion canonicalConductorLevelCorrespondenceReceipt
  ≡
  false
conductorLevelNoExactGDHRGSMPromotion =
  refl
