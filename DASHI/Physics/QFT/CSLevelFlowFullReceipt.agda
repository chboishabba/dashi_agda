module DASHI.Physics.QFT.CSLevelFlowFullReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Full Chern-Simons level-flow receipt.
--
-- This receipt compiles the current candidate picture for the three active
-- prime lanes.  It is bookkeeping for candidate level flow only:
--
--   * p2: SU(2)_4 may flow to SU(2)_1 if three Dirac fundamentals are
--     integrated out.  This is conditional/candidate data.
--   * p3: SU(2)_3 is paired with the requested SU(3)_1 colour-side candidate
--     by the existing level-rank/colour diagnostic surface.  The SU(3)_1
--     level is recorded as protected/fixed in this candidate TQFT reading.
--   * p5: SU(2)_7 has a formal SU(7)_2 level-rank partner, but no clear
--     Standard Model role is identified.
--
-- No exact SU(2)_L, SU(3)_c, Standard Model, G_DHR ~= G_SM, or terminal
-- promotion is made here.

data PrimeLane : Set where
  p2Lane :
    PrimeLane

  p3Lane :
    PrimeLane

  p5Lane :
    PrimeLane

data CSCandidateTheory : Set where
  su2Level :
    Nat →
    CSCandidateTheory

  su3Level :
    Nat →
    CSCandidateTheory

  su7Level :
    Nat →
    CSCandidateTheory

data LevelFlowStatus : Set where
  candidateFlowOnly :
    LevelFlowStatus

  protectedLevelCandidate :
    LevelFlowStatus

  openPhysicalRole :
    LevelFlowStatus

data LevelFlowCondition : Set where
  conditionalOnIntegratingOutThreeDiracFundamentals :
    LevelFlowCondition

  conditionalOnLevelRankColourReading :
    LevelFlowCondition

  p5SMRoleUnidentified :
    LevelFlowCondition

canonicalLevelFlowConditions :
  List LevelFlowCondition
canonicalLevelFlowConditions =
  conditionalOnIntegratingOutThreeDiracFundamentals
  ∷ conditionalOnLevelRankColourReading
  ∷ p5SMRoleUnidentified
  ∷ []

data ResidualLevelFlowBlocker : Set where
  exactSU2LNotConstructed :
    ResidualLevelFlowBlocker

  exactSU3cNotConstructed :
    ResidualLevelFlowBlocker

  exactStandardModelNotConstructed :
    ResidualLevelFlowBlocker

  exactGDHRGSMNotConstructed :
    ResidualLevelFlowBlocker

  terminalCompositionNotConstructed :
    ResidualLevelFlowBlocker

canonicalResidualLevelFlowBlockers :
  List ResidualLevelFlowBlocker
canonicalResidualLevelFlowBlockers =
  exactSU2LNotConstructed
  ∷ exactSU3cNotConstructed
  ∷ exactStandardModelNotConstructed
  ∷ exactGDHRGSMNotConstructed
  ∷ terminalCompositionNotConstructed
  ∷ []

record CSLevelFlowRow : Set where
  field
    lane :
      PrimeLane

    sourceTheory :
      CSCandidateTheory

    sourceLevel :
      Nat

    sourceTheoryMatchesLevel :
      sourceTheory ≡ su2Level sourceLevel

    effectiveTheory :
      CSCandidateTheory

    effectiveLevel :
      Nat

    rowStatus :
      LevelFlowStatus

    rowCondition :
      LevelFlowCondition

    rowStatement :
      String

open CSLevelFlowRow public

p2FlowStatement :
  String
p2FlowStatement =
  "p2-lane SU(2)_4 candidate can flow to SU(2)_1 if three Dirac fundamentals are integrated out; candidate only"

p3FlowStatement :
  String
p3FlowStatement =
  "p3-lane SU(2)_3 is recorded with the requested SU(3)_1 colour-side level-rank candidate; SU(3)_1 level is protected/fixed in this TQFT reading"

p5FlowStatement :
  String
p5FlowStatement =
  "p5-lane SU(2)_7 has formal SU(7)_2 level-rank partner but no clear Standard Model role"

promotionBoundaryStatement :
  String
promotionBoundaryStatement =
  "exact SU(2)_L, SU(3)_c, Standard Model, G_DHR ~= G_SM, and terminal promotions remain false"

p2LevelFlowRow :
  CSLevelFlowRow
p2LevelFlowRow =
  record
    { lane =
        p2Lane
    ; sourceTheory =
        su2Level 4
    ; sourceLevel =
        4
    ; sourceTheoryMatchesLevel =
        refl
    ; effectiveTheory =
        su2Level 1
    ; effectiveLevel =
        1
    ; rowStatus =
        candidateFlowOnly
    ; rowCondition =
        conditionalOnIntegratingOutThreeDiracFundamentals
    ; rowStatement =
        p2FlowStatement
    }

p3LevelFlowRow :
  CSLevelFlowRow
p3LevelFlowRow =
  record
    { lane =
        p3Lane
    ; sourceTheory =
        su2Level 3
    ; sourceLevel =
        3
    ; sourceTheoryMatchesLevel =
        refl
    ; effectiveTheory =
        su3Level 1
    ; effectiveLevel =
        1
    ; rowStatus =
        protectedLevelCandidate
    ; rowCondition =
        conditionalOnLevelRankColourReading
    ; rowStatement =
        p3FlowStatement
    }

p5LevelFlowRow :
  CSLevelFlowRow
p5LevelFlowRow =
  record
    { lane =
        p5Lane
    ; sourceTheory =
        su2Level 7
    ; sourceLevel =
        7
    ; sourceTheoryMatchesLevel =
        refl
    ; effectiveTheory =
        su7Level 2
    ; effectiveLevel =
        2
    ; rowStatus =
        openPhysicalRole
    ; rowCondition =
        p5SMRoleUnidentified
    ; rowStatement =
        p5FlowStatement
    }

canonicalCSLevelFlowRows :
  List CSLevelFlowRow
canonicalCSLevelFlowRows =
  p2LevelFlowRow
  ∷ p3LevelFlowRow
  ∷ p5LevelFlowRow
  ∷ []

record CSLevelFlowFullReceipt : Set where
  field
    rows :
      List CSLevelFlowRow

    rowsAreCanonical :
      rows ≡ canonicalCSLevelFlowRows

    p2Row :
      CSLevelFlowRow

    p2RowIsCanonical :
      p2Row ≡ p2LevelFlowRow

    p2SourceLevelIsFour :
      sourceLevel p2Row ≡ 4

    p2EffectiveLevelIsOne :
      effectiveLevel p2Row ≡ 1

    p2FlowIsCandidateOnly :
      rowStatus p2Row ≡ candidateFlowOnly

    p2ConditionIsThreeDiracFundamentals :
      rowCondition p2Row ≡ conditionalOnIntegratingOutThreeDiracFundamentals

    p2Statement :
      String

    p2StatementIsCanonical :
      p2Statement ≡ p2FlowStatement

    p3Row :
      CSLevelFlowRow

    p3RowIsCanonical :
      p3Row ≡ p3LevelFlowRow

    p3SourceLevelIsThree :
      sourceLevel p3Row ≡ 3

    p3ColourLevelIsOne :
      effectiveLevel p3Row ≡ 1

    p3LevelProtectedCandidate :
      rowStatus p3Row ≡ protectedLevelCandidate

    p3ConditionIsLevelRankColour :
      rowCondition p3Row ≡ conditionalOnLevelRankColourReading

    p3Statement :
      String

    p3StatementIsCanonical :
      p3Statement ≡ p3FlowStatement

    p5Row :
      CSLevelFlowRow

    p5RowIsCanonical :
      p5Row ≡ p5LevelFlowRow

    p5SourceLevelIsSeven :
      sourceLevel p5Row ≡ 7

    p5FormalPartnerLevelIsTwo :
      effectiveLevel p5Row ≡ 2

    p5RoleOpen :
      rowStatus p5Row ≡ openPhysicalRole

    p5ConditionIsRoleUnidentified :
      rowCondition p5Row ≡ p5SMRoleUnidentified

    p5Statement :
      String

    p5StatementIsCanonical :
      p5Statement ≡ p5FlowStatement

    conditions :
      List LevelFlowCondition

    conditionsAreCanonical :
      conditions ≡ canonicalLevelFlowConditions

    blockers :
      List ResidualLevelFlowBlocker

    blockersAreCanonical :
      blockers ≡ canonicalResidualLevelFlowBlockers

    p2FlowToSU2OneCandidate :
      Bool

    p2FlowToSU2OneCandidateIsTrue :
      p2FlowToSU2OneCandidate ≡ true

    p3SU3OneLevelProtectedCandidate :
      Bool

    p3SU3OneLevelProtectedCandidateIsTrue :
      p3SU3OneLevelProtectedCandidate ≡ true

    p5HasNoClearSMRole :
      Bool

    p5HasNoClearSMRoleIsTrue :
      p5HasNoClearSMRole ≡ true

    exactSU2LPromotion :
      Bool

    exactSU2LPromotionIsFalse :
      exactSU2LPromotion ≡ false

    exactSU3cPromotion :
      Bool

    exactSU3cPromotionIsFalse :
      exactSU3cPromotion ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    terminalCompositionPromotion :
      Bool

    terminalCompositionPromotionIsFalse :
      terminalCompositionPromotion ≡ false

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary
      ≡
      (p2FlowStatement
       ∷ p3FlowStatement
       ∷ p5FlowStatement
       ∷ promotionBoundaryStatement
       ∷ [])

open CSLevelFlowFullReceipt public

canonicalCSLevelFlowFullReceipt :
  CSLevelFlowFullReceipt
canonicalCSLevelFlowFullReceipt =
  record
    { rows =
        canonicalCSLevelFlowRows
    ; rowsAreCanonical =
        refl
    ; p2Row =
        p2LevelFlowRow
    ; p2RowIsCanonical =
        refl
    ; p2SourceLevelIsFour =
        refl
    ; p2EffectiveLevelIsOne =
        refl
    ; p2FlowIsCandidateOnly =
        refl
    ; p2ConditionIsThreeDiracFundamentals =
        refl
    ; p2Statement =
        p2FlowStatement
    ; p2StatementIsCanonical =
        refl
    ; p3Row =
        p3LevelFlowRow
    ; p3RowIsCanonical =
        refl
    ; p3SourceLevelIsThree =
        refl
    ; p3ColourLevelIsOne =
        refl
    ; p3LevelProtectedCandidate =
        refl
    ; p3ConditionIsLevelRankColour =
        refl
    ; p3Statement =
        p3FlowStatement
    ; p3StatementIsCanonical =
        refl
    ; p5Row =
        p5LevelFlowRow
    ; p5RowIsCanonical =
        refl
    ; p5SourceLevelIsSeven =
        refl
    ; p5FormalPartnerLevelIsTwo =
        refl
    ; p5RoleOpen =
        refl
    ; p5ConditionIsRoleUnidentified =
        refl
    ; p5Statement =
        p5FlowStatement
    ; p5StatementIsCanonical =
        refl
    ; conditions =
        canonicalLevelFlowConditions
    ; conditionsAreCanonical =
        refl
    ; blockers =
        canonicalResidualLevelFlowBlockers
    ; blockersAreCanonical =
        refl
    ; p2FlowToSU2OneCandidate =
        true
    ; p2FlowToSU2OneCandidateIsTrue =
        refl
    ; p3SU3OneLevelProtectedCandidate =
        true
    ; p3SU3OneLevelProtectedCandidateIsTrue =
        refl
    ; p5HasNoClearSMRole =
        true
    ; p5HasNoClearSMRoleIsTrue =
        refl
    ; exactSU2LPromotion =
        false
    ; exactSU2LPromotionIsFalse =
        refl
    ; exactSU3cPromotion =
        false
    ; exactSU3cPromotionIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; terminalCompositionPromotion =
        false
    ; terminalCompositionPromotionIsFalse =
        refl
    ; receiptBoundary =
        p2FlowStatement
        ∷ p3FlowStatement
        ∷ p5FlowStatement
        ∷ promotionBoundaryStatement
        ∷ []
    ; receiptBoundaryIsCanonical =
        refl
    }

csLevelFlowP2BareLevelIsFour :
  sourceLevel (p2Row canonicalCSLevelFlowFullReceipt)
  ≡
  4
csLevelFlowP2BareLevelIsFour =
  p2SourceLevelIsFour canonicalCSLevelFlowFullReceipt

csLevelFlowP2EffectiveLevelIsOne :
  effectiveLevel (p2Row canonicalCSLevelFlowFullReceipt)
  ≡
  1
csLevelFlowP2EffectiveLevelIsOne =
  p2EffectiveLevelIsOne canonicalCSLevelFlowFullReceipt

csLevelFlowP3BareLevelIsThree :
  sourceLevel (p3Row canonicalCSLevelFlowFullReceipt)
  ≡
  3
csLevelFlowP3BareLevelIsThree =
  p3SourceLevelIsThree canonicalCSLevelFlowFullReceipt

csLevelFlowP3ColourLevelIsOne :
  effectiveLevel (p3Row canonicalCSLevelFlowFullReceipt)
  ≡
  1
csLevelFlowP3ColourLevelIsOne =
  p3ColourLevelIsOne canonicalCSLevelFlowFullReceipt

csLevelFlowP5BareLevelIsSeven :
  sourceLevel (p5Row canonicalCSLevelFlowFullReceipt)
  ≡
  7
csLevelFlowP5BareLevelIsSeven =
  p5SourceLevelIsSeven canonicalCSLevelFlowFullReceipt

csLevelFlowP5FormalPartnerLevelIsTwo :
  effectiveLevel (p5Row canonicalCSLevelFlowFullReceipt)
  ≡
  2
csLevelFlowP5FormalPartnerLevelIsTwo =
  p5FormalPartnerLevelIsTwo canonicalCSLevelFlowFullReceipt

csLevelFlowP2CandidateOnly :
  p2FlowToSU2OneCandidate canonicalCSLevelFlowFullReceipt
  ≡
  true
csLevelFlowP2CandidateOnly =
  p2FlowToSU2OneCandidateIsTrue canonicalCSLevelFlowFullReceipt

csLevelFlowP3SU3OneProtectedCandidate :
  p3SU3OneLevelProtectedCandidate canonicalCSLevelFlowFullReceipt
  ≡
  true
csLevelFlowP3SU3OneProtectedCandidate =
  p3SU3OneLevelProtectedCandidateIsTrue canonicalCSLevelFlowFullReceipt

csLevelFlowP5RoleOpen :
  p5HasNoClearSMRole canonicalCSLevelFlowFullReceipt
  ≡
  true
csLevelFlowP5RoleOpen =
  p5HasNoClearSMRoleIsTrue canonicalCSLevelFlowFullReceipt

csLevelFlowDoesNotPromoteExactSU2L :
  exactSU2LPromotion canonicalCSLevelFlowFullReceipt
  ≡
  false
csLevelFlowDoesNotPromoteExactSU2L =
  exactSU2LPromotionIsFalse canonicalCSLevelFlowFullReceipt

csLevelFlowDoesNotPromoteExactSU3c :
  exactSU3cPromotion canonicalCSLevelFlowFullReceipt
  ≡
  false
csLevelFlowDoesNotPromoteExactSU3c =
  exactSU3cPromotionIsFalse canonicalCSLevelFlowFullReceipt

csLevelFlowDoesNotPromoteExactSM :
  exactStandardModelPromotion canonicalCSLevelFlowFullReceipt
  ≡
  false
csLevelFlowDoesNotPromoteExactSM =
  exactStandardModelPromotionIsFalse canonicalCSLevelFlowFullReceipt

csLevelFlowDoesNotPromoteExactGDHR :
  exactGDHREqualsGSMPromotion canonicalCSLevelFlowFullReceipt
  ≡
  false
csLevelFlowDoesNotPromoteExactGDHR =
  exactGDHREqualsGSMPromotionIsFalse canonicalCSLevelFlowFullReceipt

csLevelFlowDoesNotPromoteTerminalComposition :
  terminalCompositionPromotion canonicalCSLevelFlowFullReceipt
  ≡
  false
csLevelFlowDoesNotPromoteTerminalComposition =
  terminalCompositionPromotionIsFalse canonicalCSLevelFlowFullReceipt
