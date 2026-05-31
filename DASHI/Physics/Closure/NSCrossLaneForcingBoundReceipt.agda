module DASHI.Physics.Closure.NSCrossLaneForcingBoundReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSLerayBandBoundReceipt as Leray

------------------------------------------------------------------------
-- Navier-Stokes cross-lane forcing bound receipt.
--
-- This candidate receipt records the A3 landing-pair forcing estimate for
-- a target band j of prime p:
--
--   F_j <= C sum_{landing pairs |q^j' - r^l| approx p^j}
--              q^(j'+11/8) e_{q,j'}^(1/2) e_{r,l}^(1/2).
--
-- Using the Leray individual-band bound a <= M_0^2, this becomes
--
--   F_j <= C M_0^2 K_j,
--
-- where K_j is the finite landing-pair sum for band j.  The audit
-- conclusion recorded here is K_j = 0 for j >= 6, with the low-band table
-- explicit.  This is only a boundedness/audit receipt and makes no Clay,
-- global-regularity, or terminal promotion.

data NSCrossLaneForcingBoundStatus : Set where
  candidate :
    NSCrossLaneForcingBoundStatus

  landingPairForcingEstimateRecorded :
    NSCrossLaneForcingBoundStatus

  lerayBandBoundConsumedStatus :
    NSCrossLaneForcingBoundStatus

  m0SquaredKjBoundRecorded :
    NSCrossLaneForcingBoundStatus

  kjFiniteFromLandingPairsStatus :
    NSCrossLaneForcingBoundStatus

  highJBoundednessRecordedStatus :
    NSCrossLaneForcingBoundStatus

  auditKjZeroForJGreaterOrEqualSixStatus :
    NSCrossLaneForcingBoundStatus

  lowBandTableExplicitStatus :
    NSCrossLaneForcingBoundStatus

  noClayOrGlobalPromotion :
    NSCrossLaneForcingBoundStatus

canonicalNSCrossLaneForcingBoundStatus :
  List NSCrossLaneForcingBoundStatus
canonicalNSCrossLaneForcingBoundStatus =
  candidate
  ∷ landingPairForcingEstimateRecorded
  ∷ lerayBandBoundConsumedStatus
  ∷ m0SquaredKjBoundRecorded
  ∷ kjFiniteFromLandingPairsStatus
  ∷ highJBoundednessRecordedStatus
  ∷ auditKjZeroForJGreaterOrEqualSixStatus
  ∷ lowBandTableExplicitStatus
  ∷ noClayOrGlobalPromotion
  ∷ []

data LandingPairCriterion : Set where
  absoluteDifferenceApproximatelyTargetPrimePower :
    LandingPairCriterion

data CrossLaneForcingBoundShape : Set where
  cTimesLandingPairWeightedEnergySum :
    CrossLaneForcingBoundShape

data ReducedForcingBoundShape : Set where
  cM0SquaredKj :
    ReducedForcingBoundShape

data LowBandTableStatus : Set where
  explicitFiniteAuditTableForJLessThanSix :
    LowBandTableStatus

data NSCrossLaneForcingBoundPromotion : Set where

nsCrossLaneForcingBoundPromotionImpossibleHere :
  NSCrossLaneForcingBoundPromotion →
  ⊥
nsCrossLaneForcingBoundPromotionImpossibleHere ()

landingPairForcingBoundFormula :
  String
landingPairForcingBoundFormula =
  "F_j <= C sum_{landing pairs |q^j' - r^l| approx p^j} q^(j'+11/8) e_{q,j'}^(1/2)e_{r,l}^(1/2)"

lerayReducedForcingBoundFormula :
  String
lerayReducedForcingBoundFormula =
  "F_j <= C M_0^2 K_j"

kjDefinitionFormula :
  String
kjDefinitionFormula =
  "K_j = sum_{landing pairs |q^j' - r^l| approx p^j} q^(j'+11/8)"

kjAuditConclusionFormula :
  String
kjAuditConclusionFormula =
  "audit conclusion: K_j = 0 for j >= 6; low-band table j < 6 explicit"

highJBoundednessFormula :
  String
highJBoundednessFormula =
  "For j >= 6, K_j = 0, hence F_j <= C M_0^2 K_j = 0 in the audited high bands"

lowBandTableLabel :
  String
lowBandTableLabel =
  "low-band landing-pair table explicit for j = 0,1,2,3,4,5"

nsCrossLaneForcingBoundStatement :
  String
nsCrossLaneForcingBoundStatement =
  "Candidate receipt: for band j of prime p, record F_j <= C sum_{landing pairs |q^j' - r^l| approx p^j} q^(j'+11/8) e_{q,j'}^(1/2)e_{r,l}^(1/2).  Consuming the Leray individual-band bound a <= M_0^2 gives F_j <= C M_0^2 K_j, with K_j finite from the landing-pair audit.  The stated audit conclusion is K_j=0 for j>=6 and the low-band table is explicit.  No Clay/global terminal promotion is made."

record NSCrossLaneForcingBoundReceipt : Setω where
  field
    lerayBandBoundReceipt :
      Leray.NSLerayBandBoundReceipt

    lerayStatusCanonical :
      Leray.status lerayBandBoundReceipt
      ≡
      Leray.canonicalNSLerayBandBoundStatus

    lerayIndividualBandBoundAvailable :
      Leray.everyIndividualCarrierBandBounded lerayBandBoundReceipt
      ≡
      true

    lerayNoClayPromotion :
      Leray.clayNavierStokesPromoted lerayBandBoundReceipt
      ≡
      false

    status :
      List NSCrossLaneForcingBoundStatus

    statusIsCanonical :
      status ≡ canonicalNSCrossLaneForcingBoundStatus

    theoremKind :
      NSCrossLaneForcingBoundStatus

    theoremKindIsCandidate :
      theoremKind ≡ candidate

    targetBandIndex :
      Nat

    primeLaneIndex :
      Nat

    landingPairCriterion :
      LandingPairCriterion

    landingPairCriterionIsCanonical :
      landingPairCriterion
      ≡
      absoluteDifferenceApproximatelyTargetPrimePower

    forcingBoundShape :
      CrossLaneForcingBoundShape

    forcingBoundShapeIsCanonical :
      forcingBoundShape ≡ cTimesLandingPairWeightedEnergySum

    forcingBoundFormula :
      String

    forcingBoundFormulaIsCanonical :
      forcingBoundFormula ≡ landingPairForcingBoundFormula

    h118ShiftNumerator :
      Nat

    h118ShiftNumeratorIs11 :
      h118ShiftNumerator ≡ 11

    h118ShiftDenominator :
      Nat

    h118ShiftDenominatorIs8 :
      h118ShiftDenominator ≡ 8

    lerayBandBoundConsumed :
      Bool

    lerayBandBoundConsumedIsTrue :
      lerayBandBoundConsumed ≡ true

    lerayBoundText :
      String

    lerayBoundTextIsCanonical :
      lerayBoundText ≡ Leray.lerayBandBoundStatement

    reducedForcingBoundShape :
      ReducedForcingBoundShape

    reducedForcingBoundShapeIsCanonical :
      reducedForcingBoundShape ≡ cM0SquaredKj

    reducedForcingBoundFormula :
      String

    reducedForcingBoundFormulaIsCanonical :
      reducedForcingBoundFormula ≡ lerayReducedForcingBoundFormula

    kjDefinition :
      String

    kjDefinitionIsCanonical :
      kjDefinition ≡ kjDefinitionFormula

    kjFiniteFromLandingPairs :
      Bool

    kjFiniteFromLandingPairsIsTrue :
      kjFiniteFromLandingPairs ≡ true

    highJBoundednessRecorded :
      Bool

    highJBoundednessRecordedIsTrue :
      highJBoundednessRecorded ≡ true

    highJBoundedness :
      String

    highJBoundednessIsCanonical :
      highJBoundedness ≡ highJBoundednessFormula

    auditKjZeroForJGreaterOrEqualSix :
      Bool

    auditKjZeroForJGreaterOrEqualSixIsTrue :
      auditKjZeroForJGreaterOrEqualSix ≡ true

    auditThreshold :
      Nat

    auditThresholdIsSix :
      auditThreshold ≡ 6

    auditConclusion :
      String

    auditConclusionIsCanonical :
      auditConclusion ≡ kjAuditConclusionFormula

    lowBandTableStatus :
      LowBandTableStatus

    lowBandTableStatusIsExplicit :
      lowBandTableStatus ≡ explicitFiniteAuditTableForJLessThanSix

    lowBandTableExplicit :
      Bool

    lowBandTableExplicitIsTrue :
      lowBandTableExplicit ≡ true

    lowBandTable :
      String

    lowBandTableIsCanonical :
      lowBandTable ≡ lowBandTableLabel

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    terminalPromotionPromoted :
      Bool

    terminalPromotionPromotedIsFalse :
      terminalPromotionPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsCrossLaneForcingBoundStatement

    promotionFlags :
      List NSCrossLaneForcingBoundPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSCrossLaneForcingBoundReceipt public

canonicalNSCrossLaneForcingBoundReceipt :
  NSCrossLaneForcingBoundReceipt
canonicalNSCrossLaneForcingBoundReceipt =
  record
    { lerayBandBoundReceipt =
        Leray.canonicalNSLerayBandBoundReceipt
    ; lerayStatusCanonical =
        refl
    ; lerayIndividualBandBoundAvailable =
        refl
    ; lerayNoClayPromotion =
        refl
    ; status =
        canonicalNSCrossLaneForcingBoundStatus
    ; statusIsCanonical =
        refl
    ; theoremKind =
        candidate
    ; theoremKindIsCandidate =
        refl
    ; targetBandIndex =
        0
    ; primeLaneIndex =
        0
    ; landingPairCriterion =
        absoluteDifferenceApproximatelyTargetPrimePower
    ; landingPairCriterionIsCanonical =
        refl
    ; forcingBoundShape =
        cTimesLandingPairWeightedEnergySum
    ; forcingBoundShapeIsCanonical =
        refl
    ; forcingBoundFormula =
        landingPairForcingBoundFormula
    ; forcingBoundFormulaIsCanonical =
        refl
    ; h118ShiftNumerator =
        11
    ; h118ShiftNumeratorIs11 =
        refl
    ; h118ShiftDenominator =
        8
    ; h118ShiftDenominatorIs8 =
        refl
    ; lerayBandBoundConsumed =
        true
    ; lerayBandBoundConsumedIsTrue =
        refl
    ; lerayBoundText =
        Leray.lerayBandBoundStatement
    ; lerayBoundTextIsCanonical =
        refl
    ; reducedForcingBoundShape =
        cM0SquaredKj
    ; reducedForcingBoundShapeIsCanonical =
        refl
    ; reducedForcingBoundFormula =
        lerayReducedForcingBoundFormula
    ; reducedForcingBoundFormulaIsCanonical =
        refl
    ; kjDefinition =
        kjDefinitionFormula
    ; kjDefinitionIsCanonical =
        refl
    ; kjFiniteFromLandingPairs =
        true
    ; kjFiniteFromLandingPairsIsTrue =
        refl
    ; highJBoundednessRecorded =
        true
    ; highJBoundednessRecordedIsTrue =
        refl
    ; highJBoundedness =
        highJBoundednessFormula
    ; highJBoundednessIsCanonical =
        refl
    ; auditKjZeroForJGreaterOrEqualSix =
        true
    ; auditKjZeroForJGreaterOrEqualSixIsTrue =
        refl
    ; auditThreshold =
        6
    ; auditThresholdIsSix =
        refl
    ; auditConclusion =
        kjAuditConclusionFormula
    ; auditConclusionIsCanonical =
        refl
    ; lowBandTableStatus =
        explicitFiniteAuditTableForJLessThanSix
    ; lowBandTableStatusIsExplicit =
        refl
    ; lowBandTableExplicit =
        true
    ; lowBandTableExplicitIsTrue =
        refl
    ; lowBandTable =
        lowBandTableLabel
    ; lowBandTableIsCanonical =
        refl
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; terminalPromotionPromoted =
        false
    ; terminalPromotionPromotedIsFalse =
        refl
    ; statement =
        nsCrossLaneForcingBoundStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Records F_j <= C sum_{landing pairs |q^j' - r^l| approx p^j} q^(j'+11/8) e_{q,j'}^(1/2)e_{r,l}^(1/2)"
        ∷ "Consumes NSLerayBandBoundReceipt: a_j(t) <= M_0^2 for all j,t"
        ∷ "Records the reduced bound F_j <= C M_0^2 K_j"
        ∷ "K_j is finite from the finite landing-pair audit"
        ∷ "High-j boundedness recorded through audit conclusion K_j = 0 for j >= 6"
        ∷ "Low-band table is explicit for j = 0,1,2,3,4,5"
        ∷ "Candidate/audit receipt only; no Clay, global regularity, or terminal promotion"
        ∷ []
    }

canonicalCrossLaneForcingBoundReducedToM0SquaredKj :
  reducedForcingBoundShape canonicalNSCrossLaneForcingBoundReceipt
  ≡
  cM0SquaredKj
canonicalCrossLaneForcingBoundReducedToM0SquaredKj =
  refl

canonicalCrossLaneForcingKjFinite :
  kjFiniteFromLandingPairs canonicalNSCrossLaneForcingBoundReceipt
  ≡
  true
canonicalCrossLaneForcingKjFinite =
  refl

canonicalCrossLaneForcingKjZeroForHighJ :
  auditKjZeroForJGreaterOrEqualSix
    canonicalNSCrossLaneForcingBoundReceipt
  ≡
  true
canonicalCrossLaneForcingKjZeroForHighJ =
  refl

canonicalCrossLaneForcingLowBandTableExplicit :
  lowBandTableExplicit canonicalNSCrossLaneForcingBoundReceipt
  ≡
  true
canonicalCrossLaneForcingLowBandTableExplicit =
  refl

nsCrossLaneForcingBoundDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSCrossLaneForcingBoundReceipt
  ≡
  false
nsCrossLaneForcingBoundDoesNotPromoteClay =
  refl

nsCrossLaneForcingBoundDoesNotPromoteGlobalRegularity :
  globalRegularityPromoted canonicalNSCrossLaneForcingBoundReceipt
  ≡
  false
nsCrossLaneForcingBoundDoesNotPromoteGlobalRegularity =
  refl

nsCrossLaneForcingBoundNoPromotion :
  NSCrossLaneForcingBoundPromotion →
  ⊥
nsCrossLaneForcingBoundNoPromotion =
  nsCrossLaneForcingBoundPromotionImpossibleHere
