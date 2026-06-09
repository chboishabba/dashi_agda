module DASHI.Physics.Closure.YMBruhatTitsPathCountingKPThresholdReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_+_; _*_)

------------------------------------------------------------------------
-- YM Bruhat-Tits path counting / KP threshold receipt.
--
-- This receipt records a concrete same-prime polymer counting surface on a
-- Bruhat-Tits p-lane tree.  The path-count tail is p^n after a fixed edge:
-- the p+1 valency supplies one incoming edge and p forward choices at each
-- next step.  The KP convergence threshold is therefore the tree branching
-- threshold log p, while strict local activity absorption records log(2p).
--
-- The receipt is carrier-side bookkeeping only: no continuum KP theorem,
-- no Balaban RG theorem, no Yang-Mills mass-gap theorem, and no Clay
-- promotion are made here.

_^_ :
  Nat →
  Nat →
  Nat
base ^ zero =
  suc zero
base ^ suc exponent =
  base * (base ^ exponent)

two :
  Nat
two =
  suc (suc zero)

seven :
  Nat
seven =
  7

eight :
  Nat
eight =
  8

fourteen :
  Nat
fourteen =
  14

bruhatTitsValency :
  Nat →
  Nat
bruhatTitsValency p =
  suc p

samePrimeForwardBranching :
  Nat →
  Nat
samePrimeForwardBranching p =
  p

samePrimePathCount :
  Nat →
  Nat →
  Nat
samePrimePathCount p length =
  samePrimeForwardBranching p ^ length

strictKPMarginLogBase :
  Nat →
  Nat
strictKPMarginLogBase p =
  two * p

data YMBTPathCountingKPStatus : Set where
  ymBruhatTitsSamePrimePathCountingKPThresholdRecorded :
    YMBTPathCountingKPStatus

data SamePrimePolymerClass : Set where
  fixedPrimeBruhatTitsPathPolymer :
    SamePrimePolymerClass

data PathCountingLaw : Set where
  countAfterFixedEdgeIsPToLength :
    PathCountingLaw

data KPThresholdLaw : Set where
  convergenceThresholdUsesLogP :
    KPThresholdLaw

  strictActivityAbsorptionUsesLogTwoP :
    KPThresholdLaw

canonicalKPThresholdLaws :
  List KPThresholdLaw
canonicalKPThresholdLaws =
  convergenceThresholdUsesLogP
  ∷ strictActivityAbsorptionUsesLogTwoP
  ∷ []

data P7ThresholdOrdering : Set where
  p7StrictMarginThresholdRecordedAboveConvergenceThreshold :
    P7ThresholdOrdering

data YMBTPathCountingNonClaim : Set where
  noCrossPrimePolymerCounting :
    YMBTPathCountingNonClaim

  noFlatLatticeKPThreshold :
    YMBTPathCountingNonClaim

  noContinuumKPTheorem :
    YMBTPathCountingNonClaim

  noBalabanRGTheorem :
    YMBTPathCountingNonClaim

  noYangMillsMassGapTheorem :
    YMBTPathCountingNonClaim

  noClayYangMillsPromotion :
    YMBTPathCountingNonClaim

canonicalYMBTPathCountingNonClaims :
  List YMBTPathCountingNonClaim
canonicalYMBTPathCountingNonClaims =
  noCrossPrimePolymerCounting
  ∷ noFlatLatticeKPThreshold
  ∷ noContinuumKPTheorem
  ∷ noBalabanRGTheorem
  ∷ noYangMillsMassGapTheorem
  ∷ noClayYangMillsPromotion
  ∷ []

data YMBTPathCountingPromotion : Set where

ymBTPathCountingPromotionImpossibleHere :
  YMBTPathCountingPromotion →
  ⊥
ymBTPathCountingPromotionImpossibleHere ()

p7Prime :
  Nat
p7Prime =
  seven

p7Valency :
  Nat
p7Valency =
  eight

p7Branching :
  Nat
p7Branching =
  seven

p7ConvergenceLogBase :
  Nat
p7ConvergenceLogBase =
  seven

p7StrictMarginLogBase :
  Nat
p7StrictMarginLogBase =
  fourteen

p7BetaMinNumerator :
  Nat
p7BetaMinNumerator =
  1013

p7BetaMinDenominator :
  Nat
p7BetaMinDenominator =
  100

p7StrictKPMarginBetaNumerator :
  Nat
p7StrictKPMarginBetaNumerator =
  1364

p7StrictKPMarginBetaDenominator :
  Nat
p7StrictKPMarginBetaDenominator =
  100

p7PathCountLength0 :
  samePrimePathCount p7Prime 0 ≡ 1
p7PathCountLength0 =
  refl

p7PathCountLength1 :
  samePrimePathCount p7Prime 1 ≡ 7
p7PathCountLength1 =
  refl

p7PathCountLength2 :
  samePrimePathCount p7Prime 2 ≡ 49
p7PathCountLength2 =
  refl

p7PathCountLength3 :
  samePrimePathCount p7Prime 3 ≡ 343
p7PathCountLength3 =
  refl

p7ValencyIsPPlusOne :
  p7Valency ≡ bruhatTitsValency p7Prime
p7ValencyIsPPlusOne =
  refl

p7StrictBaseIsTwoP :
  p7StrictMarginLogBase ≡ strictKPMarginLogBase p7Prime
p7StrictBaseIsTwoP =
  refl

p7ThresholdOrdering :
  P7ThresholdOrdering
p7ThresholdOrdering =
  p7StrictMarginThresholdRecordedAboveConvergenceThreshold

pathCountingStatement :
  String
pathCountingStatement =
  "For a same-prime Bruhat-Tits p-lane polymer tail through a fixed edge, length-n path count is p^n; for p=7 the counts begin 1, 7, 49, 343."

kpThresholdStatement :
  String
kpThresholdStatement =
  "The same-prime KP convergence threshold records beta*cMin(p)-a > log p; strict local activity absorption records beta*cMin(p)-a > log(2p)."

p7ThresholdStatement :
  String
p7ThresholdStatement =
  "For p=7: valency is 8, branching is 7, convergence log base is 7, strict KP margin log base is 14, betaMin is recorded as 1013/100, and strict margin beta as 1364/100."

nonPromotionStatement :
  String
nonPromotionStatement =
  "This is a YM carrier-side path-counting receipt only; it does not promote continuum KP, Balaban RG, Yang-Mills mass gap, or Clay."

record P7ThresholdFacts : Set where
  field
    prime :
      Nat

    primeIsSeven :
      prime ≡ p7Prime

    valency :
      Nat

    valencyIsEight :
      valency ≡ p7Valency

    valencyIsPrimePlusOne :
      valency ≡ bruhatTitsValency prime

    branching :
      Nat

    branchingIsSeven :
      branching ≡ p7Branching

    convergenceLogBase :
      Nat

    convergenceLogBaseIsSeven :
      convergenceLogBase ≡ p7ConvergenceLogBase

    strictMarginLogBase :
      Nat

    strictMarginLogBaseIsFourteen :
      strictMarginLogBase ≡ p7StrictMarginLogBase

    strictMarginLogBaseIsTwoP :
      strictMarginLogBase ≡ strictKPMarginLogBase prime

    betaMinNumerator :
      Nat

    betaMinNumeratorIs1013 :
      betaMinNumerator ≡ p7BetaMinNumerator

    betaMinDenominator :
      Nat

    betaMinDenominatorIs100 :
      betaMinDenominator ≡ p7BetaMinDenominator

    strictMarginBetaNumerator :
      Nat

    strictMarginBetaNumeratorIs1364 :
      strictMarginBetaNumerator ≡ p7StrictKPMarginBetaNumerator

    strictMarginBetaDenominator :
      Nat

    strictMarginBetaDenominatorIs100 :
      strictMarginBetaDenominator ≡ p7StrictKPMarginBetaDenominator

    thresholdOrdering :
      P7ThresholdOrdering

    thresholdOrderingIsStrictAboveConvergence :
      thresholdOrdering
      ≡
      p7StrictMarginThresholdRecordedAboveConvergenceThreshold

open P7ThresholdFacts public

canonicalP7ThresholdFacts :
  P7ThresholdFacts
canonicalP7ThresholdFacts =
  record
    { prime =
        p7Prime
    ; primeIsSeven =
        refl
    ; valency =
        p7Valency
    ; valencyIsEight =
        refl
    ; valencyIsPrimePlusOne =
        refl
    ; branching =
        p7Branching
    ; branchingIsSeven =
        refl
    ; convergenceLogBase =
        p7ConvergenceLogBase
    ; convergenceLogBaseIsSeven =
        refl
    ; strictMarginLogBase =
        p7StrictMarginLogBase
    ; strictMarginLogBaseIsFourteen =
        refl
    ; strictMarginLogBaseIsTwoP =
        refl
    ; betaMinNumerator =
        p7BetaMinNumerator
    ; betaMinNumeratorIs1013 =
        refl
    ; betaMinDenominator =
        p7BetaMinDenominator
    ; betaMinDenominatorIs100 =
        refl
    ; strictMarginBetaNumerator =
        p7StrictKPMarginBetaNumerator
    ; strictMarginBetaNumeratorIs1364 =
        refl
    ; strictMarginBetaDenominator =
        p7StrictKPMarginBetaDenominator
    ; strictMarginBetaDenominatorIs100 =
        refl
    ; thresholdOrdering =
        p7ThresholdOrdering
    ; thresholdOrderingIsStrictAboveConvergence =
        refl
    }

record YMBruhatTitsPathCountingKPThresholdReceipt : Set where
  field
    status :
      YMBTPathCountingKPStatus

    statusIsCanonical :
      status
      ≡
      ymBruhatTitsSamePrimePathCountingKPThresholdRecorded

    polymerClass :
      SamePrimePolymerClass

    polymerClassIsSamePrimePath :
      polymerClass ≡ fixedPrimeBruhatTitsPathPolymer

    pathCountingLaw :
      PathCountingLaw

    pathCountingLawIsPToLength :
      pathCountingLaw ≡ countAfterFixedEdgeIsPToLength

    pathCountFunction :
      Nat → Nat → Nat

    pathCountFunctionIsCanonical :
      pathCountFunction ≡ samePrimePathCount

    p7ThresholdFacts :
      P7ThresholdFacts

    p7ThresholdFactsAreCanonical :
      p7ThresholdFacts ≡ canonicalP7ThresholdFacts

    p7Length0Count :
      pathCountFunction p7Prime 0 ≡ 1

    p7Length1Count :
      pathCountFunction p7Prime 1 ≡ 7

    p7Length2Count :
      pathCountFunction p7Prime 2 ≡ 49

    p7Length3Count :
      pathCountFunction p7Prime 3 ≡ 343

    thresholdLaws :
      List KPThresholdLaw

    thresholdLawsAreCanonical :
      thresholdLaws ≡ canonicalKPThresholdLaws

    samePrimeOnly :
      Bool

    samePrimeOnlyIsTrue :
      samePrimeOnly ≡ true

    crossPrimeCountingPromoted :
      Bool

    crossPrimeCountingPromotedIsFalse :
      crossPrimeCountingPromoted ≡ false

    continuumKPTheoremPromoted :
      Bool

    continuumKPTheoremPromotedIsFalse :
      continuumKPTheoremPromoted ≡ false

    balabanRGTheoremPromoted :
      Bool

    balabanRGTheoremPromotedIsFalse :
      balabanRGTheoremPromoted ≡ false

    yangMillsMassGapPromoted :
      Bool

    yangMillsMassGapPromotedIsFalse :
      yangMillsMassGapPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    nonClaims :
      List YMBTPathCountingNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMBTPathCountingNonClaims

    promotionFlags :
      List YMBTPathCountingPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    pathCountingReading :
      String

    pathCountingReadingIsCanonical :
      pathCountingReading ≡ pathCountingStatement

    kpThresholdReading :
      String

    kpThresholdReadingIsCanonical :
      kpThresholdReading ≡ kpThresholdStatement

    p7ThresholdReading :
      String

    p7ThresholdReadingIsCanonical :
      p7ThresholdReading ≡ p7ThresholdStatement

    nonPromotionReading :
      String

    nonPromotionReadingIsCanonical :
      nonPromotionReading ≡ nonPromotionStatement

open YMBruhatTitsPathCountingKPThresholdReceipt public

canonicalYMBruhatTitsPathCountingKPThresholdReceipt :
  YMBruhatTitsPathCountingKPThresholdReceipt
canonicalYMBruhatTitsPathCountingKPThresholdReceipt =
  record
    { status =
        ymBruhatTitsSamePrimePathCountingKPThresholdRecorded
    ; statusIsCanonical =
        refl
    ; polymerClass =
        fixedPrimeBruhatTitsPathPolymer
    ; polymerClassIsSamePrimePath =
        refl
    ; pathCountingLaw =
        countAfterFixedEdgeIsPToLength
    ; pathCountingLawIsPToLength =
        refl
    ; pathCountFunction =
        samePrimePathCount
    ; pathCountFunctionIsCanonical =
        refl
    ; p7ThresholdFacts =
        canonicalP7ThresholdFacts
    ; p7ThresholdFactsAreCanonical =
        refl
    ; p7Length0Count =
        refl
    ; p7Length1Count =
        refl
    ; p7Length2Count =
        refl
    ; p7Length3Count =
        refl
    ; thresholdLaws =
        canonicalKPThresholdLaws
    ; thresholdLawsAreCanonical =
        refl
    ; samePrimeOnly =
        true
    ; samePrimeOnlyIsTrue =
        refl
    ; crossPrimeCountingPromoted =
        false
    ; crossPrimeCountingPromotedIsFalse =
        refl
    ; continuumKPTheoremPromoted =
        false
    ; continuumKPTheoremPromotedIsFalse =
        refl
    ; balabanRGTheoremPromoted =
        false
    ; balabanRGTheoremPromotedIsFalse =
        refl
    ; yangMillsMassGapPromoted =
        false
    ; yangMillsMassGapPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; nonClaims =
        canonicalYMBTPathCountingNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; pathCountingReading =
        pathCountingStatement
    ; pathCountingReadingIsCanonical =
        refl
    ; kpThresholdReading =
        kpThresholdStatement
    ; kpThresholdReadingIsCanonical =
        refl
    ; p7ThresholdReading =
        p7ThresholdStatement
    ; p7ThresholdReadingIsCanonical =
        refl
    ; nonPromotionReading =
        nonPromotionStatement
    ; nonPromotionReadingIsCanonical =
        refl
    }

canonicalReceiptRecordsSamePrimeOnly :
  samePrimeOnly canonicalYMBruhatTitsPathCountingKPThresholdReceipt
  ≡
  true
canonicalReceiptRecordsSamePrimeOnly =
  refl

canonicalReceiptNoClayPromotion :
  clayYangMillsPromoted canonicalYMBruhatTitsPathCountingKPThresholdReceipt
  ≡
  false
canonicalReceiptNoClayPromotion =
  refl
