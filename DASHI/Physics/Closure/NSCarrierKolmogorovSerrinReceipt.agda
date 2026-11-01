module DASHI.Physics.Closure.NSCarrierKolmogorovSerrinReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes carrier/Kolmogorov/Serrin boundary receipt.
--
-- This receipt records the corrected Paper 6 NS statement.  The carrier
-- H^{11/8} bound is meaningful for carrier-structured data, but the passage
-- to standard Serrin regularity needs a norm-comparison theorem.  Finite
-- active depth supplies such a comparison.  Infinite active depth does not
-- imply blow-up; it only closes this specific carrier route to Serrin.

data CarrierKolmogorovStatus : Set where
  correctedBoundaryRecorded :
    CarrierKolmogorovStatus

data CarrierKolmogorovComponent : Set where
  dyadicBandKolmogorovEnergy :
    CarrierKolmogorovComponent

  alphaKGeometricCarrierDecay :
    CarrierKolmogorovComponent

  standardH118Divergence :
    CarrierKolmogorovComponent

  finiteDepthSerrinTransfer :
    CarrierKolmogorovComponent

  unboundedDepthRouteClosedNotBlowup :
    CarrierKolmogorovComponent

canonicalCarrierKolmogorovComponents :
  List CarrierKolmogorovComponent
canonicalCarrierKolmogorovComponents =
  dyadicBandKolmogorovEnergy
  ∷ alphaKGeometricCarrierDecay
  ∷ standardH118Divergence
  ∷ finiteDepthSerrinTransfer
  ∷ unboundedDepthRouteClosedNotBlowup
  ∷ []

data OpenNSDepthProblem : Set where
  depthControlForCarrierEvolution :
    OpenNSDepthProblem

  nontrivialDepthClosedSolutionClass :
    OpenNSDepthProblem

  carrierToStandardNormComparison :
    OpenNSDepthProblem

canonicalOpenNSDepthProblems :
  List OpenNSDepthProblem
canonicalOpenNSDepthProblems =
  depthControlForCarrierEvolution
  ∷ nontrivialDepthClosedSolutionClass
  ∷ carrierToStandardNormComparison
  ∷ []

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

alphaK :
  Float
alphaK =
  0.6299605249474366

dyadicKolmogorovStatement :
  String
dyadicKolmogorovStatement =
  "For E(K) ~ K^{-5/3}, integration over the dyadic band [2^k,2^{k+1}] gives ||u_k||^2 ~ 2^{-2k/3}; hence the natural carrier decay parameter is alpha_K = 2^{-2/3}."

h118DivergenceStatement :
  String
h118DivergenceStatement =
  "The standard H^{11/8} square norm weights the same band by 2^{11k/4}, so a Kolmogorov band gives 2^{11k/4}*2^{-2k/3}=2^{25k/12}; the series diverges.  The corrected exponent is 25/12, not 41/12."

finiteDepthTransferStatement :
  String
finiteDepthTransferStatement =
  "Finite active depth K supplies a norm comparison from carrier H^{11/8} to standard H^{11/8}; standard Sobolev embedding gives L^24 and the Serrin value 3/24=0.125 is strictly below the critical line."

unboundedDepthBoundaryStatement :
  String
unboundedDepthBoundaryStatement =
  "Unbounded active depth means the carrier route to standard H^{11/8} can fail; it does not imply blow-up and it does not promote a Clay Navier-Stokes theorem."

paper6OneSentenceStatement :
  String
paper6OneSentenceStatement =
  "The carrier localises the Clay difficulty to control of the high-depth cascade: finite active depth gives standard Serrin regularity; unbounded depth is where the norm comparison can fail."

record NSCarrierKolmogorovSerrinReceipt : Setω where
  field
    status :
      CarrierKolmogorovStatus

    statusIsCorrectedBoundaryRecorded :
      status ≡ correctedBoundaryRecorded

    components :
      List CarrierKolmogorovComponent

    componentsAreCanonical :
      components ≡ canonicalCarrierKolmogorovComponents

    kolmogorovExponentNumerator :
      Nat

    kolmogorovExponentNumeratorIsFive :
      kolmogorovExponentNumerator ≡ 5

    kolmogorovExponentDenominator :
      Nat

    kolmogorovExponentDenominatorIsThree :
      kolmogorovExponentDenominator ≡ 3

    dyadicBandEnergyExponentNumerator :
      Nat

    dyadicBandEnergyExponentNumeratorIsTwo :
      dyadicBandEnergyExponentNumerator ≡ 2

    dyadicBandEnergyExponentDenominator :
      Nat

    dyadicBandEnergyExponentDenominatorIsThree :
      dyadicBandEnergyExponentDenominator ≡ 3

    alphaKolmogorov :
      Float

    alphaKolmogorovIsTwoToMinusTwoThirdsApprox :
      alphaKolmogorov ≡ alphaK

    h118Numerator :
      Nat

    h118NumeratorIsEleven :
      h118Numerator ≡ 11

    h118Denominator :
      Nat

    h118DenominatorIsEight :
      h118Denominator ≡ 8

    correctedDivergenceExponentNumerator :
      Nat

    correctedDivergenceExponentNumeratorIsTwentyFive :
      correctedDivergenceExponentNumerator ≡ 25

    correctedDivergenceExponentDenominator :
      Nat

    correctedDivergenceExponentDenominatorIsTwelve :
      correctedDivergenceExponentDenominator ≡ 12

    staleFortyOneOverTwelveRejected :
      Bool

    staleFortyOneOverTwelveRejectedIsTrue :
      staleFortyOneOverTwelveRejected ≡ true

    finiteActiveDepthSufficesForSerrin :
      Bool

    finiteActiveDepthSufficesForSerrinIsTrue :
      finiteActiveDepthSufficesForSerrin ≡ true

    serrinLqNumerator :
      Nat

    serrinLqNumeratorIsTwentyFour :
      serrinLqNumerator ≡ 24

    serrinValueNumerator :
      Nat

    serrinValueNumeratorIsOne :
      serrinValueNumerator ≡ 1

    serrinValueDenominator :
      Nat

    serrinValueDenominatorIsEight :
      serrinValueDenominator ≡ 8

    serrinStrictlyBelowCriticalLine :
      Bool

    serrinStrictlyBelowCriticalLineIsTrue :
      serrinStrictlyBelowCriticalLine ≡ true

    unboundedDepthImpliesBlowup :
      Bool

    unboundedDepthImpliesBlowupIsFalse :
      unboundedDepthImpliesBlowup ≡ false

    unboundedDepthOnlyBlocksThisRoute :
      Bool

    unboundedDepthOnlyBlocksThisRouteIsTrue :
      unboundedDepthOnlyBlocksThisRoute ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    openProblems :
      List OpenNSDepthProblem

    openProblemsAreCanonical :
      openProblems ≡ canonicalOpenNSDepthProblems

    dyadicKolmogorovSummary :
      String

    dyadicKolmogorovSummaryIsCanonical :
      dyadicKolmogorovSummary ≡ dyadicKolmogorovStatement

    h118DivergenceSummary :
      String

    h118DivergenceSummaryIsCanonical :
      h118DivergenceSummary ≡ h118DivergenceStatement

    finiteDepthTransferSummary :
      String

    finiteDepthTransferSummaryIsCanonical :
      finiteDepthTransferSummary ≡ finiteDepthTransferStatement

    unboundedDepthBoundarySummary :
      String

    unboundedDepthBoundarySummaryIsCanonical :
      unboundedDepthBoundarySummary ≡ unboundedDepthBoundaryStatement

    paper6Summary :
      String

    paper6SummaryIsCanonical :
      paper6Summary ≡ paper6OneSentenceStatement

    promotionFlags :
      List PromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSCarrierKolmogorovSerrinReceipt public

canonicalNSCarrierKolmogorovSerrinReceipt :
  NSCarrierKolmogorovSerrinReceipt
canonicalNSCarrierKolmogorovSerrinReceipt =
  record
    { status =
        correctedBoundaryRecorded
    ; statusIsCorrectedBoundaryRecorded =
        refl
    ; components =
        canonicalCarrierKolmogorovComponents
    ; componentsAreCanonical =
        refl
    ; kolmogorovExponentNumerator =
        5
    ; kolmogorovExponentNumeratorIsFive =
        refl
    ; kolmogorovExponentDenominator =
        3
    ; kolmogorovExponentDenominatorIsThree =
        refl
    ; dyadicBandEnergyExponentNumerator =
        2
    ; dyadicBandEnergyExponentNumeratorIsTwo =
        refl
    ; dyadicBandEnergyExponentDenominator =
        3
    ; dyadicBandEnergyExponentDenominatorIsThree =
        refl
    ; alphaKolmogorov =
        alphaK
    ; alphaKolmogorovIsTwoToMinusTwoThirdsApprox =
        refl
    ; h118Numerator =
        11
    ; h118NumeratorIsEleven =
        refl
    ; h118Denominator =
        8
    ; h118DenominatorIsEight =
        refl
    ; correctedDivergenceExponentNumerator =
        25
    ; correctedDivergenceExponentNumeratorIsTwentyFive =
        refl
    ; correctedDivergenceExponentDenominator =
        12
    ; correctedDivergenceExponentDenominatorIsTwelve =
        refl
    ; staleFortyOneOverTwelveRejected =
        true
    ; staleFortyOneOverTwelveRejectedIsTrue =
        refl
    ; finiteActiveDepthSufficesForSerrin =
        true
    ; finiteActiveDepthSufficesForSerrinIsTrue =
        refl
    ; serrinLqNumerator =
        24
    ; serrinLqNumeratorIsTwentyFour =
        refl
    ; serrinValueNumerator =
        1
    ; serrinValueNumeratorIsOne =
        refl
    ; serrinValueDenominator =
        8
    ; serrinValueDenominatorIsEight =
        refl
    ; serrinStrictlyBelowCriticalLine =
        true
    ; serrinStrictlyBelowCriticalLineIsTrue =
        refl
    ; unboundedDepthImpliesBlowup =
        false
    ; unboundedDepthImpliesBlowupIsFalse =
        refl
    ; unboundedDepthOnlyBlocksThisRoute =
        true
    ; unboundedDepthOnlyBlocksThisRouteIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; openProblems =
        canonicalOpenNSDepthProblems
    ; openProblemsAreCanonical =
        refl
    ; dyadicKolmogorovSummary =
        dyadicKolmogorovStatement
    ; dyadicKolmogorovSummaryIsCanonical =
        refl
    ; h118DivergenceSummary =
        h118DivergenceStatement
    ; h118DivergenceSummaryIsCanonical =
        refl
    ; finiteDepthTransferSummary =
        finiteDepthTransferStatement
    ; finiteDepthTransferSummaryIsCanonical =
        refl
    ; unboundedDepthBoundarySummary =
        unboundedDepthBoundaryStatement
    ; unboundedDepthBoundarySummaryIsCanonical =
        refl
    ; paper6Summary =
        paper6OneSentenceStatement
    ; paper6SummaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Kolmogorov dyadic band energy exponent is -2/3"
        ∷ "Carrier alpha_K is 2^{-2/3}"
        ∷ "Corrected H^{11/8} divergence exponent is 25/12"
        ∷ "Finite depth gives Serrin regularity by standard H^{11/8} control"
        ∷ "Unbounded depth blocks this carrier route only; it is not a blow-up theorem"
        ∷ []
    }

nsCarrierKolmogorovRejectsFortyOneOverTwelve :
  staleFortyOneOverTwelveRejected canonicalNSCarrierKolmogorovSerrinReceipt ≡ true
nsCarrierKolmogorovRejectsFortyOneOverTwelve =
  refl

nsCarrierKolmogorovNoBlowupClaim :
  unboundedDepthImpliesBlowup canonicalNSCarrierKolmogorovSerrinReceipt ≡ false
nsCarrierKolmogorovNoBlowupClaim =
  refl

nsCarrierKolmogorovNoClayPromotion :
  clayNavierStokesPromoted canonicalNSCarrierKolmogorovSerrinReceipt ≡ false
nsCarrierKolmogorovNoClayPromotion =
  refl
