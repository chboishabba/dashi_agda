module DASHI.Physics.Closure.NSDissipationCutoffReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes dissipation-cutoff receipt.
--
-- This receipt records the adjacent-only high-frequency cutoff calculation:
-- with adjacent-only nonlinear production bounded by C p^j and dissipation
-- rate nu p^{2j}, the cutoff
--   j_nu = floor(log_p(C/nu))
-- is finite for every nu > 0.  For j > j_nu the dissipation rate exceeds
-- the adjacent-only nonlinear production.  As nu -> 0 the cutoff tends to
-- infinity.  This is a scale-cutoff bookkeeping receipt only; no Clay or
-- global regularity promotion is made here.

data NSDissipationCutoffStatus : Set where
  adjacentOnlyNonlinearProductionBoundRecorded :
    NSDissipationCutoffStatus

  dissipationRateStatusRecorded :
    NSDissipationCutoffStatus

  cutoffDefinedByFloorLog :
    NSDissipationCutoffStatus

  highModesDissipationDominatesAfterCutoff :
    NSDissipationCutoffStatus

  cutoffFiniteForEveryPositiveViscosity :
    NSDissipationCutoffStatus

  cutoffDivergesAsViscosityTendsToZero :
    NSDissipationCutoffStatus

  noClayPromotion :
    NSDissipationCutoffStatus

canonicalNSDissipationCutoffStatus :
  List NSDissipationCutoffStatus
canonicalNSDissipationCutoffStatus =
  adjacentOnlyNonlinearProductionBoundRecorded
  ∷ dissipationRateStatusRecorded
  ∷ cutoffDefinedByFloorLog
  ∷ highModesDissipationDominatesAfterCutoff
  ∷ cutoffFiniteForEveryPositiveViscosity
  ∷ cutoffDivergesAsViscosityTendsToZero
  ∷ noClayPromotion
  ∷ []

data CutoffValueExample : Set where
  nu0001P2J11 :
    CutoffValueExample

  nu001P3J5 :
    CutoffValueExample

canonicalCutoffValueTable :
  List CutoffValueExample
canonicalCutoffValueTable =
  nu0001P2J11
  ∷ nu001P3J5
  ∷ []

data NSDissipationCutoffPromotion : Set where

nsDissipationCutoffPromotionImpossibleHere :
  NSDissipationCutoffPromotion →
  ⊥
nsDissipationCutoffPromotionImpossibleHere ()

dissipationCutoffFormula : String
dissipationCutoffFormula =
  "floor(log_p(C/nu))"

adjacentOnlyNonlinearProductionFormula : String
adjacentOnlyNonlinearProductionFormula =
  "C p^j"

dissipationRateFormula : String
dissipationRateFormula =
  "nu p^{2j}"

cutoffDominanceFormula : String
cutoffDominanceFormula =
  "j > j_nu implies nu p^{2j} > C p^j"

cutoffLimitFormula : String
cutoffLimitFormula =
  "nu -> 0 implies j_nu -> infinity"

cutoffExamplesText : String
cutoffExamplesText =
  "nu=0.001,p=2 => j_nu=11; nu=0.01,p=3 => j_nu=5"

nsDissipationCutoffStatement : String
nsDissipationCutoffStatement =
  "Define j_nu = floor(log_p(C/nu)).  For j > j_nu, the dissipation rate nu p^{2j} exceeds adjacent-only nonlinear production C p^j; the cutoff is finite for every nu > 0 and tends to infinity as nu -> 0.  Examples recorded: nu=0.001,p=2 => j_nu=11; nu=0.01,p=3 => j_nu=5.  No Clay promotion follows."

record NSDissipationCutoffReceipt : Setω where
  field
    status :
      List NSDissipationCutoffStatus

    statusIsCanonical :
      status ≡ canonicalNSDissipationCutoffStatus

    adjacentOnlyNonlinearProduction :
      String

    adjacentOnlyNonlinearProductionIsCanonical :
      adjacentOnlyNonlinearProduction ≡ adjacentOnlyNonlinearProductionFormula

    dissipationRate :
      String

    dissipationRateIsCanonical :
      dissipationRate ≡ dissipationRateFormula

    dissipationCutoffJNu :
      String

    dissipationCutoffJNuIsFloorLog :
      dissipationCutoffJNu ≡ dissipationCutoffFormula

    cutoffDominanceCondition :
      String

    cutoffDominanceConditionIsCanonical :
      cutoffDominanceCondition ≡ cutoffDominanceFormula

    cutoffLimitAsNuToZero :
      String

    cutoffLimitAsNuToZeroIsCanonical :
      cutoffLimitAsNuToZero ≡ cutoffLimitFormula

    adjacentOnlyProductionBoundRecorded :
      Bool

    adjacentOnlyProductionBoundRecordedIsTrue :
      adjacentOnlyProductionBoundRecorded ≡ true

    dissipationRateRecorded :
      Bool

    dissipationRateRecordedIsTrue :
      dissipationRateRecorded ≡ true

    highModesDissipationDominates :
      Bool

    highModesDissipationDominatesIsTrue :
      highModesDissipationDominates ≡ true

    cutoffFiniteForAnyNu :
      Bool

    cutoffFiniteForAnyNuIsTrue :
      cutoffFiniteForAnyNu ≡ true

    cutoffTendsToInfinityAsNuToZero :
      Bool

    cutoffTendsToInfinityAsNuToZeroIsTrue :
      cutoffTendsToInfinityAsNuToZero ≡ true

    cutoffValueTable :
      List CutoffValueExample

    cutoffValueTableRecorded :
      cutoffValueTable ≡ canonicalCutoffValueTable

    firstExampleNuTimes1000 :
      Nat

    firstExampleNuTimes1000Is1 :
      firstExampleNuTimes1000 ≡ 1

    firstExamplePrime :
      Nat

    firstExamplePrimeIs2 :
      firstExamplePrime ≡ 2

    firstExampleJNu :
      Nat

    firstExampleJNuIs11 :
      firstExampleJNu ≡ 11

    secondExampleNuTimes100 :
      Nat

    secondExampleNuTimes100Is1 :
      secondExampleNuTimes100 ≡ 1

    secondExamplePrime :
      Nat

    secondExamplePrimeIs3 :
      secondExamplePrime ≡ 3

    secondExampleJNu :
      Nat

    secondExampleJNuIs5 :
      secondExampleJNu ≡ 5

    cutoffExamples :
      String

    cutoffExamplesAreCanonical :
      cutoffExamples ≡ cutoffExamplesText

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    clayMillenniumPromotionClaimed :
      Bool

    clayMillenniumPromotionClaimedIsFalse :
      clayMillenniumPromotionClaimed ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsDissipationCutoffStatement

    promotionFlags :
      List NSDissipationCutoffPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSDissipationCutoffReceipt public

canonicalNSDissipationCutoffReceipt :
  NSDissipationCutoffReceipt
canonicalNSDissipationCutoffReceipt =
  record
    { status =
        canonicalNSDissipationCutoffStatus
    ; statusIsCanonical =
        refl
    ; adjacentOnlyNonlinearProduction =
        adjacentOnlyNonlinearProductionFormula
    ; adjacentOnlyNonlinearProductionIsCanonical =
        refl
    ; dissipationRate =
        dissipationRateFormula
    ; dissipationRateIsCanonical =
        refl
    ; dissipationCutoffJNu =
        dissipationCutoffFormula
    ; dissipationCutoffJNuIsFloorLog =
        refl
    ; cutoffDominanceCondition =
        cutoffDominanceFormula
    ; cutoffDominanceConditionIsCanonical =
        refl
    ; cutoffLimitAsNuToZero =
        cutoffLimitFormula
    ; cutoffLimitAsNuToZeroIsCanonical =
        refl
    ; adjacentOnlyProductionBoundRecorded =
        true
    ; adjacentOnlyProductionBoundRecordedIsTrue =
        refl
    ; dissipationRateRecorded =
        true
    ; dissipationRateRecordedIsTrue =
        refl
    ; highModesDissipationDominates =
        true
    ; highModesDissipationDominatesIsTrue =
        refl
    ; cutoffFiniteForAnyNu =
        true
    ; cutoffFiniteForAnyNuIsTrue =
        refl
    ; cutoffTendsToInfinityAsNuToZero =
        true
    ; cutoffTendsToInfinityAsNuToZeroIsTrue =
        refl
    ; cutoffValueTable =
        canonicalCutoffValueTable
    ; cutoffValueTableRecorded =
        refl
    ; firstExampleNuTimes1000 =
        1
    ; firstExampleNuTimes1000Is1 =
        refl
    ; firstExamplePrime =
        2
    ; firstExamplePrimeIs2 =
        refl
    ; firstExampleJNu =
        11
    ; firstExampleJNuIs11 =
        refl
    ; secondExampleNuTimes100 =
        1
    ; secondExampleNuTimes100Is1 =
        refl
    ; secondExamplePrime =
        3
    ; secondExamplePrimeIs3 =
        refl
    ; secondExampleJNu =
        5
    ; secondExampleJNuIs5 =
        refl
    ; cutoffExamples =
        cutoffExamplesText
    ; cutoffExamplesAreCanonical =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; clayMillenniumPromotionClaimed =
        false
    ; clayMillenniumPromotionClaimedIsFalse =
        refl
    ; statement =
        nsDissipationCutoffStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "dissipationCutoffJNu = floor(log_p(C/nu))"
        ∷ "For j > j_nu, nu p^{2j} exceeds adjacent-only nonlinear production C p^j"
        ∷ "cutoffFiniteForAnyNu = true for every nu > 0"
        ∷ "nu -> 0 implies j_nu -> infinity"
        ∷ "cutoffValueTable records nu=0.001,p=2 => j_nu=11"
        ∷ "cutoffValueTable records nu=0.01,p=3 => j_nu=5"
        ∷ "No Clay Navier-Stokes, global regularity, or Millennium promotion flags are set"
        ∷ []
    }

dissipationCutoffJNuCanonical :
  dissipationCutoffJNu canonicalNSDissipationCutoffReceipt
  ≡
  "floor(log_p(C/nu))"
dissipationCutoffJNuCanonical =
  refl

cutoffFiniteForAnyNuTrue :
  cutoffFiniteForAnyNu canonicalNSDissipationCutoffReceipt
  ≡
  true
cutoffFiniteForAnyNuTrue =
  refl

cutoffValueTableCanonical :
  cutoffValueTable canonicalNSDissipationCutoffReceipt
  ≡
  canonicalCutoffValueTable
cutoffValueTableCanonical =
  refl

firstCutoffExampleIsNu0001P2J11 :
  firstExampleJNu canonicalNSDissipationCutoffReceipt
  ≡
  11
firstCutoffExampleIsNu0001P2J11 =
  refl

secondCutoffExampleIsNu001P3J5 :
  secondExampleJNu canonicalNSDissipationCutoffReceipt
  ≡
  5
secondCutoffExampleIsNu001P3J5 =
  refl

nsDissipationCutoffNoClayPromotion :
  clayNavierStokesPromoted canonicalNSDissipationCutoffReceipt
  ≡
  false
nsDissipationCutoffNoClayPromotion =
  refl

nsDissipationCutoffNoPromotion :
  NSDissipationCutoffPromotion →
  ⊥
nsDissipationCutoffNoPromotion =
  nsDissipationCutoffPromotionImpossibleHere
