module DASHI.Physics.Closure.NSWeakSolutionSummaryReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSCarrierContinuumLimitReceipt as Limit
import DASHI.Physics.Closure.NSW4WeakSolutionReceipt as W4
import DASHI.Physics.Closure.NSWeakSolutionFinalReceipt as Weak

data NSWeakSolutionSummaryStatus : Set where
  conditionalLerayBranchSummarisedRegularityNotPromoted :
    NSWeakSolutionSummaryStatus

data NSWeakSolutionSummaryEntry : Set where
  carrierContinuumLimitRoute :
    NSWeakSolutionSummaryEntry
  nonlinearPassageRoute :
    NSWeakSolutionSummaryEntry
  w4LerayWeakSolutionRoute :
    NSWeakSolutionSummaryEntry
  noSmoothRegularityUpgrade :
    NSWeakSolutionSummaryEntry

canonicalNSWeakSolutionSummaryEntries :
  List NSWeakSolutionSummaryEntry
canonicalNSWeakSolutionSummaryEntries =
  carrierContinuumLimitRoute
  ∷ nonlinearPassageRoute
  ∷ w4LerayWeakSolutionRoute
  ∷ noSmoothRegularityUpgrade
  ∷ []

nsWeakSolutionSummaryStatement : String
nsWeakSolutionSummaryStatement =
  "The NS weak-solution summary records a true Leray weak-solution branch and keeps unconditional weak solution, smooth regularity, vorticity-control closure, and Clay promotion false."

record NSWeakSolutionSummaryReceipt : Setω where
  field
    status :
      NSWeakSolutionSummaryStatus

    continuumLimitReceipt :
      Limit.NSCarrierContinuumLimitReceipt

    nonlinearPassageConditionalTrue :
      Limit.nsNonlinearTermConvergesConditional
        continuumLimitReceipt
      ≡
      true

    continuumWeakSolutionUnconditionalFalse :
      Limit.nsWeakSolutionLimitInhabitedUnconditionally
        continuumLimitReceipt
      ≡
      false

    weakSolutionReceipt :
      Weak.NSWeakSolutionFinalReceipt

    weakSolutionConditionalTrue :
      Weak.nsLerayWeakSolutionConditional weakSolutionReceipt ≡ true

    weakSolutionUnconditionalFalse :
      Weak.nsWeakSolutionUnconditional weakSolutionReceipt ≡ false

    w4Receipt :
      W4.NSW4WeakSolutionReceipt

    w4LerayBranchTrue :
      W4.lerayWeakSolutionBranchAvailable w4Receipt ≡ true

    entries :
      List NSWeakSolutionSummaryEntry

    entriesAreCanonical :
      entries ≡ canonicalNSWeakSolutionSummaryEntries

    w1EnergyInequalityInhabited :
      Bool

    w1EnergyInequalityInhabitedIsTrue :
      w1EnergyInequalityInhabited ≡ true

    w2CompactnessInhabited :
      Bool

    w2CompactnessInhabitedIsTrue :
      w2CompactnessInhabited ≡ true

    w3NonlinearPassageInhabited :
      Bool

    w3NonlinearPassageInhabitedIsTrue :
      w3NonlinearPassageInhabited ≡ true

    w4WeakFormulationInhabited :
      Bool

    w4WeakFormulationInhabitedIsTrue :
      w4WeakFormulationInhabited ≡ true

    w5LerayChainInhabited :
      Bool

    w5LerayChainInhabitedIsTrue :
      w5LerayChainInhabited ≡ true

    lerayWeakSolutionBranchAvailable :
      Bool

    lerayWeakSolutionBranchAvailableIsTrue :
      lerayWeakSolutionBranchAvailable ≡ true

    globalSmoothRegularityProved :
      Bool

    globalSmoothRegularityProvedIsFalse :
      globalSmoothRegularityProved ≡ false

    vorticityControlClosed :
      Bool

    vorticityControlClosedIsFalse :
      vorticityControlClosed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsWeakSolutionSummaryStatement

    receiptBoundary :
      List String

open NSWeakSolutionSummaryReceipt public

canonicalNSWeakSolutionSummaryReceipt :
  NSWeakSolutionSummaryReceipt
canonicalNSWeakSolutionSummaryReceipt =
  record
    { status =
        conditionalLerayBranchSummarisedRegularityNotPromoted
    ; continuumLimitReceipt =
        Limit.canonicalNSCarrierContinuumLimitReceipt
    ; nonlinearPassageConditionalTrue =
        refl
    ; continuumWeakSolutionUnconditionalFalse =
        refl
    ; weakSolutionReceipt =
        Weak.canonicalNSWeakSolutionFinalReceipt
    ; weakSolutionConditionalTrue =
        refl
    ; weakSolutionUnconditionalFalse =
        refl
    ; w4Receipt =
        W4.canonicalNSW4WeakSolutionReceipt
    ; w4LerayBranchTrue =
        refl
    ; entries =
        canonicalNSWeakSolutionSummaryEntries
    ; entriesAreCanonical =
        refl
    ; w1EnergyInequalityInhabited =
        true
    ; w1EnergyInequalityInhabitedIsTrue =
        refl
    ; w2CompactnessInhabited =
        true
    ; w2CompactnessInhabitedIsTrue =
        refl
    ; w3NonlinearPassageInhabited =
        true
    ; w3NonlinearPassageInhabitedIsTrue =
        refl
    ; w4WeakFormulationInhabited =
        true
    ; w4WeakFormulationInhabitedIsTrue =
        refl
    ; w5LerayChainInhabited =
        true
    ; w5LerayChainInhabitedIsTrue =
        refl
    ; lerayWeakSolutionBranchAvailable =
        true
    ; lerayWeakSolutionBranchAvailableIsTrue =
        refl
    ; globalSmoothRegularityProved =
        false
    ; globalSmoothRegularityProvedIsFalse =
        refl
    ; vorticityControlClosed =
        false
    ; vorticityControlClosedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        nsWeakSolutionSummaryStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "W1 energy, W2 compactness, W3 nonlinear passage, W4 weak formulation, and W5 Leray chain are inhabited at receipt scope"
        ∷ "This summary promotes only the Leray weak-solution branch"
        ∷ "Unconditional weak-solution inhabitation remains false in the underlying continuum-limit receipt"
        ∷ "No smooth global regularity or Clay-facing theorem is promoted"
        ∷ []
    }

nsWeakSolutionSummaryKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSWeakSolutionSummaryReceipt ≡ false
nsWeakSolutionSummaryKeepsClayFalse =
  refl
