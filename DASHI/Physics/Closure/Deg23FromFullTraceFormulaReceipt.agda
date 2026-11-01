module DASHI.Physics.Closure.Deg23FromFullTraceFormulaReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Deg23SummaryAndFutureDirectionReceipt as Summary

data TraceFormulaContribution : Set where
  identityContributionOnePlusThirteen :
    TraceFormulaContribution

  ellipticFixedPointContribution :
    TraceFormulaContribution

  parabolicContribution :
    TraceFormulaContribution

  hyperbolicContribution :
    TraceFormulaContribution

canonicalTraceFormulaContributions : List TraceFormulaContribution
canonicalTraceFormulaContributions =
  identityContributionOnePlusThirteen
  ∷ ellipticFixedPointContribution
  ∷ parabolicContribution
  ∷ hyperbolicContribution
  ∷ []

fullTraceFormulaStatement : String
fullTraceFormulaStatement =
  "The full Eichler-Selberg trace formula may contain nonlocal CM contributions; the selected joint CM point contributes zero and does not close deg23."

record Deg23FromFullTraceFormulaReceipt : Setω where
  field
    summaryReceipt :
      Summary.Deg23SummaryAndFutureDirectionReceipt

    selectedCMResidualStillOpen :
      Summary.deg23ResidualExplained summaryReceipt ≡ false

    contributions :
      List TraceFormulaContribution

    contributionsAreCanonical :
      contributions ≡ canonicalTraceFormulaContributions

    traceFormulaEllipticContributionSumOverAllCMPoints :
      Bool

    traceFormulaEllipticContributionSumOverAllCMPointsIsTrue :
      traceFormulaEllipticContributionSumOverAllCMPoints ≡ true

    selectedCMPointContributesZero :
      Bool

    selectedCMPointContributesZeroIsTrue :
      selectedCMPointContributesZero ≡ true

    otherCMPointsMayContribute :
      Bool

    otherCMPointsMayContributeIsTrue :
      otherCMPointsMayContribute ≡ true

    deg23ResidualExplained :
      Bool

    deg23ResidualExplainedIsFalse :
      deg23ResidualExplained ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ fullTraceFormulaStatement

open Deg23FromFullTraceFormulaReceipt public

canonicalDeg23FromFullTraceFormulaReceipt :
  Deg23FromFullTraceFormulaReceipt
canonicalDeg23FromFullTraceFormulaReceipt =
  record
    { summaryReceipt =
        Summary.canonicalDeg23SummaryAndFutureDirectionReceipt
    ; selectedCMResidualStillOpen =
        refl
    ; contributions =
        canonicalTraceFormulaContributions
    ; contributionsAreCanonical =
        refl
    ; traceFormulaEllipticContributionSumOverAllCMPoints =
        true
    ; traceFormulaEllipticContributionSumOverAllCMPointsIsTrue =
        refl
    ; selectedCMPointContributesZero =
        true
    ; selectedCMPointContributesZeroIsTrue =
        refl
    ; otherCMPointsMayContribute =
        true
    ; otherCMPointsMayContributeIsTrue =
        refl
    ; deg23ResidualExplained =
        false
    ; deg23ResidualExplainedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; statement =
        fullTraceFormulaStatement
    ; statementIsCanonical =
        refl
    }
