module DASHI.Physics.Closure.Deg23HeckeEigenvalueReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Deg23ResidualDiagnosticReceipt as Deg23

------------------------------------------------------------------------
-- Hecke-eigenvalue diagnostic for the p3-p5 deg23 residual.
--
-- The requested check is finite: expand
--
--   f(q) = q * prod_n (1 - q^n)^2 (1 - q^(7n))^2
--
-- through q^5 and inspect a5.  The local computation gives
--
--   f(q) = q - 2 q^2 - q^3 + 0 q^4 + q^5 + 6 q^6 + ...
--
-- so a5 = +1 for this eta-product normalization.  This does not resolve the
-- natural deg23 residual 14 -> 14.302.  The prompt-quoted a5 = -2 expansion is
-- therefore retained only as a rejected normalization target.

data SignedCoefficient : Set where
  negativeCoefficient :
    SignedCoefficient

  zeroCoefficient :
    SignedCoefficient

  positiveCoefficient :
    SignedCoefficient

data Deg23HeckeDiagnosticStatus : Set where
  etaProductA5ComputedButResidualNotResolved :
    Deg23HeckeDiagnosticStatus

data Deg23HeckePromotionFlag : Set where

deg23HeckePromotionFlagImpossibleHere :
  Deg23HeckePromotionFlag →
  ⊥
deg23HeckePromotionFlagImpossibleHere ()

etaProductLevelSevenFormula : String
etaProductLevelSevenFormula =
  "f(q)=q*prod_n(1-q^n)^2(1-q^(7n))^2"

etaProductComputedExpansionPrefix : String
etaProductComputedExpansionPrefix =
  "q - 2q^2 - q^3 + 0q^4 + q^5 + 6q^6 + ..."

promptQuotedExpansionPrefix : String
promptQuotedExpansionPrefix =
  "q - 2q^2 - 3q^3 + 2q^4 - 2q^5 + ..."

record Deg23HeckeEigenvalueReceipt : Set where
  field
    residualReceipt :
      Deg23.Deg23ResidualDiagnosticReceipt

    naturalDeg23StillFourteen :
      Deg23.naturalDeg23 residualReceipt ≡ 14

    status :
      Deg23HeckeDiagnosticStatus

    etaProductFormula :
      String

    etaProductFormulaIsCanonical :
      etaProductFormula ≡ etaProductLevelSevenFormula

    computedExpansionPrefix :
      String

    computedExpansionPrefixIsCanonical :
      computedExpansionPrefix ≡ etaProductComputedExpansionPrefix

    promptExpansionPrefix :
      String

    promptExpansionRecordedForRejection :
      promptExpansionPrefix ≡ promptQuotedExpansionPrefix

    computedA5Sign :
      SignedCoefficient

    computedA5SignIsPositive :
      computedA5Sign ≡ positiveCoefficient

    computedA5Abs :
      Nat

    computedA5AbsIsOne :
      computedA5Abs ≡ 1

    promptQuotedA5Sign :
      SignedCoefficient

    promptQuotedA5SignIsNegative :
      promptQuotedA5Sign ≡ negativeCoefficient

    promptQuotedA5Abs :
      Nat

    promptQuotedA5AbsIsTwo :
      promptQuotedA5Abs ≡ 2

    promptExpansionMatchesEtaProductComputation :
      Bool

    promptExpansionMatchesEtaProductComputationIsFalse :
      promptExpansionMatchesEtaProductComputation ≡ false

    correctedDeg23ByAbsA5 :
      Nat

    correctedDeg23ByAbsA5IsFourteen :
      correctedDeg23ByAbsA5 ≡ 14

    correctedDeg23ByPromptAbsA5 :
      Nat

    correctedDeg23ByPromptAbsA5IsTwentyEight :
      correctedDeg23ByPromptAbsA5 ≡ 28

    heckeA5ResolvesDeg23Residual :
      Bool

    heckeA5ResolvesDeg23ResidualIsFalse :
      heckeA5ResolvesDeg23Residual ≡ false

    rgRunningHypothesisClosed :
      Bool

    rgRunningHypothesisClosedIsFalse :
      rgRunningHypothesisClosed ≡ false

    vcbPromotionClaimed :
      Bool

    vcbPromotionClaimedIsFalse :
      vcbPromotionClaimed ≡ false

    promotionFlags :
      List Deg23HeckePromotionFlag

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Deg23HeckeEigenvalueReceipt public

canonicalDeg23HeckeEigenvalueReceipt :
  Deg23HeckeEigenvalueReceipt
canonicalDeg23HeckeEigenvalueReceipt =
  record
    { residualReceipt =
        Deg23.canonicalDeg23ResidualDiagnosticReceipt
    ; naturalDeg23StillFourteen =
        refl
    ; status =
        etaProductA5ComputedButResidualNotResolved
    ; etaProductFormula =
        etaProductLevelSevenFormula
    ; etaProductFormulaIsCanonical =
        refl
    ; computedExpansionPrefix =
        etaProductComputedExpansionPrefix
    ; computedExpansionPrefixIsCanonical =
        refl
    ; promptExpansionPrefix =
        promptQuotedExpansionPrefix
    ; promptExpansionRecordedForRejection =
        refl
    ; computedA5Sign =
        positiveCoefficient
    ; computedA5SignIsPositive =
        refl
    ; computedA5Abs =
        1
    ; computedA5AbsIsOne =
        refl
    ; promptQuotedA5Sign =
        negativeCoefficient
    ; promptQuotedA5SignIsNegative =
        refl
    ; promptQuotedA5Abs =
        2
    ; promptQuotedA5AbsIsTwo =
        refl
    ; promptExpansionMatchesEtaProductComputation =
        false
    ; promptExpansionMatchesEtaProductComputationIsFalse =
        refl
    ; correctedDeg23ByAbsA5 =
        14
    ; correctedDeg23ByAbsA5IsFourteen =
        refl
    ; correctedDeg23ByPromptAbsA5 =
        28
    ; correctedDeg23ByPromptAbsA5IsTwentyEight =
        refl
    ; heckeA5ResolvesDeg23Residual =
        false
    ; heckeA5ResolvesDeg23ResidualIsFalse =
        refl
    ; rgRunningHypothesisClosed =
        false
    ; rgRunningHypothesisClosedIsFalse =
        refl
    ; vcbPromotionClaimed =
        false
    ; vcbPromotionClaimedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The eta-product expansion check gives a5=+1 through q^5"
        ∷ "The quoted a5=-2 expansion is not the expansion of the selected eta product"
        ∷ "Multiplying deg23=14 by |a5| leaves 14; using the quoted |a5|=2 would overcorrect to 28"
        ∷ "The 14 -> 14.302 residual remains open; no Vcb or Wolfenstein-A promotion is claimed"
        ∷ []
    }

deg23HeckeComputedA5IsPositiveOne :
  computedA5Sign canonicalDeg23HeckeEigenvalueReceipt
  ≡
  positiveCoefficient
deg23HeckeComputedA5IsPositiveOne =
  refl

deg23HeckeDoesNotResolveResidual :
  heckeA5ResolvesDeg23Residual canonicalDeg23HeckeEigenvalueReceipt
  ≡
  false
deg23HeckeDoesNotResolveResidual =
  refl

deg23HeckeDoesNotPromoteVcb :
  vcbPromotionClaimed canonicalDeg23HeckeEigenvalueReceipt
  ≡
  false
deg23HeckeDoesNotPromoteVcb =
  refl
