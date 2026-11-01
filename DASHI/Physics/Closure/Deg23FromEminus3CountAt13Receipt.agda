module DASHI.Physics.Closure.Deg23FromEminus3CountAt13Receipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.EichlerSelbergAtCMPointReceipt as ES

------------------------------------------------------------------------
-- C3: explicit E_-3 count at p=13.

data Deg23Eminus3F13Contribution : Set where
  affinePointCountEleven :
    Deg23Eminus3F13Contribution

  pointAtInfinityOne :
    Deg23Eminus3F13Contribution

  totalPointCountTwelve :
    Deg23Eminus3F13Contribution

  traceA13Two :
    Deg23Eminus3F13Contribution

canonicalDeg23Eminus3F13Contributions :
  List Deg23Eminus3F13Contribution
canonicalDeg23Eminus3F13Contributions =
  affinePointCountEleven
  ∷ pointAtInfinityOne
  ∷ totalPointCountTwelve
  ∷ traceA13Two
  ∷ []

data Deg23FromEminus3CountAt13Promotion : Set where

deg23FromEminus3CountAt13PromotionImpossibleHere :
  Deg23FromEminus3CountAt13Promotion →
  ⊥
deg23FromEminus3CountAt13PromotionImpossibleHere ()

countStatement : String
countStatement =
  "For E_-3: y^2=x^3+1 over F_13 has 11 affine points plus infinity, so |E(F_13)|=12 and a_13=14-12=2."

record Deg23FromEminus3CountAt13Receipt : Setω where
  field
    eichlerSelbergReceipt :
      ES.EichlerSelbergAtCMPointReceipt

    eichlerSelbergTraceAgrees :
      ES.a13DiscMinusThree eichlerSelbergReceipt ≡ 2

    affinePointCount :
      Nat

    affinePointCountIsEleven :
      affinePointCount ≡ 11

    pointAtInfinity :
      Nat

    pointAtInfinityIsOne :
      pointAtInfinity ≡ 1

    totalPointCount :
      Nat

    totalPointCountIsTwelve :
      totalPointCount ≡ 12

    pPlusOne :
      Nat

    pPlusOneIsFourteen :
      pPlusOne ≡ 14

    traceA13 :
      Nat

    traceA13IsTwo :
      traceA13 ≡ 2

    eMinusSevenTraceA13 :
      Nat

    eMinusSevenTraceA13IsZero :
      eMinusSevenTraceA13 ≡ 0

    localProductEigenvalue :
      Nat

    localProductEigenvalueIsZero :
      localProductEigenvalue ≡ 0

    contributions :
      List Deg23Eminus3F13Contribution

    contributionsAreCanonical :
      contributions ≡ canonicalDeg23Eminus3F13Contributions

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    derivesDeg23Residual :
      Bool

    derivesDeg23ResidualIsFalse :
      derivesDeg23Residual ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List Deg23FromEminus3CountAt13Promotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ countStatement

open Deg23FromEminus3CountAt13Receipt public

canonicalDeg23FromEminus3CountAt13Receipt :
  Deg23FromEminus3CountAt13Receipt
canonicalDeg23FromEminus3CountAt13Receipt =
  record
    { eichlerSelbergReceipt =
        ES.canonicalEichlerSelbergAtCMPointReceipt
    ; eichlerSelbergTraceAgrees =
        refl
    ; affinePointCount =
        11
    ; affinePointCountIsEleven =
        refl
    ; pointAtInfinity =
        1
    ; pointAtInfinityIsOne =
        refl
    ; totalPointCount =
        12
    ; totalPointCountIsTwelve =
        refl
    ; pPlusOne =
        14
    ; pPlusOneIsFourteen =
        refl
    ; traceA13 =
        2
    ; traceA13IsTwo =
        refl
    ; eMinusSevenTraceA13 =
        0
    ; eMinusSevenTraceA13IsZero =
        refl
    ; localProductEigenvalue =
        0
    ; localProductEigenvalueIsZero =
        refl
    ; contributions =
        canonicalDeg23Eminus3F13Contributions
    ; contributionsAreCanonical =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; derivesDeg23Residual =
        false
    ; derivesDeg23ResidualIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        countStatement
    ; statementIsCanonical =
        refl
    }

deg23FromEminus3CountDoesNotDeriveResidual :
  derivesDeg23Residual canonicalDeg23FromEminus3CountAt13Receipt ≡ false
deg23FromEminus3CountDoesNotDeriveResidual =
  refl

deg23FromEminus3CountKeepsTerminalFalse :
  terminalClaimPromoted canonicalDeg23FromEminus3CountAt13Receipt ≡ false
deg23FromEminus3CountKeepsTerminalFalse =
  refl

deg23FromEminus3CountNoPromotion :
  Deg23FromEminus3CountAt13Promotion →
  ⊥
deg23FromEminus3CountNoPromotion =
  deg23FromEminus3CountAt13PromotionImpossibleHere
