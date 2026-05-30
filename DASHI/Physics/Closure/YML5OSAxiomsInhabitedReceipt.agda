module DASHI.Physics.Closure.YML5OSAxiomsInhabitedReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YML5OSAxiomsForGaugeSectorReceipt as L5

data YML5OSAxiomsInhabitedStatus : Set where
  candidateConditionalOnL3 :
    YML5OSAxiomsInhabitedStatus

data YML5EuclideanCovarianceSource : Set where
  candidate :
    YML5EuclideanCovarianceSource

data YML5OSAxiomsInhabitedPromotion : Set where

yml5OSAxiomsInhabitedPromotionImpossibleHere :
  YML5OSAxiomsInhabitedPromotion →
  ⊥
yml5OSAxiomsInhabitedPromotionImpossibleHere ()

yml5OSAxiomsInhabitedStatement : String
yml5OSAxiomsInhabitedStatement =
  "YML5 OS data are only candidate/conditional through L4 and candidate-only L3; no conditionallyInhabited promotion follows from the product-lattice receipt, and Clay plus terminal promotions remain false."

record YML5OSAxiomsInhabitedReceipt : Setω where
  field
    c1GaugeSectorReceipt :
      L5.YML5OSAxiomsForGaugeSectorReceipt

    c1IsConditionalOnL4 :
      L5.conditionalOnL4ContinuumLimit c1GaugeSectorReceipt ≡ true

    c1GaugeSectorOSAxiomsComplete :
      L5.gaugeSectorOSAxiomsConditionallyComplete c1GaugeSectorReceipt
        ≡ true

    c1KeepsUnconditionalOSFalse :
      L5.unconditionalOSAxiomsPromoted c1GaugeSectorReceipt ≡ false

    c1KeepsClayFalse :
      L5.clayYangMillsPromoted c1GaugeSectorReceipt ≡ false

    c1KeepsTerminalFalse :
      L5.terminalClayClaimPromoted c1GaugeSectorReceipt ≡ false

    ymL5OSAxiomsInhabited :
      YML5OSAxiomsInhabitedStatus

    ymL5OSAxiomsInhabitedIsConditionalOnL4 :
      ymL5OSAxiomsInhabited ≡ candidateConditionalOnL3

    osPositivityInherited :
      Bool

    osPositivityInheritedIsTrue :
      osPositivityInherited ≡ true

    euclideanCovarianceFromAnisotropyDecay :
      YML5EuclideanCovarianceSource

    euclideanCovarianceFromAnisotropyDecayIsCandidate :
      euclideanCovarianceFromAnisotropyDecay ≡ candidate

    clusteringFromStringTension :
      Bool

    clusteringFromStringTensionIsTrue :
      clusteringFromStringTension ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ yml5OSAxiomsInhabitedStatement

    promotionFlags :
      List YML5OSAxiomsInhabitedPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML5OSAxiomsInhabitedReceipt public

canonicalYML5OSAxiomsInhabitedReceipt :
  YML5OSAxiomsInhabitedReceipt
canonicalYML5OSAxiomsInhabitedReceipt =
  record
    { c1GaugeSectorReceipt =
        L5.canonicalYML5OSAxiomsForGaugeSectorReceipt
    ; c1IsConditionalOnL4 =
        refl
    ; c1GaugeSectorOSAxiomsComplete =
        refl
    ; c1KeepsUnconditionalOSFalse =
        refl
    ; c1KeepsClayFalse =
        refl
    ; c1KeepsTerminalFalse =
        refl
    ; ymL5OSAxiomsInhabited =
        candidateConditionalOnL3
    ; ymL5OSAxiomsInhabitedIsConditionalOnL4 =
        refl
    ; osPositivityInherited =
        true
    ; osPositivityInheritedIsTrue =
        refl
    ; euclideanCovarianceFromAnisotropyDecay =
        candidate
    ; euclideanCovarianceFromAnisotropyDecayIsCandidate =
        refl
    ; clusteringFromStringTension =
        true
    ; clusteringFromStringTensionIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        yml5OSAxiomsInhabitedStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Depends on YML5OSAxiomsForGaugeSectorReceipt as the C1 authority surface"
        ∷ "The surface remains candidate/conditional on L4 and candidate-only L3"
        ∷ "Product-lattice L3 conditionallyInhabited language is not promoted here"
        ∷ "Euclidean covariance from anisotropy decay is recorded only as candidate"
        ∷ "No Clay YM or terminal Clay promotion follows"
        ∷ []
    }

yml5OSAxiomsInhabitedIsConditional :
  ymL5OSAxiomsInhabited canonicalYML5OSAxiomsInhabitedReceipt
  ≡ candidateConditionalOnL3
yml5OSAxiomsInhabitedIsConditional = refl

yml5OSAxiomsInhabitedKeepsClayFalse :
  clayYangMillsPromoted canonicalYML5OSAxiomsInhabitedReceipt
  ≡ false
yml5OSAxiomsInhabitedKeepsClayFalse = refl

yml5OSAxiomsInhabitedKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML5OSAxiomsInhabitedReceipt
  ≡ false
yml5OSAxiomsInhabitedKeepsTerminalFalse = refl
