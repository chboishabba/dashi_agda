module DASHI.Physics.Closure.YML5OSAxiomsForGaugeSectorReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ReflectionPositivityForWilsonReceipt as RP
import DASHI.Physics.Closure.YML4ContinuumLimitReceipt as L4
import DASHI.Physics.Closure.YML3TightnessFromKRunningReceipt as L3

data YML5OSGaugeSectorStatus : Set where
  osGaugeSectorConditionallyReceiptedOnL4 :
    YML5OSGaugeSectorStatus

data YML5OSAxiomForGaugeSector : Set where
  osRegularityTemperedSchwingerFunctions :
    YML5OSAxiomForGaugeSector
  osEuclideanCovarianceFromContinuumLimit :
    YML5OSAxiomForGaugeSector
  osReflectionPositivityFromWilsonMeasure :
    YML5OSAxiomForGaugeSector
  osSymmetryForGaugeInvariantObservables :
    YML5OSAxiomForGaugeSector
  osClusteringForVacuumSector :
    YML5OSAxiomForGaugeSector

canonicalYML5OSAxiomsForGaugeSector :
  List YML5OSAxiomForGaugeSector
canonicalYML5OSAxiomsForGaugeSector =
  osRegularityTemperedSchwingerFunctions
  ∷ osEuclideanCovarianceFromContinuumLimit
  ∷ osReflectionPositivityFromWilsonMeasure
  ∷ osSymmetryForGaugeInvariantObservables
  ∷ osClusteringForVacuumSector
  ∷ []

data YML5OSPromotion : Set where

yml5OSPromotionImpossibleHere : YML5OSPromotion → ⊥
yml5OSPromotionImpossibleHere ()

yml5OSAxiomsStatement : String
yml5OSAxiomsStatement =
  "YML5 records only candidate OS data for the gauge sector, conditional on the YML4 continuum candidate and the still candidate-only L3 tightness input; Clay YM remains false."

record YML5OSAxiomsForGaugeSectorReceipt : Setω where
  field
    status :
      YML5OSGaugeSectorStatus

    continuumLimitReceipt :
      L4.YML4ContinuumLimitReceipt

    l4CandidateWeakLimitAvailable :
      L4.candidateWeakLimitConstructed continuumLimitReceipt ≡ true

    l4ContinuumYMCandidateAvailable :
      L4.rigorousContinuumYMCandidateConstructed continuumLimitReceipt
        ≡ true

    l4KeepsClayFalse :
      L4.clayYangMillsPromoted continuumLimitReceipt ≡ false

    l4PriorL3StillCandidateOnly :
      L3.ymL3TightnessConstructed
        (L4.priorL3Receipt continuumLimitReceipt)
        ≡ false

    reflectionReceipt :
      RP.ReflectionPositivityForWilsonReceipt

    finiteWilsonReflectionPositive :
      RP.finiteLatticeReflectionPositivityInherited reflectionReceipt
        ≡ true

    conditionalOnL4ContinuumLimit :
      Bool
    conditionalOnL4ContinuumLimitIsTrue :
      conditionalOnL4ContinuumLimit ≡ true

    osPositivityConditionallyEstablished :
      Bool
    osPositivityConditionallyEstablishedIsTrue :
      osPositivityConditionallyEstablished ≡ true

    osEuclideanCovarianceConditionallyEstablished :
      Bool
    osEuclideanCovarianceConditionallyEstablishedIsTrue :
      osEuclideanCovarianceConditionallyEstablished ≡ true

    osClusteringConditionallyEstablished :
      Bool
    osClusteringConditionallyEstablishedIsTrue :
      osClusteringConditionallyEstablished ≡ true

    osTemperednessConditionallyEstablished :
      Bool
    osTemperednessConditionallyEstablishedIsTrue :
      osTemperednessConditionallyEstablished ≡ true

    osSymmetryConditionallyEstablished :
      Bool
    osSymmetryConditionallyEstablishedIsTrue :
      osSymmetryConditionallyEstablished ≡ true

    gaugeSectorOSAxiomsConditionallyComplete :
      Bool
    gaugeSectorOSAxiomsConditionallyCompleteIsTrue :
      gaugeSectorOSAxiomsConditionallyComplete ≡ true

    unconditionalOSAxiomsPromoted :
      Bool
    unconditionalOSAxiomsPromotedIsFalse :
      unconditionalOSAxiomsPromoted ≡ false

    clayYangMillsPromoted :
      Bool
    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool
    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    osAxioms :
      List YML5OSAxiomForGaugeSector
    osAxiomsAreCanonical :
      osAxioms ≡ canonicalYML5OSAxiomsForGaugeSector

    statement :
      String
    statementIsCanonical :
      statement ≡ yml5OSAxiomsStatement

    promotionFlags :
      List YML5OSPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML5OSAxiomsForGaugeSectorReceipt public

canonicalYML5OSAxiomsForGaugeSectorReceipt :
  YML5OSAxiomsForGaugeSectorReceipt
canonicalYML5OSAxiomsForGaugeSectorReceipt =
  record
    { status = osGaugeSectorConditionallyReceiptedOnL4
    ; continuumLimitReceipt = L4.canonicalYML4ContinuumLimitReceipt
    ; l4CandidateWeakLimitAvailable = refl
    ; l4ContinuumYMCandidateAvailable = refl
    ; l4KeepsClayFalse = refl
    ; l4PriorL3StillCandidateOnly = refl
    ; reflectionReceipt = RP.canonicalReflectionPositivityForWilsonReceipt
    ; finiteWilsonReflectionPositive = refl
    ; conditionalOnL4ContinuumLimit = true
    ; conditionalOnL4ContinuumLimitIsTrue = refl
    ; osPositivityConditionallyEstablished = true
    ; osPositivityConditionallyEstablishedIsTrue = refl
    ; osEuclideanCovarianceConditionallyEstablished = true
    ; osEuclideanCovarianceConditionallyEstablishedIsTrue = refl
    ; osClusteringConditionallyEstablished = true
    ; osClusteringConditionallyEstablishedIsTrue = refl
    ; osTemperednessConditionallyEstablished = true
    ; osTemperednessConditionallyEstablishedIsTrue = refl
    ; osSymmetryConditionallyEstablished = true
    ; osSymmetryConditionallyEstablishedIsTrue = refl
    ; gaugeSectorOSAxiomsConditionallyComplete = true
    ; gaugeSectorOSAxiomsConditionallyCompleteIsTrue = refl
    ; unconditionalOSAxiomsPromoted = false
    ; unconditionalOSAxiomsPromotedIsFalse = refl
    ; clayYangMillsPromoted = false
    ; clayYangMillsPromotedIsFalse = refl
    ; terminalClayClaimPromoted = false
    ; terminalClayClaimPromotedIsFalse = refl
    ; osAxioms = canonicalYML5OSAxiomsForGaugeSector
    ; osAxiomsAreCanonical = refl
    ; statement = yml5OSAxiomsStatement
    ; statementIsCanonical = refl
    ; promotionFlags = []
    ; promotionFlagsAreEmpty = refl
    ; receiptBoundary =
        "OS positivity, covariance, and clustering are receipted only as candidate data over the YML4 continuum candidate"
        ∷ "Finite Wilson reflection positivity is used as the lattice-side authority input"
        ∷ "The YML4 input still depends on candidate-only/blocked L3 tightness"
        ∷ "The receipt is not an unconditional OS theorem for the whole repository"
        ∷ "No Clay YM or terminal Clay promotion follows"
        ∷ []
    }

yml5OSGaugeSectorKeepsClayFalse :
  clayYangMillsPromoted canonicalYML5OSAxiomsForGaugeSectorReceipt
  ≡ false
yml5OSGaugeSectorKeepsClayFalse = refl

yml5OSGaugeSectorKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML5OSAxiomsForGaugeSectorReceipt
  ≡ false
yml5OSGaugeSectorKeepsTerminalFalse = refl
