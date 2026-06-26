module DASHI.Physics.Closure.CSLevelRunningLawReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierGaugeCouplingFromCSLevelReceipt as Coupling
import DASHI.Physics.Closure.WilsonBetaFromCSLevelReceipt as WilsonBeta

------------------------------------------------------------------------
-- CS-level running-law receipt.

data CSLevelRunningLawStatus : Set where
  dimensionalTransmutationRunningLawRecorded :
    CSLevelRunningLawStatus

  weakCouplingCandidateStatusOnly :
    CSLevelRunningLawStatus

  notAClayPromotion :
    CSLevelRunningLawStatus

canonicalCSLevelRunningLawStatus :
  List CSLevelRunningLawStatus
canonicalCSLevelRunningLawStatus =
  dimensionalTransmutationRunningLawRecorded
  ∷ weakCouplingCandidateStatusOnly
  ∷ notAClayPromotion
  ∷ []

data CSLevelRunningLawPromotion : Set where

csLevelRunningLawPromotionImpossibleHere :
  CSLevelRunningLawPromotion →
  ⊥
csLevelRunningLawPromotionImpossibleHere ()

csLevelRunningLawEquation : String
csLevelRunningLawEquation =
  "k(mu)=b0/(2pi)log(mu/Lambda_c)"

csLevelLatticeSpacingEquation : String
csLevelLatticeSpacingEquation =
  "a(k)=Lambda_c^-1 exp(-2pi k/b0)"

csLevelSU2SpecialisationEquation : String
csLevelSU2SpecialisationEquation =
  "b0_SU2=22/3, Lambda_c=1.59 GeV, a(k)=exp(-3pi k/11)/Lambda_c"

csLevelMuKFamilyEquation : String
csLevelMuKFamilyEquation =
  "mu_k=Lambda_c exp(2pi k/b0)"

csLevelRunningLawNumericalAnchors : List String
csLevelRunningLawNumericalAnchors =
  "k=1 -> 0.0526 fm"
  ∷ "k=5 -> 0.0017 fm"
  ∷ []

csLevelRunningLawStatement : String
csLevelRunningLawStatement =
  "The stated CS-level running law is recorded as a dimensional-transmutation weak-coupling candidate; it does not construct Wilson continuum tightness, continuum Yang-Mills, or Clay promotion."

record CSLevelRunningLawReceipt : Setω where
  field
    carrierCouplingReceipt :
      Coupling.CarrierGaugeCouplingFromCSLevelReceipt

    carrierCouplingKeepsRunningFalse :
      Coupling.kRunningConstructed carrierCouplingReceipt ≡ false

    wilsonBetaReceipt :
      WilsonBeta.WilsonBetaFromCSLevelReceipt

    wilsonBetaTrajectoryStillFalse :
      WilsonBeta.betaToInfinityTrajectoryConstructed wilsonBetaReceipt
        ≡ false

    status :
      List CSLevelRunningLawStatus

    statusIsCanonical :
      status ≡ canonicalCSLevelRunningLawStatus

    runningLawEquation :
      String

    runningLawEquationIsCanonical :
      runningLawEquation ≡ csLevelRunningLawEquation

    latticeSpacingEquation :
      String

    latticeSpacingEquationIsCanonical :
      latticeSpacingEquation ≡ csLevelLatticeSpacingEquation

    su2OneLoopB0Numerator :
      Nat

    su2OneLoopB0NumeratorIsTwentyTwo :
      su2OneLoopB0Numerator ≡ 22

    su2OneLoopB0Denominator :
      Nat

    su2OneLoopB0DenominatorIsThree :
      su2OneLoopB0Denominator ≡ 3

    lambdaCGeV :
      String

    lambdaCGeVIsCanonical :
      lambdaCGeV ≡ "1.59 GeV"

    su2SpecialisationEquation :
      String

    su2SpecialisationEquationIsCanonical :
      su2SpecialisationEquation ≡ csLevelSU2SpecialisationEquation

    muKFamilyEquation :
      String

    muKFamilyEquationIsCanonical :
      muKFamilyEquation ≡ csLevelMuKFamilyEquation

    numericalAnchors :
      List String

    numericalAnchorsAreCanonical :
      numericalAnchors ≡ csLevelRunningLawNumericalAnchors

    dimensionalTransmutationCandidateRecorded :
      Bool

    dimensionalTransmutationCandidateRecordedIsTrue :
      dimensionalTransmutationCandidateRecorded ≡ true

    runningLawCandidateRecorded :
      Bool

    runningLawCandidateRecordedIsTrue :
      runningLawCandidateRecorded ≡ true

    standardAuthorityRouteRequired :
      Bool

    standardAuthorityRouteRequiredIsTrue :
      standardAuthorityRouteRequired ≡ true

    standardAuthorityRouteConstructed :
      Bool

    standardAuthorityRouteConstructedIsFalse :
      standardAuthorityRouteConstructed ≡ false

    weakCouplingCandidateOnly :
      Bool

    weakCouplingCandidateOnlyIsTrue :
      weakCouplingCandidateOnly ≡ true

    wilsonMeasureTightnessConstructed :
      Bool

    wilsonMeasureTightnessConstructedIsFalse :
      wilsonMeasureTightnessConstructed ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ true

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
      statement ≡ csLevelRunningLawStatement

    promotionFlags :
      List CSLevelRunningLawPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CSLevelRunningLawReceipt public

canonicalCSLevelRunningLawReceipt :
  CSLevelRunningLawReceipt
canonicalCSLevelRunningLawReceipt =
  record
    { carrierCouplingReceipt =
        Coupling.canonicalCarrierGaugeCouplingFromCSLevelReceipt
    ; carrierCouplingKeepsRunningFalse =
        refl
    ; wilsonBetaReceipt =
        WilsonBeta.canonicalWilsonBetaFromCSLevelReceipt
    ; wilsonBetaTrajectoryStillFalse =
        refl
    ; status =
        canonicalCSLevelRunningLawStatus
    ; statusIsCanonical =
        refl
    ; runningLawEquation =
        csLevelRunningLawEquation
    ; runningLawEquationIsCanonical =
        refl
    ; latticeSpacingEquation =
        csLevelLatticeSpacingEquation
    ; latticeSpacingEquationIsCanonical =
        refl
    ; su2OneLoopB0Numerator =
        22
    ; su2OneLoopB0NumeratorIsTwentyTwo =
        refl
    ; su2OneLoopB0Denominator =
        3
    ; su2OneLoopB0DenominatorIsThree =
        refl
    ; lambdaCGeV =
        "1.59 GeV"
    ; lambdaCGeVIsCanonical =
        refl
    ; su2SpecialisationEquation =
        csLevelSU2SpecialisationEquation
    ; su2SpecialisationEquationIsCanonical =
        refl
    ; muKFamilyEquation =
        csLevelMuKFamilyEquation
    ; muKFamilyEquationIsCanonical =
        refl
    ; numericalAnchors =
        csLevelRunningLawNumericalAnchors
    ; numericalAnchorsAreCanonical =
        refl
    ; dimensionalTransmutationCandidateRecorded =
        true
    ; dimensionalTransmutationCandidateRecordedIsTrue =
        refl
    ; runningLawCandidateRecorded =
        true
    ; runningLawCandidateRecordedIsTrue =
        refl
    ; standardAuthorityRouteRequired =
        true
    ; standardAuthorityRouteRequiredIsTrue =
        refl
    ; standardAuthorityRouteConstructed =
        false
    ; standardAuthorityRouteConstructedIsFalse =
        refl
    ; weakCouplingCandidateOnly =
        true
    ; weakCouplingCandidateOnlyIsTrue =
        refl
    ; wilsonMeasureTightnessConstructed =
        false
    ; wilsonMeasureTightnessConstructedIsFalse =
        refl
    ; continuumYangMillsConstructed =
        true
    ; continuumYangMillsConstructedIsFalse =
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
        csLevelRunningLawStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The exact stated running law k(mu)=b0/(2pi)log(mu/Lambda_c) is recorded"
        ∷ "The inverse lattice-spacing law a(k)=Lambda_c^-1 exp(-2pi k/b0) is recorded"
        ∷ "b0_SU2=22/3, Lambda_c=1.59 GeV, a(k)=exp(-3pi k/11)/Lambda_c, and the mu_k family are recorded"
        ∷ "The receipt is a weak-coupling dimensional-transmutation candidate only; standard authority is required and not constructed"
        ∷ "No Wilson measure tightness, continuum Yang-Mills, Clay Yang-Mills, or terminal Clay promotion follows"
        ∷ []
    }

csLevelRunningLawKeepsClayFalse :
  clayYangMillsPromoted canonicalCSLevelRunningLawReceipt ≡ false
csLevelRunningLawKeepsClayFalse =
  refl

csLevelRunningLawKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalCSLevelRunningLawReceipt ≡ false
csLevelRunningLawKeepsTerminalFalse =
  refl
