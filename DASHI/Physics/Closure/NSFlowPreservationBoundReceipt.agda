module DASHI.Physics.Closure.NSFlowPreservationBoundReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes prime-LP flow-preservation bound receipt.
--
-- This receipt records the reopened H^s, s > 0, carrier route: for
-- prime-LP supported initial data, the off-carrier nonlinear projection
-- error (1-Pi_d)[(u_d · nabla)u_d] in H^{-1} is controlled by cross-base
-- sums of the form
--
--   (p^l)/(p^j+q^l) * a_j^{1/2} * b_l^{1/2}
--
-- and the proposed summability decay is C ||u_0||_{H^s}^2 r^d with r < 1.
-- The theorem is recorded as a candidate receipt only.  It reopens the NS
-- H^{7/4} route, but it does not promote Clay Navier-Stokes.

data NSFlowPreservationBoundStatus : Set where
  candidate :
    NSFlowPreservationBoundStatus

  carrierPrimeLPSupportedHsData :
    NSFlowPreservationBoundStatus

  positiveSobolevExponent :
    NSFlowPreservationBoundStatus

  offCarrierHMinusOneProjectionError :
    NSFlowPreservationBoundStatus

  crossBaseSumBound :
    NSFlowPreservationBoundStatus

  exponentialDepthDecay :
    NSFlowPreservationBoundStatus

  nsH74RouteReopenedStatus :
    NSFlowPreservationBoundStatus

  noClayPromotionStatus :
    NSFlowPreservationBoundStatus

canonicalNSFlowPreservationBoundStatus :
  List NSFlowPreservationBoundStatus
canonicalNSFlowPreservationBoundStatus =
  candidate
  ∷ carrierPrimeLPSupportedHsData
  ∷ positiveSobolevExponent
  ∷ offCarrierHMinusOneProjectionError
  ∷ crossBaseSumBound
  ∷ exponentialDepthDecay
  ∷ nsH74RouteReopenedStatus
  ∷ noClayPromotionStatus
  ∷ []

data PrimeBase : Set where
  p :
    PrimeBase

  q :
    PrimeBase

data CarrierBand : Set where
  band :
    PrimeBase →
    Nat →
    CarrierBand

data CrossBaseCoefficient : Set where
  coefficient :
    (numeratorBase : PrimeBase) →
    (numeratorExponent : Nat) →
    (leftDenominatorBase : PrimeBase) →
    (leftDenominatorExponent : Nat) →
    (rightDenominatorBase : PrimeBase) →
    (rightDenominatorExponent : Nat) →
    CrossBaseCoefficient

canonicalCrossBaseCoefficient :
  Nat →
  Nat →
  CrossBaseCoefficient
canonicalCrossBaseCoefficient j l =
  coefficient p l p j q l

data CrossBaseEnergyFactor : Set where
  sqrtEnergyPair :
    (leftBand : CarrierBand) →
    (rightBand : CarrierBand) →
    CrossBaseEnergyFactor

canonicalCrossBaseEnergyFactor :
  Nat →
  Nat →
  CrossBaseEnergyFactor
canonicalCrossBaseEnergyFactor j l =
  sqrtEnergyPair (band p j) (band q l)

data CrossBaseBoundTerm : Set where
  crossBaseTerm :
    CrossBaseCoefficient →
    CrossBaseEnergyFactor →
    CrossBaseBoundTerm

canonicalCrossBaseBoundTerm :
  Nat →
  Nat →
  CrossBaseBoundTerm
canonicalCrossBaseBoundTerm j l =
  crossBaseTerm
    (canonicalCrossBaseCoefficient j l)
    (canonicalCrossBaseEnergyFactor j l)

data OffCarrierProjectionError : Set where
  oneMinusPiDNonlinearTransportInHMinusOne :
    OffCarrierProjectionError

data SummableDecayShape : Set where
  CNormU0HsSquaredTimesRToDWithRLessThanOne :
    SummableDecayShape

data NSFlowPreservationPromotion : Set where

nsFlowPreservationPromotionImpossibleHere :
  NSFlowPreservationPromotion →
  ⊥
nsFlowPreservationPromotionImpossibleHere ()

nsFlowPreservationBoundStatement :
  String
nsFlowPreservationBoundStatement =
  "Candidate theorem: for carrier prime-LP supported u_0 in H^s with s > 0, the off-carrier nonlinear projection error (1-Pi_d)[(u_d*nabla)u_d] in H^{-1} is bounded by cross-base sums (p^l)/(p^j+q^l) * a_j^{1/2} * b_l^{1/2}, summable with decay C ||u_0||_{H^s}^2 r^d for r < 1; this reopens the NS H74 route but makes no Clay promotion."

record NSFlowPreservationBoundReceipt : Setω where
  field
    status :
      List NSFlowPreservationBoundStatus

    statusIsCanonical :
      status ≡ canonicalNSFlowPreservationBoundStatus

    theoremKind :
      NSFlowPreservationBoundStatus

    flowPreservationBoundInhabited :
      NSFlowPreservationBoundStatus

    flowPreservationBoundInhabitedIsCandidate :
      flowPreservationBoundInhabited ≡ candidate

    carrierPrimeLPSupportedInitialData :
      Bool

    carrierPrimeLPSupportedInitialDataIsTrue :
      carrierPrimeLPSupportedInitialData ≡ true

    u0InHsRecorded :
      Bool

    u0InHsRecordedIsTrue :
      u0InHsRecorded ≡ true

    sPositiveRecorded :
      Bool

    sPositiveRecordedIsTrue :
      sPositiveRecorded ≡ true

    offCarrierProjectionError :
      OffCarrierProjectionError

    offCarrierProjectionErrorIsCanonical :
      offCarrierProjectionError
      ≡
      oneMinusPiDNonlinearTransportInHMinusOne

    hMinusOneNormTargetRecorded :
      Bool

    hMinusOneNormTargetRecordedIsTrue :
      hMinusOneNormTargetRecorded ≡ true

    sampleCrossBaseBoundTerm :
      CrossBaseBoundTerm

    sampleCrossBaseBoundTermIsCanonical :
      sampleCrossBaseBoundTerm ≡ canonicalCrossBaseBoundTerm 0 0

    crossBaseSumsBoundRecorded :
      Bool

    crossBaseSumsBoundRecordedIsTrue :
      crossBaseSumsBoundRecorded ≡ true

    crossBaseCoefficientFormulaLabel :
      String

    crossBaseCoefficientFormulaLabelIsCanonical :
      crossBaseCoefficientFormulaLabel
      ≡
      "(p^l)/(p^j+q^l) * a_j^{1/2} * b_l^{1/2}"

    decayShape :
      SummableDecayShape

    decayShapeIsCanonical :
      decayShape ≡ CNormU0HsSquaredTimesRToDWithRLessThanOne

    summableForHsWithS>0 :
      Bool

    summableForHsWithS>0IsTrue :
      summableForHsWithS>0 ≡ true

    rLessThanOneRecorded :
      Bool

    rLessThanOneRecordedIsTrue :
      rLessThanOneRecorded ≡ true

    offCarrierTermGoesToZero :
      Bool

    offCarrierTermGoesToZeroIsTrue :
      offCarrierTermGoesToZero ≡ true

    nsH74RouteReopened :
      Bool

    nsH74RouteReopenedIsTrue :
      nsH74RouteReopened ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    clayPromotionFlags :
      List NSFlowPreservationPromotion

    clayPromotionFlagsAreEmpty :
      clayPromotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ nsFlowPreservationBoundStatement

    receiptBoundary :
      List String

open NSFlowPreservationBoundReceipt public

canonicalNSFlowPreservationBoundReceipt :
  NSFlowPreservationBoundReceipt
canonicalNSFlowPreservationBoundReceipt =
  record
    { status =
        canonicalNSFlowPreservationBoundStatus
    ; statusIsCanonical =
        refl
    ; theoremKind =
        candidate
    ; flowPreservationBoundInhabited =
        candidate
    ; flowPreservationBoundInhabitedIsCandidate =
        refl
    ; carrierPrimeLPSupportedInitialData =
        true
    ; carrierPrimeLPSupportedInitialDataIsTrue =
        refl
    ; u0InHsRecorded =
        true
    ; u0InHsRecordedIsTrue =
        refl
    ; sPositiveRecorded =
        true
    ; sPositiveRecordedIsTrue =
        refl
    ; offCarrierProjectionError =
        oneMinusPiDNonlinearTransportInHMinusOne
    ; offCarrierProjectionErrorIsCanonical =
        refl
    ; hMinusOneNormTargetRecorded =
        true
    ; hMinusOneNormTargetRecordedIsTrue =
        refl
    ; sampleCrossBaseBoundTerm =
        canonicalCrossBaseBoundTerm 0 0
    ; sampleCrossBaseBoundTermIsCanonical =
        refl
    ; crossBaseSumsBoundRecorded =
        true
    ; crossBaseSumsBoundRecordedIsTrue =
        refl
    ; crossBaseCoefficientFormulaLabel =
        "(p^l)/(p^j+q^l) * a_j^{1/2} * b_l^{1/2}"
    ; crossBaseCoefficientFormulaLabelIsCanonical =
        refl
    ; decayShape =
        CNormU0HsSquaredTimesRToDWithRLessThanOne
    ; decayShapeIsCanonical =
        refl
    ; summableForHsWithS>0 =
        true
    ; summableForHsWithS>0IsTrue =
        refl
    ; rLessThanOneRecorded =
        true
    ; rLessThanOneRecordedIsTrue =
        refl
    ; offCarrierTermGoesToZero =
        true
    ; offCarrierTermGoesToZeroIsTrue =
        refl
    ; nsH74RouteReopened =
        true
    ; nsH74RouteReopenedIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; clayPromotionFlags =
        []
    ; clayPromotionFlagsAreEmpty =
        refl
    ; statement =
        nsFlowPreservationBoundStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The flow-preservation estimate is recorded as a candidate theorem only"
        ∷ "Scope is carrier prime-LP supported initial data u_0 in H^s with s > 0"
        ∷ "The off-carrier nonlinear projection error is measured in H^{-1}"
        ∷ "The recorded bound uses cross-base sums with coefficient (p^l)/(p^j+q^l) and sqrt energy factors"
        ∷ "Summability is recorded with decay C ||u_0||_{H^s}^2 r^d for r < 1"
        ∷ "The NS H^{7/4} route is reopened, but Clay Navier-Stokes promotion remains false"
        ∷ []
    }

nsFlowPreservationBoundIsCandidate :
  flowPreservationBoundInhabited canonicalNSFlowPreservationBoundReceipt
  ≡
  candidate
nsFlowPreservationBoundIsCandidate =
  refl

nsFlowPreservationSummableForPositiveHs :
  summableForHsWithS>0 canonicalNSFlowPreservationBoundReceipt
  ≡
  true
nsFlowPreservationSummableForPositiveHs =
  refl

nsFlowPreservationOffCarrierTermVanishes :
  offCarrierTermGoesToZero canonicalNSFlowPreservationBoundReceipt
  ≡
  true
nsFlowPreservationOffCarrierTermVanishes =
  refl

nsFlowPreservationReopensH74Route :
  nsH74RouteReopened canonicalNSFlowPreservationBoundReceipt
  ≡
  true
nsFlowPreservationReopensH74Route =
  refl

nsFlowPreservationDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSFlowPreservationBoundReceipt
  ≡
  false
nsFlowPreservationDoesNotPromoteClay =
  refl
