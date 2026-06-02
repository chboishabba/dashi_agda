module DASHI.Physics.Closure.OverlapDominationLemmaReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierAreaLawBalabanSeedReceipt as Area
import DASHI.Physics.Closure.Gate3NormDictionary as Gate3
import DASHI.Physics.Closure.PolymerKPAsMDLReceipt as KP
import DASHI.Physics.Closure.UltrametricClusterSeparationReceipt as Ultra

------------------------------------------------------------------------
-- Overlap-domination / KP combinatorial receipt.
--
-- This is a finite-carrier receipt.  It records the combinatorial
-- bookkeeping surface that separates exact disjoint decorrelation from
-- overlapping-plaquette domination.  It consumes the exact disjoint input
-- from UltrametricClusterSeparationReceipt, records overlapping plaquettes
-- through a finite/geometric-tail carrier code, and keeps all continuum
-- Kotecky-Preiss, infinite-volume polymer, Balaban RG, carrier area-law,
-- and Clay Yang-Mills promotions false.

data OverlapDominationStatus : Set where
  finiteCarrierOverlapDominationKPBookkeepingRecorded :
    OverlapDominationStatus

data OverlapDominationInput : Set where
  ultrametricExactDisjointDecorrelationFunction :
    OverlapDominationInput

  ultrametricFiniteBetaMinEulerSurface :
    OverlapDominationInput

  gate3FiniteLimit71CarrierSurface :
    OverlapDominationInput

  polymerKPAsMDLBookkeepingSurface :
    OverlapDominationInput

  carrierAreaLawBalabanSeedNonPromotionBoundary :
    OverlapDominationInput

canonicalOverlapDominationInputs :
  List OverlapDominationInput
canonicalOverlapDominationInputs =
  ultrametricExactDisjointDecorrelationFunction
  ∷ ultrametricFiniteBetaMinEulerSurface
  ∷ gate3FiniteLimit71CarrierSurface
  ∷ polymerKPAsMDLBookkeepingSurface
  ∷ carrierAreaLawBalabanSeedNonPromotionBoundary
  ∷ []

data OverlapTailStatus : Set where
  overlappingPlaquettesBoundedByFiniteGeometricTailCarrierCode :
    OverlapTailStatus

data KPUniformityStatus : Set where
  kpUniformityRecordedAsFiniteCarrierSurfaceOnly :
    KPUniformityStatus

data OverlapDominationNonClaim : Set where
  noContinuumKPProof :
    OverlapDominationNonClaim

  noInfiniteVolumePolymerExpansion :
    OverlapDominationNonClaim

  noBalabanRGConvergenceProof :
    OverlapDominationNonClaim

  noCarrierAreaLawTheorem :
    OverlapDominationNonClaim

  noClayYangMillsPromotion :
    OverlapDominationNonClaim

canonicalOverlapDominationNonClaims :
  List OverlapDominationNonClaim
canonicalOverlapDominationNonClaims =
  noContinuumKPProof
  ∷ noInfiniteVolumePolymerExpansion
  ∷ noBalabanRGConvergenceProof
  ∷ noCarrierAreaLawTheorem
  ∷ noClayYangMillsPromotion
  ∷ []

data OverlapDominationPromotion : Set where

overlapDominationPromotionImpossibleHere :
  OverlapDominationPromotion →
  ⊥
overlapDominationPromotionImpossibleHere ()

record FiniteGeometricTailCode : Set where
  constructor finiteTail
  field
    betaMinNumerator :
      Nat

    betaMinDenominator :
      Nat

    positiveTailRecorded :
      Bool

open FiniteGeometricTailCode public

canonicalOverlapTailCode :
  FiniteGeometricTailCode
canonicalOverlapTailCode =
  finiteTail
    Ultra.betaMinNumerator
    Ultra.betaMinDenominator
    true

overlapTailStatement : String
overlapTailStatement =
  "Overlapping plaquettes are routed to a finite carrier geometric-tail code using the ultrametric beta_min bookkeeping; positive-tail status is recorded as finite carrier bookkeeping, not as an analytic continuum estimate."

kpUniformityStatement : String
kpUniformityStatement =
  "KP uniformity is recorded only as a finite carrier surface over the Gate3 limit71/SSP bookkeeping and PolymerKPAsMDL shape; no continuum KP or infinite-volume polymer expansion is promoted."

overlapDominationStatement : String
overlapDominationStatement =
  "The overlap-domination/KP combinatorial receipt consumes exact disjoint decorrelation from UltrametricClusterSeparationReceipt and records overlapping plaquette domination as finite carrier tail bookkeeping.  It is not a Clay/YM continuum promotion."

record OverlapDominationLemmaReceipt : Setω where
  field
    status :
      OverlapDominationStatus

    statusIsCanonical :
      status
      ≡
      finiteCarrierOverlapDominationKPBookkeepingRecorded

    ultrametricClusterReceipt :
      Ultra.UltrametricClusterSeparationReceipt

    exactDisjointDecorrelationInput :
      Ultra.exactDecorrelationFunction ultrametricClusterReceipt
      ≡
      Ultra.exactDecorrelation

    disjointWitnessInput :
      Ultra.p2p3P5p7DisjointSupportWitness ultrametricClusterReceipt
      ≡
      Ultra.p2p3DisjointFromP5p7

    concreteDisjointFactorisationConsumed :
      (k : Nat) →
      Ultra.carrierCovarianceZero
        Ultra.p2p3Plaquette
        Ultra.p5p7Plaquette
        k
      ≡
      true

    concreteDisjointFactorisationConsumedIsUltrametric :
      concreteDisjointFactorisationConsumed
      ≡
      Ultra.p2p3P5p7ExactDecorrelation

    disjointDecorrelationConsumedExactly :
      Bool

    disjointDecorrelationConsumedExactlyIsTrue :
      disjointDecorrelationConsumedExactly ≡ true

    disjointDecorrelationReprovedAnalytically :
      Bool

    disjointDecorrelationReprovedAnalyticallyIsFalse :
      disjointDecorrelationReprovedAnalytically ≡ false

    overlapTailStatus :
      OverlapTailStatus

    overlapTailStatusIsFiniteCarrier :
      overlapTailStatus
      ≡
      overlappingPlaquettesBoundedByFiniteGeometricTailCarrierCode

    overlapTailCode :
      FiniteGeometricTailCode

    overlapTailCodeIsCanonical :
      overlapTailCode ≡ canonicalOverlapTailCode

    betaMinBookkeepingNumerator :
      Nat

    betaMinBookkeepingNumeratorIsUltrametric :
      betaMinBookkeepingNumerator
      ≡
      Ultra.betaMinNumerator

    betaMinBookkeepingDenominator :
      Nat

    betaMinBookkeepingDenominatorIsUltrametric :
      betaMinBookkeepingDenominator
      ≡
      Ultra.betaMinDenominator

    positiveOverlapTailRecorded :
      Bool

    positiveOverlapTailRecordedIsTrue :
      positiveOverlapTailRecorded ≡ true

    positiveOverlapTailIsAnalyticContinuumProof :
      Bool

    positiveOverlapTailIsAnalyticContinuumProofIsFalse :
      positiveOverlapTailIsAnalyticContinuumProof ≡ false

    gate3NormDictionary :
      Gate3.Gate3NormDictionaryReceipt

    finiteCarrierLimit71Surface :
      Gate3.Gate3NormDictionaryReceipt.boundedModelStatus
        gate3NormDictionary
      ≡
      Gate3.finiteBoundedModelLimit71InequalitySurface_only

    finiteCarrierSSPSet :
      Gate3.Gate3NormDictionaryReceipt.finitePrimeSet
        gate3NormDictionary
      ≡
      Gate3.finiteSSP

    polymerKPReceipt :
      KP.PolymerKPAsMDLReceipt

    polymerKPBookkeepingAvailable :
      KP.mdLFejerBookkeepingAvailable polymerKPReceipt ≡ true

    polymerKPConditionStillFalse :
      KP.koteckyPreissConditionProved polymerKPReceipt ≡ false

    polymerUniformVolumeStillFalse :
      KP.uniformVolumeKPBoundProved polymerKPReceipt ≡ false

    areaLawBalabanSeedReceipt :
      Area.CarrierAreaLawBalabanSeedReceipt

    carrierAreaLawStillFalse :
      Area.carrierAreaLawProved areaLawBalabanSeedReceipt ≡ false

    balabanRGStillFalseFromAreaReceipt :
      Area.balabanRGConvergenceProved areaLawBalabanSeedReceipt ≡ false

    kpUniformityStatus :
      KPUniformityStatus

    kpUniformityStatusIsFiniteCarrier :
      kpUniformityStatus
      ≡
      kpUniformityRecordedAsFiniteCarrierSurfaceOnly

    kpUniformityFiniteCarrierRecorded :
      Bool

    kpUniformityFiniteCarrierRecordedIsTrue :
      kpUniformityFiniteCarrierRecorded ≡ true

    kpUniformityPromotedToContinuum :
      Bool

    kpUniformityPromotedToContinuumIsFalse :
      kpUniformityPromotedToContinuum ≡ false

    continuumKPProved :
      Bool

    continuumKPProvedIsFalse :
      continuumKPProved ≡ false

    infiniteVolumePolymerExpansionProved :
      Bool

    infiniteVolumePolymerExpansionProvedIsFalse :
      infiniteVolumePolymerExpansionProved ≡ false

    balabanRGConvergenceProved :
      Bool

    balabanRGConvergenceProvedIsFalse :
      balabanRGConvergenceProved ≡ false

    carrierAreaLawTheoremProved :
      Bool

    carrierAreaLawTheoremProvedIsFalse :
      carrierAreaLawTheoremProved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    inputs :
      List OverlapDominationInput

    inputsAreCanonical :
      inputs ≡ canonicalOverlapDominationInputs

    nonClaims :
      List OverlapDominationNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalOverlapDominationNonClaims

    promotionFlags :
      List OverlapDominationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    overlapTailReading :
      String

    overlapTailReadingIsCanonical :
      overlapTailReading ≡ overlapTailStatement

    kpUniformityReading :
      String

    kpUniformityReadingIsCanonical :
      kpUniformityReading ≡ kpUniformityStatement

    statement :
      String

    statementIsCanonical :
      statement ≡ overlapDominationStatement

    receiptBoundary :
      List String

open OverlapDominationLemmaReceipt public

canonicalOverlapDominationLemmaReceipt :
  OverlapDominationLemmaReceipt
canonicalOverlapDominationLemmaReceipt =
  record
    { status =
        finiteCarrierOverlapDominationKPBookkeepingRecorded
    ; statusIsCanonical =
        refl
    ; ultrametricClusterReceipt =
        Ultra.canonicalUltrametricClusterSeparationReceipt
    ; exactDisjointDecorrelationInput =
        refl
    ; disjointWitnessInput =
        refl
    ; concreteDisjointFactorisationConsumed =
        Ultra.p2p3P5p7ExactDecorrelation
    ; concreteDisjointFactorisationConsumedIsUltrametric =
        refl
    ; disjointDecorrelationConsumedExactly =
        true
    ; disjointDecorrelationConsumedExactlyIsTrue =
        refl
    ; disjointDecorrelationReprovedAnalytically =
        false
    ; disjointDecorrelationReprovedAnalyticallyIsFalse =
        refl
    ; overlapTailStatus =
        overlappingPlaquettesBoundedByFiniteGeometricTailCarrierCode
    ; overlapTailStatusIsFiniteCarrier =
        refl
    ; overlapTailCode =
        canonicalOverlapTailCode
    ; overlapTailCodeIsCanonical =
        refl
    ; betaMinBookkeepingNumerator =
        Ultra.betaMinNumerator
    ; betaMinBookkeepingNumeratorIsUltrametric =
        refl
    ; betaMinBookkeepingDenominator =
        Ultra.betaMinDenominator
    ; betaMinBookkeepingDenominatorIsUltrametric =
        refl
    ; positiveOverlapTailRecorded =
        true
    ; positiveOverlapTailRecordedIsTrue =
        refl
    ; positiveOverlapTailIsAnalyticContinuumProof =
        false
    ; positiveOverlapTailIsAnalyticContinuumProofIsFalse =
        refl
    ; gate3NormDictionary =
        Gate3.canonicalGate3NormDictionaryReceipt
    ; finiteCarrierLimit71Surface =
        refl
    ; finiteCarrierSSPSet =
        refl
    ; polymerKPReceipt =
        KP.canonicalPolymerKPAsMDLReceipt
    ; polymerKPBookkeepingAvailable =
        refl
    ; polymerKPConditionStillFalse =
        refl
    ; polymerUniformVolumeStillFalse =
        refl
    ; areaLawBalabanSeedReceipt =
        Area.canonicalCarrierAreaLawBalabanSeedReceipt
    ; carrierAreaLawStillFalse =
        refl
    ; balabanRGStillFalseFromAreaReceipt =
        refl
    ; kpUniformityStatus =
        kpUniformityRecordedAsFiniteCarrierSurfaceOnly
    ; kpUniformityStatusIsFiniteCarrier =
        refl
    ; kpUniformityFiniteCarrierRecorded =
        true
    ; kpUniformityFiniteCarrierRecordedIsTrue =
        refl
    ; kpUniformityPromotedToContinuum =
        false
    ; kpUniformityPromotedToContinuumIsFalse =
        refl
    ; continuumKPProved =
        false
    ; continuumKPProvedIsFalse =
        refl
    ; infiniteVolumePolymerExpansionProved =
        false
    ; infiniteVolumePolymerExpansionProvedIsFalse =
        refl
    ; balabanRGConvergenceProved =
        false
    ; balabanRGConvergenceProvedIsFalse =
        refl
    ; carrierAreaLawTheoremProved =
        false
    ; carrierAreaLawTheoremProvedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; inputs =
        canonicalOverlapDominationInputs
    ; inputsAreCanonical =
        refl
    ; nonClaims =
        canonicalOverlapDominationNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; overlapTailReading =
        overlapTailStatement
    ; overlapTailReadingIsCanonical =
        refl
    ; kpUniformityReading =
        kpUniformityStatement
    ; kpUniformityReadingIsCanonical =
        refl
    ; statement =
        overlapDominationStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Consumes exact disjoint decorrelation from UltrametricClusterSeparationReceipt.exactDecorrelationFunction"
        ∷ "Consumes the concrete p2,p3 versus p5,p7 disjoint-support factorisation witness from the ultrametric cluster receipt"
        ∷ "Routes overlapping plaquettes to a finite/geometric-tail carrier code with beta_min bookkeeping from the ultrametric receipt"
        ∷ "Records positive overlap-tail status as finite carrier bookkeeping only, not as an analytic continuum proof"
        ∷ "Records KP uniformity as a finite Gate3 limit71/SSP and PolymerKPAsMDL bookkeeping surface"
        ∷ "Does not prove continuum KP or an infinite-volume polymer expansion"
        ∷ "Does not prove the carrier area-law theorem or Balaban RG convergence"
        ∷ "Keeps Clay Yang-Mills and terminal Clay promotion flags false"
        ∷ []
    }

overlapDominationKeepsContinuumKPFalse :
  continuumKPProved canonicalOverlapDominationLemmaReceipt ≡ false
overlapDominationKeepsContinuumKPFalse =
  refl

overlapDominationKeepsClayFalse :
  clayYangMillsPromoted canonicalOverlapDominationLemmaReceipt ≡ false
overlapDominationKeepsClayFalse =
  refl
