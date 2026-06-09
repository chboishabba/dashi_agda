module DASHI.Physics.Closure.KPUniformVolumeBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import MonsterOntos using
  ( SSP
  ; p2
  )

import DASHI.Physics.Closure.CarrierBalabanInductiveStepReceipt as Balaban
import DASHI.Physics.Closure.BruhatTitsCarrierGaugeFixingReceipt as BT
import DASHI.Physics.Closure.OverlapDominationLemmaReceipt as Overlap
import DASHI.Physics.Closure.PolymerKPAsMDLReceipt as KP
import DASHI.Physics.Closure.UltrametricClusterSeparationReceipt as Ultra

------------------------------------------------------------------------
-- KP uniform-volume carrier-side receipt.
--
-- This is a finite-carrier bookkeeping theorem receipt.  It records the
-- corrected carrier-side shape for the KP/Balaban overlap bound:
--
-- * the naive independent geometric expansion over all 15 SSP primes is
--   explicitly marked as an overcount/failure mode;
-- * activity is not treated as multiplicative across unions, even for
--   disjoint prime support; the resulting cross term is recorded as
--   an explicit finite-carrier obligation;
-- * exact ultrametric decorrelation is not promoted here as a KP proof;
--   the receipt records only the support-level obligation shape;
-- * Bruhat-Tits branching/valency data are referenced through the separate
--   carrier gauge-fixing receipt, not converted into a KP numeric bound;
-- * the remaining effective overlap object is routed to same-prime,
--   single-prime polymer bookkeeping;
-- * the bounded object is a symbolic single-prime geometric carrier tail.
--
-- No continuum KP theorem, no Balaban RG convergence theorem, no infinite
-- volume polymer expansion, and no Clay Yang-Mills promotion are claimed.

data KPUniformVolumeCarrierStatus : Set where
  finiteCarrierSinglePrimeKPBoundTargetRecorded :
    KPUniformVolumeCarrierStatus

data NaiveFifteenPrimeExpansionVerdict : Set where
  naive15PrimeIndependentGeometricExpansionOvercounts :
    NaiveFifteenPrimeExpansionVerdict

data ActivityFactorisationVerdict : Set where
  activityUnionIsNotMultiplicativeCrossTermExists :
    ActivityFactorisationVerdict

data NaiveActivityFactorisationVerdict : Set where
  naiveActivityFactorisationRejected :
    NaiveActivityFactorisationVerdict

data CrossTermBoundStatus : Set where
  crossTermBoundObligationRecorded :
    CrossTermBoundStatus

data BranchingObstructionStatus : Set where
  bruhatTitsBranchingObstructionReferencedSeparately :
    BranchingObstructionStatus

data PlaquetteSupportReduction : Set where
  disjointPrimeSupportImpliesDisjointPlaquettes :
    PlaquetteSupportReduction

data KPOverlapReductionStatus : Set where
  kpOverlapReducesToSamePrime :
    KPOverlapReductionStatus

data UltrametricReductionStep : Set where
  recordDisjointPrimeSupportObligation :
    UltrametricReductionStep

  rejectNaiveActivityMultiplicativity :
    UltrametricReductionStep

  recordActivityCrossTermObligation :
    UltrametricReductionStep

  referenceBTBranchingObstructionSeparately :
    UltrametricReductionStep

  reduceDisjointPrimeSupportToDisjointPlaquettes :
    UltrametricReductionStep

  excludeCrossPrimeDisconnectedPairsFromKPOverlapSet :
    UltrametricReductionStep

  retainOnlySamePrimeOverlapPolymers :
    UltrametricReductionStep

  routeRetainedTailToSinglePrimeGeometricCode :
    UltrametricReductionStep

canonicalUltrametricReductionSteps :
  List UltrametricReductionStep
canonicalUltrametricReductionSteps =
  recordDisjointPrimeSupportObligation
  ∷ rejectNaiveActivityMultiplicativity
  ∷ recordActivityCrossTermObligation
  ∷ referenceBTBranchingObstructionSeparately
  ∷ reduceDisjointPrimeSupportToDisjointPlaquettes
  ∷ excludeCrossPrimeDisconnectedPairsFromKPOverlapSet
  ∷ retainOnlySamePrimeOverlapPolymers
  ∷ routeRetainedTailToSinglePrimeGeometricCode
  ∷ []

data EffectiveOverlapClass : Set where
  samePrimeSinglePrimePolymer :
    EffectiveOverlapClass

data CarrierBoundedObject : Set where
  singlePrimeGeometricConvergenceCarrierTail :
    CarrierBoundedObject

data KPBalabanCarrierNonClaim : Set where
  noNaiveFifteenPrimeProductBound :
    KPBalabanCarrierNonClaim

  noContinuumKPTheorem :
    KPBalabanCarrierNonClaim

  noInfiniteVolumePolymerExpansion :
    KPBalabanCarrierNonClaim

  noBalabanRGConvergenceTheorem :
    KPBalabanCarrierNonClaim

  noContinuumEuclideanYangMillsConstruction :
    KPBalabanCarrierNonClaim

  noClayYangMillsPromotion :
    KPBalabanCarrierNonClaim

canonicalKPBalabanCarrierNonClaims :
  List KPBalabanCarrierNonClaim
canonicalKPBalabanCarrierNonClaims =
  noNaiveFifteenPrimeProductBound
  ∷ noContinuumKPTheorem
  ∷ noInfiniteVolumePolymerExpansion
  ∷ noBalabanRGConvergenceTheorem
  ∷ noContinuumEuclideanYangMillsConstruction
  ∷ noClayYangMillsPromotion
  ∷ []

data KPUniformVolumeCarrierPromotion : Set where

kpUniformVolumeCarrierPromotionImpossibleHere :
  KPUniformVolumeCarrierPromotion →
  ⊥
kpUniformVolumeCarrierPromotionImpossibleHere ()

sspPrimeCount :
  Nat
sspPrimeCount =
  15

naiveGeometricFactorCount :
  Nat
naiveGeometricFactorCount =
  15

effectiveGeometricFactorCount :
  Nat
effectiveGeometricFactorCount =
  1

singlePrimeWitness :
  SSP
singlePrimeWitness =
  p2

singlePrimeRatioNumerator :
  Nat
singlePrimeRatioNumerator =
  1

singlePrimeRatioDenominator :
  Nat
singlePrimeRatioDenominator =
  3

singlePrimeTailNumerator :
  Nat
singlePrimeTailNumerator =
  3

singlePrimeTailDenominator :
  Nat
singlePrimeTailDenominator =
  2

naiveExpansionFailureStatement : String
naiveExpansionFailureStatement =
  "The naive product of 15 independent prime-lane geometric tails is recorded as an overcount and the naive activity factorisation z(G union G') = z(G)z(G') is rejected: activity is not multiplicative in this receipt, because a finite carrier cross term remains an explicit obligation."

ultrametricReductionStatement : String
ultrametricReductionStatement =
  "The KP reduction is recorded as a support-level obligation: disjoint prime support should imply disjoint plaquette support, so cross-prime disconnected pairs are excluded from the KP overlap set rather than removed by activity factorisation."

singlePrimeBoundStatement : String
singlePrimeBoundStatement =
  "The carrier-side bounded object is the symbolic single-prime geometric tail with ratio 1/3 and formal sum 3/2; Bruhat-Tits branching data are a separate receipt-level obstruction, not an analytic continuum KP proof."

record SinglePrimeGeometricTailCode : Set where
  constructor singlePrimeTail
  field
    prime :
      SSP

    ratioNumerator :
      Nat

    ratioDenominator :
      Nat

    tailNumerator :
      Nat

    tailDenominator :
      Nat

    convergenceRecorded :
      Bool

open SinglePrimeGeometricTailCode public

canonicalSinglePrimeTailCode :
  SinglePrimeGeometricTailCode
canonicalSinglePrimeTailCode =
  singlePrimeTail
    singlePrimeWitness
    singlePrimeRatioNumerator
    singlePrimeRatioDenominator
    singlePrimeTailNumerator
    singlePrimeTailDenominator
    true

record KPUniformVolumeBoundReceipt : Setω where
  field
    status :
      KPUniformVolumeCarrierStatus

    statusIsCanonical :
      status ≡ finiteCarrierSinglePrimeKPBoundTargetRecorded

    polymerKPReceipt :
      KP.PolymerKPAsMDLReceipt

    polymerKPBookkeepingAvailable :
      KP.mdLFejerBookkeepingAvailable polymerKPReceipt ≡ true

    polymerKPContinuumConditionStillFalse :
      KP.koteckyPreissConditionProved polymerKPReceipt ≡ false

    polymerKPUniformVolumeStillFalse :
      KP.uniformVolumeKPBoundProved polymerKPReceipt ≡ false

    ultrametricClusterReceipt :
      Ultra.UltrametricClusterSeparationReceipt

    exactDecorrelationConsumedAsKPProof :
      Bool

    exactDecorrelationConsumedAsKPProofIsFalse :
      exactDecorrelationConsumedAsKPProof ≡ false

    concreteDisjointWitnessRecorded :
      Ultra.p2p3P5p7DisjointSupportWitness ultrametricClusterReceipt
      ≡
      Ultra.p2p3DisjointFromP5p7

    concreteDisjointCovarianceWitness :
      (k : Nat) →
      Ultra.carrierCovarianceZero
        Ultra.p2p3Plaquette
        Ultra.p5p7Plaquette
        k
      ≡
      true

    concreteDisjointCovarianceWitnessIsUltrametric :
      concreteDisjointCovarianceWitness
      ≡
      Ultra.p2p3P5p7ExactDecorrelation

    overlapDominationReceipt :
      Overlap.OverlapDominationLemmaReceipt

    overlapTailIsFiniteCarrier :
      Overlap.positiveOverlapTailRecorded overlapDominationReceipt ≡ true

    overlapContinuumKPStillFalse :
      Overlap.continuumKPProved overlapDominationReceipt ≡ false

    balabanInductiveStepReceipt :
      Balaban.CarrierBalabanInductiveStepReceipt

    balabanConsumesOverlapDomination :
      Balaban.overlapDominationKPFiniteCarrierRecorded
        balabanInductiveStepReceipt
      ≡
      true

    balabanRGConvergenceStillFalse :
      Balaban.continuumRGConvergencePromoted balabanInductiveStepReceipt
      ≡
      false

    naiveVerdict :
      NaiveFifteenPrimeExpansionVerdict

    naiveVerdictIsOvercount :
      naiveVerdict ≡ naive15PrimeIndependentGeometricExpansionOvercounts

    naive15PrimeExpansionAccepted :
      Bool

    naive15PrimeExpansionAcceptedIsFalse :
      naive15PrimeExpansionAccepted ≡ false

    naiveActivityFactorisationVerdict :
      NaiveActivityFactorisationVerdict

    naiveActivityFactorisationVerdictIsRejected :
      naiveActivityFactorisationVerdict
      ≡
      naiveActivityFactorisationRejected

    naiveActivityFactorisationAccepted :
      Bool

    naiveActivityFactorisationAcceptedIsFalse :
      naiveActivityFactorisationAccepted ≡ false

    activityNotMultiplicative :
      ActivityFactorisationVerdict

    activityNotMultiplicativeIsCanonical :
      activityNotMultiplicative
      ≡
      activityUnionIsNotMultiplicativeCrossTermExists

    crossTermExists :
      Bool

    crossTermExistsIsTrue :
      crossTermExists ≡ true

    crossTermBoundStatus :
      CrossTermBoundStatus

    crossTermBoundStatusIsRecorded :
      crossTermBoundStatus ≡ crossTermBoundObligationRecorded

    bruhatTitsCarrierReceipt :
      BT.BruhatTitsCarrierGaugeFixingReceipt

    bruhatTitsBranchingObstructionStatus :
      BranchingObstructionStatus

    bruhatTitsBranchingObstructionIsSeparate :
      bruhatTitsBranchingObstructionStatus
      ≡
      bruhatTitsBranchingObstructionReferencedSeparately

    bruhatTitsValenciesRecordedSeparately :
      BT.primeLaneValencies bruhatTitsCarrierReceipt
      ≡
      BT.canonicalSSPPrimeLaneValencies

    bruhatTitsKPPromotionStillFalse :
      BT.kpTheoremPromoted bruhatTitsCarrierReceipt ≡ false

    exactUltrametricReductionPromoted :
      Bool

    exactUltrametricReductionPromotedIsFalse :
      exactUltrametricReductionPromoted ≡ false

    disjointPrimeSupportImpliesDisjointPlaquettesStatus :
      PlaquetteSupportReduction

    disjointPrimeSupportImpliesDisjointPlaquettesStatusIsCanonical :
      disjointPrimeSupportImpliesDisjointPlaquettesStatus
      ≡
      disjointPrimeSupportImpliesDisjointPlaquettes

    kpOverlapReductionStatus :
      KPOverlapReductionStatus

    kpOverlapReductionStatusIsSamePrime :
      kpOverlapReductionStatus ≡ kpOverlapReducesToSamePrime

    effectiveOverlapClass :
      EffectiveOverlapClass

    effectiveOverlapClassIsSinglePrime :
      effectiveOverlapClass ≡ samePrimeSinglePrimePolymer

    boundedObject :
      CarrierBoundedObject

    boundedObjectIsSinglePrimeTail :
      boundedObject ≡ singlePrimeGeometricConvergenceCarrierTail

    sspPrimeCountRecorded :
      Nat

    sspPrimeCountRecordedIsCanonical :
      sspPrimeCountRecorded ≡ sspPrimeCount

    naiveGeometricFactorCountRecorded :
      Nat

    naiveGeometricFactorCountRecordedIsCanonical :
      naiveGeometricFactorCountRecorded ≡ naiveGeometricFactorCount

    effectiveGeometricFactorCountRecorded :
      Nat

    effectiveGeometricFactorCountRecordedIsCanonical :
      effectiveGeometricFactorCountRecorded ≡ effectiveGeometricFactorCount

    singlePrimeTailCode :
      SinglePrimeGeometricTailCode

    singlePrimeTailCodeIsCanonical :
      singlePrimeTailCode ≡ canonicalSinglePrimeTailCode

    singlePrimeConvergenceRecorded :
      convergenceRecorded singlePrimeTailCode ≡ true

    carrierSideBoundedObjectRecorded :
      Bool

    carrierSideBoundedObjectRecordedIsTrue :
      carrierSideBoundedObjectRecorded ≡ true

    continuumKPProved :
      Bool

    continuumKPProvedIsFalse :
      continuumKPProved ≡ false

    infiniteVolumePolymerExpansionProved :
      Bool

    infiniteVolumePolymerExpansionProvedIsFalse :
      infiniteVolumePolymerExpansionProved ≡ false

    continuumBalabanTheoremProved :
      Bool

    continuumBalabanTheoremProvedIsFalse :
      continuumBalabanTheoremProved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    reductionSteps :
      List UltrametricReductionStep

    reductionStepsAreCanonical :
      reductionSteps ≡ canonicalUltrametricReductionSteps

    nonClaims :
      List KPBalabanCarrierNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalKPBalabanCarrierNonClaims

    promotionFlags :
      List KPUniformVolumeCarrierPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    naiveExpansionReading :
      String

    naiveExpansionReadingIsCanonical :
      naiveExpansionReading ≡ naiveExpansionFailureStatement

    ultrametricReductionReading :
      String

    ultrametricReductionReadingIsCanonical :
      ultrametricReductionReading ≡ ultrametricReductionStatement

    singlePrimeBoundReading :
      String

    singlePrimeBoundReadingIsCanonical :
      singlePrimeBoundReading ≡ singlePrimeBoundStatement

    receiptBoundary :
      List String

open KPUniformVolumeBoundReceipt public

canonicalKPUniformVolumeBoundReceipt :
  KPUniformVolumeBoundReceipt
canonicalKPUniformVolumeBoundReceipt =
  record
    { status =
        finiteCarrierSinglePrimeKPBoundTargetRecorded
    ; statusIsCanonical =
        refl
    ; polymerKPReceipt =
        KP.canonicalPolymerKPAsMDLReceipt
    ; polymerKPBookkeepingAvailable =
        refl
    ; polymerKPContinuumConditionStillFalse =
        refl
    ; polymerKPUniformVolumeStillFalse =
        refl
    ; ultrametricClusterReceipt =
        Ultra.canonicalUltrametricClusterSeparationReceipt
    ; exactDecorrelationConsumedAsKPProof =
        false
    ; exactDecorrelationConsumedAsKPProofIsFalse =
        refl
    ; concreteDisjointWitnessRecorded =
        refl
    ; concreteDisjointCovarianceWitness =
        Ultra.p2p3P5p7ExactDecorrelation
    ; concreteDisjointCovarianceWitnessIsUltrametric =
        refl
    ; overlapDominationReceipt =
        Overlap.canonicalOverlapDominationLemmaReceipt
    ; overlapTailIsFiniteCarrier =
        refl
    ; overlapContinuumKPStillFalse =
        refl
    ; balabanInductiveStepReceipt =
        Balaban.canonicalCarrierBalabanInductiveStepReceipt
    ; balabanConsumesOverlapDomination =
        refl
    ; balabanRGConvergenceStillFalse =
        refl
    ; naiveVerdict =
        naive15PrimeIndependentGeometricExpansionOvercounts
    ; naiveVerdictIsOvercount =
        refl
    ; naive15PrimeExpansionAccepted =
        false
    ; naive15PrimeExpansionAcceptedIsFalse =
        refl
    ; naiveActivityFactorisationVerdict =
        naiveActivityFactorisationRejected
    ; naiveActivityFactorisationVerdictIsRejected =
        refl
    ; naiveActivityFactorisationAccepted =
        false
    ; naiveActivityFactorisationAcceptedIsFalse =
        refl
    ; activityNotMultiplicative =
        activityUnionIsNotMultiplicativeCrossTermExists
    ; activityNotMultiplicativeIsCanonical =
        refl
    ; crossTermExists =
        true
    ; crossTermExistsIsTrue =
        refl
    ; crossTermBoundStatus =
        crossTermBoundObligationRecorded
    ; crossTermBoundStatusIsRecorded =
        refl
    ; bruhatTitsCarrierReceipt =
        BT.canonicalBruhatTitsCarrierGaugeFixingReceipt
    ; bruhatTitsBranchingObstructionStatus =
        bruhatTitsBranchingObstructionReferencedSeparately
    ; bruhatTitsBranchingObstructionIsSeparate =
        refl
    ; bruhatTitsValenciesRecordedSeparately =
        refl
    ; bruhatTitsKPPromotionStillFalse =
        refl
    ; exactUltrametricReductionPromoted =
        false
    ; exactUltrametricReductionPromotedIsFalse =
        refl
    ; disjointPrimeSupportImpliesDisjointPlaquettesStatus =
        disjointPrimeSupportImpliesDisjointPlaquettes
    ; disjointPrimeSupportImpliesDisjointPlaquettesStatusIsCanonical =
        refl
    ; kpOverlapReductionStatus =
        kpOverlapReducesToSamePrime
    ; kpOverlapReductionStatusIsSamePrime =
        refl
    ; effectiveOverlapClass =
        samePrimeSinglePrimePolymer
    ; effectiveOverlapClassIsSinglePrime =
        refl
    ; boundedObject =
        singlePrimeGeometricConvergenceCarrierTail
    ; boundedObjectIsSinglePrimeTail =
        refl
    ; sspPrimeCountRecorded =
        sspPrimeCount
    ; sspPrimeCountRecordedIsCanonical =
        refl
    ; naiveGeometricFactorCountRecorded =
        naiveGeometricFactorCount
    ; naiveGeometricFactorCountRecordedIsCanonical =
        refl
    ; effectiveGeometricFactorCountRecorded =
        effectiveGeometricFactorCount
    ; effectiveGeometricFactorCountRecordedIsCanonical =
        refl
    ; singlePrimeTailCode =
        canonicalSinglePrimeTailCode
    ; singlePrimeTailCodeIsCanonical =
        refl
    ; singlePrimeConvergenceRecorded =
        refl
    ; carrierSideBoundedObjectRecorded =
        true
    ; carrierSideBoundedObjectRecordedIsTrue =
        refl
    ; continuumKPProved =
        false
    ; continuumKPProvedIsFalse =
        refl
    ; infiniteVolumePolymerExpansionProved =
        false
    ; infiniteVolumePolymerExpansionProvedIsFalse =
        refl
    ; continuumBalabanTheoremProved =
        false
    ; continuumBalabanTheoremProvedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; reductionSteps =
        canonicalUltrametricReductionSteps
    ; reductionStepsAreCanonical =
        refl
    ; nonClaims =
        canonicalKPBalabanCarrierNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; naiveExpansionReading =
        naiveExpansionFailureStatement
    ; naiveExpansionReadingIsCanonical =
        refl
    ; ultrametricReductionReading =
        ultrametricReductionStatement
    ; ultrametricReductionReadingIsCanonical =
        refl
    ; singlePrimeBoundReading =
        singlePrimeBoundStatement
    ; singlePrimeBoundReadingIsCanonical =
        refl
    ; receiptBoundary =
        "Rejects the naive 15-prime product/geometric expansion as an overcount"
        ∷ "Rejects naive activity factorisation: z(G union G') is not recorded as z(G)z(G') even for disjoint prime support"
        ∷ "Records an activity cross term as an explicit finite carrier obligation, not a multiplicative factorisation"
        ∷ "References Bruhat-Tits branching/valency data through the separate carrier gauge-fixing receipt"
        ∷ "Does not consume exact ultrametric decorrelation as a KP proof"
        ∷ "Records disjoint prime support as yielding disjoint plaquette support for this finite carrier surface"
        ∷ "Excludes cross-prime disconnected pairs from the KP overlap set rather than removing them by activity factorisation"
        ∷ "Records KP overlap reduction to the same-prime case for single-prime Gamma"
        ∷ "Records the single-prime geometric tail ratio 1/3 and sum 3/2 as symbolic carrier witnesses"
        ∷ "Records the carrier-side bounded object without claiming continuum KP, Balaban RG convergence, infinite volume, or Clay Yang-Mills"
        ∷ []
    }

kpUniformVolumeBoundRejectsNaive15PrimeProduct :
  naive15PrimeExpansionAccepted canonicalKPUniformVolumeBoundReceipt ≡ false
kpUniformVolumeBoundRejectsNaive15PrimeProduct =
  refl

kpUniformVolumeBoundKeepsClayFalse :
  clayYangMillsPromoted canonicalKPUniformVolumeBoundReceipt ≡ false
kpUniformVolumeBoundKeepsClayFalse =
  refl

kpUniformVolumeBoundCarrierObjectIsSinglePrime :
  boundedObject canonicalKPUniformVolumeBoundReceipt
  ≡
  singlePrimeGeometricConvergenceCarrierTail
kpUniformVolumeBoundCarrierObjectIsSinglePrime =
  refl

kpUniformVolumeBoundRejectsNaiveActivityFactorisation :
  naiveActivityFactorisationAccepted canonicalKPUniformVolumeBoundReceipt
  ≡
  false
kpUniformVolumeBoundRejectsNaiveActivityFactorisation =
  refl

kpUniformVolumeBoundRecordsCrossTerm :
  crossTermExists canonicalKPUniformVolumeBoundReceipt ≡ true
kpUniformVolumeBoundRecordsCrossTerm =
  refl

kpUniformVolumeBoundReducesOverlapToSamePrime :
  kpOverlapReductionStatus canonicalKPUniformVolumeBoundReceipt
  ≡
  kpOverlapReducesToSamePrime
kpUniformVolumeBoundReducesOverlapToSamePrime =
  refl
