module DASHI.Physics.Closure.UltrametricClusterSeparationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Nullary.Decidable.Core using (yes; no)

open import MonsterOntos using
  ( SSP
  ; _≟_
  ; p2
  ; p3
  ; p5
  ; p7
  ; p11
  ; p13
  ; p17
  ; p19
  ; p23
  ; p29
  ; p31
  ; p41
  ; p47
  ; p59
  ; p71
  )
import DASHI.Physics.Closure.CarrierOS3ReflectionPositivityReceipt as OS3
import DASHI.Physics.Closure.CheckerboardUltrametricBridgeReceipt as Checker
import DASHI.Physics.Closure.Gate3NormDictionary as Gate3
import DASHI.Physics.Closure.PolymerKPAsMDLReceipt as KP

------------------------------------------------------------------------
-- Ultrametric cluster-separation receipt.
--
-- This is a finite-carrier receipt.  It records the SSP plaquette
-- factorisation surface and the associated Kotecky-Preiss/Euler-product
-- constants requested by the polymer programme.  It does not prove the
-- analytic infinite-volume polymer expansion, continuum OS reconstruction,
-- or a Clay Yang-Mills theorem.

record SSPPlaquette : Set where
  constructor plaquette
  field
    firstPrime :
      SSP

    secondPrime :
      SSP

open SSPPlaquette public

data UltrametricClusterSeparationStatus : Set where
  finiteCarrierExactDecorrelationSurfaceRecorded :
    UltrametricClusterSeparationStatus

data UltrametricClusterInput : Set where
  agreementUltrametricStrongTriangle :
    UltrametricClusterInput

  finiteSSPPrimeLaneFactorisation :
    UltrametricClusterInput

  carrierOS3ReflectionPositivity :
    UltrametricClusterInput

  checkerboardUltrametricBridge :
    UltrametricClusterInput

  gate3BoundedModelLimit71 :
    UltrametricClusterInput

  polymerKPAsMDLBookkeeping :
    UltrametricClusterInput

canonicalUltrametricClusterInputs :
  List UltrametricClusterInput
canonicalUltrametricClusterInputs =
  agreementUltrametricStrongTriangle
  ∷ finiteSSPPrimeLaneFactorisation
  ∷ carrierOS3ReflectionPositivity
  ∷ checkerboardUltrametricBridge
  ∷ gate3BoundedModelLimit71
  ∷ polymerKPAsMDLBookkeeping
  ∷ []

data CarrierDecorrelationVerdict : Set where
  conditionalExactZeroByDisjointPrimeSupports_finiteCarrier :
    CarrierDecorrelationVerdict

data KoteckyPreissCarrierVerdict : Set where
  finiteSSPEulerBoundSurface_betaMinApprox033 :
    KoteckyPreissCarrierVerdict

data UltrametricClusterPromotion : Set where

ultrametricClusterPromotionImpossibleHere :
  UltrametricClusterPromotion →
  ⊥
ultrametricClusterPromotionImpossibleHere ()

finiteSSP :
  List SSP
finiteSSP =
  p2
  ∷ p3
  ∷ p5
  ∷ p7
  ∷ p11
  ∷ p13
  ∷ p17
  ∷ p19
  ∷ p23
  ∷ p29
  ∷ p31
  ∷ p41
  ∷ p47
  ∷ p59
  ∷ p71
  ∷ []

andBool :
  Bool →
  Bool →
  Bool
andBool true true =
  true
andBool _ _ =
  false

notSameSSPBool :
  SSP →
  SSP →
  Bool
notSameSSPBool p q with p ≟ q
... | yes _ =
  false
... | no _ =
  true

record DisjointPrimeSupports
  (p q : SSPPlaquette) :
  Set where
  field
    firstFirstDisjoint :
      notSameSSPBool (firstPrime p) (firstPrime q) ≡ true

    firstSecondDisjoint :
      notSameSSPBool (firstPrime p) (secondPrime q) ≡ true

    secondFirstDisjoint :
      notSameSSPBool (secondPrime p) (firstPrime q) ≡ true

    secondSecondDisjoint :
      notSameSSPBool (secondPrime p) (secondPrime q) ≡ true

open DisjointPrimeSupports public

disjointPrimeSupportsBool :
  SSPPlaquette →
  SSPPlaquette →
  Bool
disjointPrimeSupportsBool p q =
  andBool
    (notSameSSPBool (firstPrime p) (firstPrime q))
    (andBool
      (notSameSSPBool (firstPrime p) (secondPrime q))
      (andBool
        (notSameSSPBool (secondPrime p) (firstPrime q))
        (notSameSSPBool (secondPrime p) (secondPrime q))))

data SeparatedBeyondDepth : SSPPlaquette → SSPPlaquette → Nat → Set where
  separatedByFinitePrimeLaneFactorisation :
    (p q : SSPPlaquette) →
    (k : Nat) →
    DisjointPrimeSupports p q →
    SeparatedBeyondDepth p q k

carrierCovarianceZero :
  SSPPlaquette →
  SSPPlaquette →
  Nat →
  Bool
carrierCovarianceZero p q _ =
  disjointPrimeSupportsBool p q

exactDecorrelation :
  (p q : SSPPlaquette) →
  (k : Nat) →
  SeparatedBeyondDepth p q k →
  carrierCovarianceZero p q k ≡ true
exactDecorrelation
  (plaquette a b)
  (plaquette c d)
  k
  (separatedByFinitePrimeLaneFactorisation
    (plaquette .a .b)
    (plaquette .c .d)
    .k
    disjoint)
  rewrite firstFirstDisjoint disjoint
        | firstSecondDisjoint disjoint
        | secondFirstDisjoint disjoint
        | secondSecondDisjoint disjoint =
  refl

p2p3Plaquette :
  SSPPlaquette
p2p3Plaquette =
  plaquette p2 p3

p5p7Plaquette :
  SSPPlaquette
p5p7Plaquette =
  plaquette p5 p7

p2p3DisjointFromP5p7 :
  DisjointPrimeSupports p2p3Plaquette p5p7Plaquette
p2p3DisjointFromP5p7 =
  record
    { firstFirstDisjoint =
        refl
    ; firstSecondDisjoint =
        refl
    ; secondFirstDisjoint =
        refl
    ; secondSecondDisjoint =
        refl
    }

p2p3SeparatedFromP5p7 :
  (k : Nat) →
  SeparatedBeyondDepth p2p3Plaquette p5p7Plaquette k
p2p3SeparatedFromP5p7 k =
  separatedByFinitePrimeLaneFactorisation
    p2p3Plaquette
    p5p7Plaquette
    k
    p2p3DisjointFromP5p7

p2p3P5p7ExactDecorrelation :
  (k : Nat) →
  carrierCovarianceZero p2p3Plaquette p5p7Plaquette k ≡ true
p2p3P5p7ExactDecorrelation k =
  exactDecorrelation
    p2p3Plaquette
    p5p7Plaquette
    k
    (p2p3SeparatedFromP5p7 k)

betaMinNumerator :
  Nat
betaMinNumerator =
  33

betaMinDenominator :
  Nat
betaMinDenominator =
  100

adelicEulerConstantApproxNumerator :
  Nat
adelicEulerConstantApproxNumerator =
  194

adelicEulerConstantApproxDenominator :
  Nat
adelicEulerConstantApproxDenominator =
  100

cMinNumerator :
  Nat
cMinNumerator =
  2

cMinDenominator :
  Nat
cMinDenominator =
  1

ultrametricClusterStatement : String
ultrametricClusterStatement =
  "Finite SSP carrier cluster separation: exact carrier covariance zero is conditional on an explicit disjoint-prime-support witness; one finite p2,p3 versus p5,p7 witness is inhabited.  The KP/Euler-product constants are recorded only as a finite carrier bound surface with beta_min approximately 0.33."

ultrametricClusterBoundary : String
ultrametricClusterBoundary =
  "The finite carrier separation surface is recorded fail-closed: unconditional exact decorrelation, continuum polymer convergence, volume-removal analysis, OS reconstruction, and Clay Yang-Mills promotion remain unproved here."

record UltrametricClusterSeparationReceipt : Setω where
  field
    status :
      UltrametricClusterSeparationStatus

    statusIsCanonical :
      status ≡ finiteCarrierExactDecorrelationSurfaceRecorded

    agreementUltrametricAvailable :
      Bool

    agreementUltrametricAvailableIsTrue :
      agreementUltrametricAvailable ≡ true

    carrierOS3Receipt :
      OS3.CarrierOS3ReflectionPositivityReceipt

    carrierOS3FiniteSurfaceAvailable :
      OS3.carrierOS3SurfaceRecorded carrierOS3Receipt ≡ true

    checkerboardBridgeReceipt :
      Checker.CheckerboardUltrametricBridgeReceipt

    checkerboardSubmultiplicativityShapeAvailable :
      Checker.checkerboardSubmultiplicativityShapeRecorded
        checkerboardBridgeReceipt
      ≡
      true

    gate3NormDictionaryReceipt :
      Gate3.Gate3NormDictionaryReceipt

    finiteSSPLimit71SurfaceAvailable :
      Gate3.Gate3NormDictionaryReceipt.boundedModelStatus
        gate3NormDictionaryReceipt
      ≡
      Gate3.finiteBoundedModelLimit71InequalitySurface_only

    polymerKPReceipt :
      KP.PolymerKPAsMDLReceipt

    polymerKPBookkeepingAvailable :
      KP.mdLFejerBookkeepingAvailable polymerKPReceipt ≡ true

    sspPrimes :
      List SSP

    sspPrimesAreCanonical :
      sspPrimes ≡ finiteSSP

    decorrelationVerdict :
      CarrierDecorrelationVerdict

    decorrelationVerdictIsCarrierFinite :
      decorrelationVerdict
      ≡
      conditionalExactZeroByDisjointPrimeSupports_finiteCarrier

    exactDecorrelationFunction :
      (p q : SSPPlaquette) →
      (k : Nat) →
      SeparatedBeyondDepth p q k →
      carrierCovarianceZero p q k ≡ true

    exactDecorrelationFunctionIsCanonical :
      exactDecorrelationFunction ≡ exactDecorrelation

    p2p3P5p7DisjointSupportWitness :
      DisjointPrimeSupports p2p3Plaquette p5p7Plaquette

    p2p3P5p7DisjointSupportWitnessIsCanonical :
      p2p3P5p7DisjointSupportWitness ≡ p2p3DisjointFromP5p7

    p2p3P5p7ExactDecorrelationFunction :
      (k : Nat) →
      carrierCovarianceZero p2p3Plaquette p5p7Plaquette k ≡ true

    p2p3P5p7ExactDecorrelationFunctionIsCanonical :
      p2p3P5p7ExactDecorrelationFunction
      ≡
      p2p3P5p7ExactDecorrelation

    finiteCarrierExactDecorrelationConditionalRecorded :
      Bool

    finiteCarrierExactDecorrelationConditionalRecordedIsTrue :
      finiteCarrierExactDecorrelationConditionalRecorded ≡ true

    unconditionalExactDecorrelationProved :
      Bool

    unconditionalExactDecorrelationProvedIsFalse :
      unconditionalExactDecorrelationProved ≡ false

    generalDisjointSupportFactorisationProved :
      Bool

    generalDisjointSupportFactorisationProvedIsFalse :
      generalDisjointSupportFactorisationProved ≡ false

    polymerActivitiesFactorForSeparatedClusters :
      Bool

    polymerActivitiesFactorForSeparatedClustersIsFalse :
      polymerActivitiesFactorForSeparatedClusters ≡ false

    kpVerdict :
      KoteckyPreissCarrierVerdict

    kpVerdictIsFiniteCarrier :
      kpVerdict ≡ finiteSSPEulerBoundSurface_betaMinApprox033

    koteckyPreissFiniteCarrierBoundRecorded :
      Bool

    koteckyPreissFiniteCarrierBoundRecordedIsTrue :
      koteckyPreissFiniteCarrierBoundRecorded ≡ true

    betaMinApproxNumerator :
      Nat

    betaMinApproxNumeratorIsCanonical :
      betaMinApproxNumerator ≡ betaMinNumerator

    betaMinApproxDenominator :
      Nat

    betaMinApproxDenominatorIsCanonical :
      betaMinApproxDenominator ≡ betaMinDenominator

    adelicEulerApproxNumerator :
      Nat

    adelicEulerApproxNumeratorIsCanonical :
      adelicEulerApproxNumerator ≡ adelicEulerConstantApproxNumerator

    adelicEulerApproxDenominator :
      Nat

    adelicEulerApproxDenominatorIsCanonical :
      adelicEulerApproxDenominator ≡ adelicEulerConstantApproxDenominator

    cMinNumeratorRecorded :
      Nat

    cMinNumeratorRecordedIsCanonical :
      cMinNumeratorRecorded ≡ cMinNumerator

    cMinDenominatorRecorded :
      Nat

    cMinDenominatorRecordedIsCanonical :
      cMinDenominatorRecorded ≡ cMinDenominator

    analyticContinuumKPProved :
      Bool

    analyticContinuumKPProvedIsFalse :
      analyticContinuumKPProved ≡ false

    uniformInfiniteVolumePolymerExpansionProved :
      Bool

    uniformInfiniteVolumePolymerExpansionProvedIsFalse :
      uniformInfiniteVolumePolymerExpansionProved ≡ false

    continuumOSReconstructionPromoted :
      Bool

    continuumOSReconstructionPromotedIsFalse :
      continuumOSReconstructionPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    inputs :
      List UltrametricClusterInput

    inputsAreCanonical :
      inputs ≡ canonicalUltrametricClusterInputs

    promotionFlags :
      List UltrametricClusterPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ ultrametricClusterStatement

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ ultrametricClusterBoundary

    receiptBoundary :
      List String

open UltrametricClusterSeparationReceipt public

canonicalUltrametricClusterSeparationReceipt :
  UltrametricClusterSeparationReceipt
canonicalUltrametricClusterSeparationReceipt =
  record
    { status =
        finiteCarrierExactDecorrelationSurfaceRecorded
    ; statusIsCanonical =
        refl
    ; agreementUltrametricAvailable =
        true
    ; agreementUltrametricAvailableIsTrue =
        refl
    ; carrierOS3Receipt =
        OS3.canonicalCarrierOS3ReflectionPositivityReceipt
    ; carrierOS3FiniteSurfaceAvailable =
        refl
    ; checkerboardBridgeReceipt =
        Checker.canonicalCheckerboardUltrametricBridgeReceipt
    ; checkerboardSubmultiplicativityShapeAvailable =
        refl
    ; gate3NormDictionaryReceipt =
        Gate3.canonicalGate3NormDictionaryReceipt
    ; finiteSSPLimit71SurfaceAvailable =
        refl
    ; polymerKPReceipt =
        KP.canonicalPolymerKPAsMDLReceipt
    ; polymerKPBookkeepingAvailable =
        refl
    ; sspPrimes =
        finiteSSP
    ; sspPrimesAreCanonical =
        refl
    ; decorrelationVerdict =
        conditionalExactZeroByDisjointPrimeSupports_finiteCarrier
    ; decorrelationVerdictIsCarrierFinite =
        refl
    ; exactDecorrelationFunction =
        exactDecorrelation
    ; exactDecorrelationFunctionIsCanonical =
        refl
    ; p2p3P5p7DisjointSupportWitness =
        p2p3DisjointFromP5p7
    ; p2p3P5p7DisjointSupportWitnessIsCanonical =
        refl
    ; p2p3P5p7ExactDecorrelationFunction =
        p2p3P5p7ExactDecorrelation
    ; p2p3P5p7ExactDecorrelationFunctionIsCanonical =
        refl
    ; finiteCarrierExactDecorrelationConditionalRecorded =
        true
    ; finiteCarrierExactDecorrelationConditionalRecordedIsTrue =
        refl
    ; unconditionalExactDecorrelationProved =
        false
    ; unconditionalExactDecorrelationProvedIsFalse =
        refl
    ; generalDisjointSupportFactorisationProved =
        false
    ; generalDisjointSupportFactorisationProvedIsFalse =
        refl
    ; polymerActivitiesFactorForSeparatedClusters =
        false
    ; polymerActivitiesFactorForSeparatedClustersIsFalse =
        refl
    ; kpVerdict =
        finiteSSPEulerBoundSurface_betaMinApprox033
    ; kpVerdictIsFiniteCarrier =
        refl
    ; koteckyPreissFiniteCarrierBoundRecorded =
        true
    ; koteckyPreissFiniteCarrierBoundRecordedIsTrue =
        refl
    ; betaMinApproxNumerator =
        betaMinNumerator
    ; betaMinApproxNumeratorIsCanonical =
        refl
    ; betaMinApproxDenominator =
        betaMinDenominator
    ; betaMinApproxDenominatorIsCanonical =
        refl
    ; adelicEulerApproxNumerator =
        adelicEulerConstantApproxNumerator
    ; adelicEulerApproxNumeratorIsCanonical =
        refl
    ; adelicEulerApproxDenominator =
        adelicEulerConstantApproxDenominator
    ; adelicEulerApproxDenominatorIsCanonical =
        refl
    ; cMinNumeratorRecorded =
        cMinNumerator
    ; cMinNumeratorRecordedIsCanonical =
        refl
    ; cMinDenominatorRecorded =
        cMinDenominator
    ; cMinDenominatorRecordedIsCanonical =
        refl
    ; analyticContinuumKPProved =
        false
    ; analyticContinuumKPProvedIsFalse =
        refl
    ; uniformInfiniteVolumePolymerExpansionProved =
        false
    ; uniformInfiniteVolumePolymerExpansionProvedIsFalse =
        refl
    ; continuumOSReconstructionPromoted =
        false
    ; continuumOSReconstructionPromotedIsFalse =
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
        canonicalUltrametricClusterInputs
    ; inputsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        ultrametricClusterStatement
    ; statementIsCanonical =
        refl
    ; boundaryStatement =
        ultrametricClusterBoundary
    ; boundaryStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Exact covariance-zero is conditional on an explicit finite DisjointPrimeSupports witness"
        ∷ "A concrete p2,p3 plaquette versus p5,p7 plaquette disjoint-support exact-decorrelation lemma is inhabited"
        ∷ "The general disjoint-support factorisation proof remains open and unconditional exact decorrelation is false"
        ∷ "The KP bound is recorded as a finite Euler-product/beta_min surface with beta_min approximately 0.33"
        ∷ "The finite SSP set is the 15-prime carrier through p71"
        ∷ "This receipt consumes CarrierOS3ReflectionPositivityReceipt, CheckerboardUltrametricBridgeReceipt, Gate3NormDictionary, and PolymerKPAsMDLReceipt"
        ∷ "Continuum polymer convergence and infinite-volume Kotecky-Preiss analysis remain unproved here"
        ∷ "No continuum OS reconstruction or Clay Yang-Mills promotion is made"
        ∷ []
    }

ultrametricClusterKeepsClayFalse :
  clayYangMillsPromoted canonicalUltrametricClusterSeparationReceipt
  ≡
  false
ultrametricClusterKeepsClayFalse =
  refl
