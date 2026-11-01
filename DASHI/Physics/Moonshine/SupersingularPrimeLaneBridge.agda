module DASHI.Physics.Moonshine.SupersingularPrimeLaneBridge where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- DASHI -> 15 supersingular-prime bridge.
--
-- This receipt records the precise mathematical characterization of the
-- tracked DASHI prime-lane set.  The positive claim is narrow:
--
--   the tracked DASHI lane set is the 15 supersingular-prime set, and the
--   DASHI-natural entry point is Ogg condition (2), field-completeness of the
--   supersingular j-invariants over F_p.
--
-- It deliberately does not prove Ogg's theorem internally, derive the prime
-- set from first principles, solve Ogg's original Monster question, derive the
-- Standard Model gauge group, or promote any terminal/unification claim.

data SupersingularPrime : Set where
  p2 p3 p5 p7 p11 p13 p17 p19 p23 p29 p31 p41 p47 p59 p71 :
    SupersingularPrime

supersingularPrimeToNat :
  SupersingularPrime →
  Nat
supersingularPrimeToNat p2 =
  2
supersingularPrimeToNat p3 =
  3
supersingularPrimeToNat p5 =
  5
supersingularPrimeToNat p7 =
  7
supersingularPrimeToNat p11 =
  11
supersingularPrimeToNat p13 =
  13
supersingularPrimeToNat p17 =
  17
supersingularPrimeToNat p19 =
  19
supersingularPrimeToNat p23 =
  23
supersingularPrimeToNat p29 =
  29
supersingularPrimeToNat p31 =
  31
supersingularPrimeToNat p41 =
  41
supersingularPrimeToNat p47 =
  47
supersingularPrimeToNat p59 =
  59
supersingularPrimeToNat p71 =
  71

canonicalSupersingularPrimeLane :
  List SupersingularPrime
canonicalSupersingularPrimeLane =
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

canonicalSupersingularPrimeLaneNats :
  List Nat
canonicalSupersingularPrimeLaneNats =
  2
  ∷ 3
  ∷ 5
  ∷ 7
  ∷ 11
  ∷ 13
  ∷ 17
  ∷ 19
  ∷ 23
  ∷ 29
  ∷ 31
  ∷ 41
  ∷ 47
  ∷ 59
  ∷ 71
  ∷ []

supersingularPrimeToMonsterPrimeLane :
  SupersingularPrime →
  Lane.MonsterPrimeLane
supersingularPrimeToMonsterPrimeLane p2 =
  Lane.p2
supersingularPrimeToMonsterPrimeLane p3 =
  Lane.p3
supersingularPrimeToMonsterPrimeLane p5 =
  Lane.p5
supersingularPrimeToMonsterPrimeLane p7 =
  Lane.p7
supersingularPrimeToMonsterPrimeLane p11 =
  Lane.p11
supersingularPrimeToMonsterPrimeLane p13 =
  Lane.p13
supersingularPrimeToMonsterPrimeLane p17 =
  Lane.p17
supersingularPrimeToMonsterPrimeLane p19 =
  Lane.p19
supersingularPrimeToMonsterPrimeLane p23 =
  Lane.p23
supersingularPrimeToMonsterPrimeLane p29 =
  Lane.p29
supersingularPrimeToMonsterPrimeLane p31 =
  Lane.p31
supersingularPrimeToMonsterPrimeLane p41 =
  Lane.p41
supersingularPrimeToMonsterPrimeLane p47 =
  Lane.p47
supersingularPrimeToMonsterPrimeLane p59 =
  Lane.p59
supersingularPrimeToMonsterPrimeLane p71 =
  Lane.p71

supersingularPrimeLaneMapsToSameNat :
  (p : SupersingularPrime) →
  Lane.monsterPrimeLaneToNat (supersingularPrimeToMonsterPrimeLane p)
    ≡
  supersingularPrimeToNat p
supersingularPrimeLaneMapsToSameNat p2 =
  refl
supersingularPrimeLaneMapsToSameNat p3 =
  refl
supersingularPrimeLaneMapsToSameNat p5 =
  refl
supersingularPrimeLaneMapsToSameNat p7 =
  refl
supersingularPrimeLaneMapsToSameNat p11 =
  refl
supersingularPrimeLaneMapsToSameNat p13 =
  refl
supersingularPrimeLaneMapsToSameNat p17 =
  refl
supersingularPrimeLaneMapsToSameNat p19 =
  refl
supersingularPrimeLaneMapsToSameNat p23 =
  refl
supersingularPrimeLaneMapsToSameNat p29 =
  refl
supersingularPrimeLaneMapsToSameNat p31 =
  refl
supersingularPrimeLaneMapsToSameNat p41 =
  refl
supersingularPrimeLaneMapsToSameNat p47 =
  refl
supersingularPrimeLaneMapsToSameNat p59 =
  refl
supersingularPrimeLaneMapsToSameNat p71 =
  refl

data SupersingularPrimeLaneCitation : Set where
  ogg1975AutomorphismesDeCourbesModulaires :
    SupersingularPrimeLaneCitation

  borcherds1992MonstrousMoonshine :
    SupersingularPrimeLaneCitation

data OggCondition : Set where
  genusZeroX0Plus :
    OggCondition

  supersingularPolynomialSplitsOverFp :
    OggCondition

  primeDividesMonsterOrder :
    OggCondition

canonicalOggConditions :
  List OggCondition
canonicalOggConditions =
  genusZeroX0Plus
  ∷ supersingularPolynomialSplitsOverFp
  ∷ primeDividesMonsterOrder
  ∷ []

record SupersingularPrimeLaneAuthority : Set where
  field
    citation :
      SupersingularPrimeLaneCitation

    authorityLabel :
      String

    acceptedAsExternalAuthority :
      Bool

    acceptedAsExternalAuthorityIsTrue :
      acceptedAsExternalAuthority ≡ true

open SupersingularPrimeLaneAuthority public

ogg1975Authority :
  SupersingularPrimeLaneAuthority
ogg1975Authority =
  record
    { citation =
        ogg1975AutomorphismesDeCourbesModulaires
    ; authorityLabel =
        "Ogg 1975: Automorphismes de courbes modulaires; genus-zero/supersingular-prime classification authority"
    ; acceptedAsExternalAuthority =
        true
    ; acceptedAsExternalAuthorityIsTrue =
        refl
    }

borcherds1992Authority :
  SupersingularPrimeLaneAuthority
borcherds1992Authority =
  record
    { citation =
        borcherds1992MonstrousMoonshine
    ; authorityLabel =
        "Borcherds 1992: Monstrous moonshine and monstrous Lie superalgebras; Monster-to-genus-zero moonshine authority"
    ; acceptedAsExternalAuthority =
        true
    ; acceptedAsExternalAuthorityIsTrue =
        refl
    }

record OggEquivalence (p : SupersingularPrime) : Set where
  field
    prime :
      SupersingularPrime

    primeIsInput :
      prime ≡ p

    genusZeroModularCurve :
      Bool

    genusZeroModularCurveIsTrue :
      genusZeroModularCurve ≡ true

    supersingularFieldComplete :
      Bool

    supersingularFieldCompleteIsTrue :
      supersingularFieldComplete ≡ true

    dividesMonsterOrder :
      Bool

    dividesMonsterOrderIsTrue :
      dividesMonsterOrder ≡ true

    externalAuthorityOnly :
      Bool

    externalAuthorityOnlyIsTrue :
      externalAuthorityOnly ≡ true

open OggEquivalence public

canonicalOggEquivalence :
  (p : SupersingularPrime) →
  OggEquivalence p
canonicalOggEquivalence p =
  record
    { prime =
        p
    ; primeIsInput =
        refl
    ; genusZeroModularCurve =
        true
    ; genusZeroModularCurveIsTrue =
        refl
    ; supersingularFieldComplete =
        true
    ; supersingularFieldCompleteIsTrue =
        refl
    ; dividesMonsterOrder =
        true
    ; dividesMonsterOrderIsTrue =
        refl
    ; externalAuthorityOnly =
        true
    ; externalAuthorityOnlyIsTrue =
        refl
    }

record DASHILaneLegitimacy (p : SupersingularPrime) : Set where
  field
    oggEquivalence :
      OggEquivalence p

    dashiNaturalCondition :
      OggCondition

    dashiNaturalConditionIsFieldCompleteness :
      dashiNaturalCondition ≡ supersingularPolynomialSplitsOverFp

    depth1FieldComplete :
      supersingularFieldComplete oggEquivalence ≡ true

    localGeometryDepth :
      Nat

    localGeometryDepthIs1 :
      localGeometryDepth ≡ 1

    laneBoundaryWellDefinedAtDepth1 :
      Bool

    laneBoundaryWellDefinedAtDepth1IsTrue :
      laneBoundaryWellDefinedAtDepth1 ≡ true

open DASHILaneLegitimacy public

canonicalDASHILaneLegitimacy :
  (p : SupersingularPrime) →
  DASHILaneLegitimacy p
canonicalDASHILaneLegitimacy p =
  record
    { oggEquivalence =
        canonicalOggEquivalence p
    ; dashiNaturalCondition =
        supersingularPolynomialSplitsOverFp
    ; dashiNaturalConditionIsFieldCompleteness =
        refl
    ; depth1FieldComplete =
        refl
    ; localGeometryDepth =
        1
    ; localGeometryDepthIs1 =
        refl
    ; laneBoundaryWellDefinedAtDepth1 =
        true
    ; laneBoundaryWellDefinedAtDepth1IsTrue =
        refl
    }

data DASHIGateAssignment : Set where
  u1HyperchargeLaneG1 :
    DASHIGateAssignment

  su2WeakLaneG1 :
    DASHIGateAssignment

  su3ColorLaneG1 :
    DASHIGateAssignment

  gravityLaneG2 :
    DASHIGateAssignment

  higherGenerationOrDHRSectorLane :
    DASHIGateAssignment

gateAssignment :
  SupersingularPrime →
  DASHIGateAssignment
gateAssignment p2 =
  u1HyperchargeLaneG1
gateAssignment p3 =
  su2WeakLaneG1
gateAssignment p5 =
  su3ColorLaneG1
gateAssignment p7 =
  gravityLaneG2
gateAssignment p11 =
  higherGenerationOrDHRSectorLane
gateAssignment p13 =
  higherGenerationOrDHRSectorLane
gateAssignment p17 =
  higherGenerationOrDHRSectorLane
gateAssignment p19 =
  higherGenerationOrDHRSectorLane
gateAssignment p23 =
  higherGenerationOrDHRSectorLane
gateAssignment p29 =
  higherGenerationOrDHRSectorLane
gateAssignment p31 =
  higherGenerationOrDHRSectorLane
gateAssignment p41 =
  higherGenerationOrDHRSectorLane
gateAssignment p47 =
  higherGenerationOrDHRSectorLane
gateAssignment p59 =
  higherGenerationOrDHRSectorLane
gateAssignment p71 =
  higherGenerationOrDHRSectorLane

supersingularJInvariantCountBound :
  SupersingularPrime →
  Nat
supersingularJInvariantCountBound p2 =
  1
supersingularJInvariantCountBound p3 =
  1
supersingularJInvariantCountBound p5 =
  1
supersingularJInvariantCountBound p7 =
  1
supersingularJInvariantCountBound p11 =
  1
supersingularJInvariantCountBound p13 =
  2
supersingularJInvariantCountBound p17 =
  2
supersingularJInvariantCountBound p19 =
  2
supersingularJInvariantCountBound p23 =
  2
supersingularJInvariantCountBound p29 =
  3
supersingularJInvariantCountBound p31 =
  3
supersingularJInvariantCountBound p41 =
  4
supersingularJInvariantCountBound p47 =
  4
supersingularJInvariantCountBound p59 =
  5
supersingularJInvariantCountBound p71 =
  6

p2UniqueSupersingularCurve :
  supersingularJInvariantCountBound p2 ≡ 1
p2UniqueSupersingularCurve =
  refl

p3UniqueSupersingularCurve :
  supersingularJInvariantCountBound p3 ≡ 1
p3UniqueSupersingularCurve =
  refl

p5UniqueSupersingularCurve :
  supersingularJInvariantCountBound p5 ≡ 1
p5UniqueSupersingularCurve =
  refl

p7UniqueSupersingularCurve :
  supersingularJInvariantCountBound p7 ≡ 1
p7UniqueSupersingularCurve =
  refl

data SupersingularPrimeLaneBoundary : Set where
  boundaryOggTheoremExternalAuthority :
    SupersingularPrimeLaneBoundary

  boundaryBorcherdsAuthorityNotReverseDerivation :
    SupersingularPrimeLaneBoundary

  boundaryPrimeSetNotForcedFromFirstPrinciples :
    SupersingularPrimeLaneBoundary

  boundaryNoMonsterFirstPrinciplesDerivation :
    SupersingularPrimeLaneBoundary

  boundaryNoStandardModelGaugeDerivation :
    SupersingularPrimeLaneBoundary

  boundaryNoTerminalUnificationPromotion :
    SupersingularPrimeLaneBoundary

canonicalSupersingularPrimeLaneBoundaries :
  List SupersingularPrimeLaneBoundary
canonicalSupersingularPrimeLaneBoundaries =
  boundaryOggTheoremExternalAuthority
  ∷ boundaryBorcherdsAuthorityNotReverseDerivation
  ∷ boundaryPrimeSetNotForcedFromFirstPrinciples
  ∷ boundaryNoMonsterFirstPrinciplesDerivation
  ∷ boundaryNoStandardModelGaugeDerivation
  ∷ boundaryNoTerminalUnificationPromotion
  ∷ []

data SupersingularPrimeLanePromotionAuthorityToken : Set where

record SupersingularPrimeLaneBridgeReceipt : Set where
  field
    trackedDASHILaneReceiptBound :
      Bool

    trackedDASHILaneReceiptBoundIsTrue :
      trackedDASHILaneReceiptBound ≡ true

    supersingularPrimes :
      List SupersingularPrime

    supersingularPrimesAreCanonical :
      supersingularPrimes ≡ canonicalSupersingularPrimeLane

    supersingularPrimeNats :
      List Nat

    supersingularPrimeNatsAreCanonical :
      supersingularPrimeNats ≡ canonicalSupersingularPrimeLaneNats

    dashiTrackedPrimeNats :
      List Nat

    dashiTrackedPrimeNatsMatchPSS :
      dashiTrackedPrimeNats ≡ canonicalSupersingularPrimeLaneNats

    oggConditions :
      List OggCondition

    oggConditionsAreCanonical :
      oggConditions ≡ canonicalOggConditions

    oggAuthority :
      SupersingularPrimeLaneAuthority

    borcherdsAuthority :
      SupersingularPrimeLaneAuthority

    laneLegitimacyAt :
      (p : SupersingularPrime) →
      DASHILaneLegitimacy p

    dashiNaturalCharacterization :
      String

    dashiNaturalCharacterization-v :
      dashiNaturalCharacterization
      ≡
      "A DASHI tracked prime lane is selected by Ogg condition (2): the supersingular polynomial splits over F_p, so depth-1 lane geometry is field-complete."

    DASHIPrimeSetIsP-SS :
      Bool

    DASHIPrimeSetIsP-SS-isTrue :
      DASHIPrimeSetIsP-SS ≡ true

    primeSetForcedFromFirstPrinciples :
      Bool

    primeSetForcedFromFirstPrinciplesIsFalse :
      primeSetForcedFromFirstPrinciples ≡ false

    oggOriginalQuestionResolved :
      Bool

    oggOriginalQuestionResolvedIsFalse :
      oggOriginalQuestionResolved ≡ false

    monsterConnectionObservedNotDerivation :
      Bool

    monsterConnectionObservedNotDerivationIsTrue :
      monsterConnectionObservedNotDerivation ≡ true

    standardModelGaugeGroupDerived :
      Bool

    standardModelGaugeGroupDerivedIsFalse :
      standardModelGaugeGroupDerived ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    boundaries :
      List SupersingularPrimeLaneBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalSupersingularPrimeLaneBoundaries

    noPromotionWithoutAuthority :
      SupersingularPrimeLanePromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open SupersingularPrimeLaneBridgeReceipt public

canonicalSupersingularPrimeLaneBridgeReceipt :
  SupersingularPrimeLaneBridgeReceipt
canonicalSupersingularPrimeLaneBridgeReceipt =
  record
    { trackedDASHILaneReceiptBound =
        true
    ; trackedDASHILaneReceiptBoundIsTrue =
        refl
    ; supersingularPrimes =
        canonicalSupersingularPrimeLane
    ; supersingularPrimesAreCanonical =
        refl
    ; supersingularPrimeNats =
        canonicalSupersingularPrimeLaneNats
    ; supersingularPrimeNatsAreCanonical =
        refl
    ; dashiTrackedPrimeNats =
        Lane.canonicalMonsterPrimeLaneNats
    ; dashiTrackedPrimeNatsMatchPSS =
        refl
    ; oggConditions =
        canonicalOggConditions
    ; oggConditionsAreCanonical =
        refl
    ; oggAuthority =
        ogg1975Authority
    ; borcherdsAuthority =
        borcherds1992Authority
    ; laneLegitimacyAt =
        canonicalDASHILaneLegitimacy
    ; dashiNaturalCharacterization =
        "A DASHI tracked prime lane is selected by Ogg condition (2): the supersingular polynomial splits over F_p, so depth-1 lane geometry is field-complete."
    ; dashiNaturalCharacterization-v =
        refl
    ; DASHIPrimeSetIsP-SS =
        true
    ; DASHIPrimeSetIsP-SS-isTrue =
        refl
    ; primeSetForcedFromFirstPrinciples =
        false
    ; primeSetForcedFromFirstPrinciplesIsFalse =
        refl
    ; oggOriginalQuestionResolved =
        false
    ; oggOriginalQuestionResolvedIsFalse =
        refl
    ; monsterConnectionObservedNotDerivation =
        true
    ; monsterConnectionObservedNotDerivationIsTrue =
        refl
    ; standardModelGaugeGroupDerived =
        false
    ; standardModelGaugeGroupDerivedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; boundaries =
        canonicalSupersingularPrimeLaneBoundaries
    ; boundariesAreCanonical =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "The DASHI tracked prime set is bound to the 15 supersingular primes P_SS"
        ∷ "Ogg condition (2), supersingular field-completeness over F_p, is the DASHI-natural bridge condition"
        ∷ "Ogg 1975 and Borcherds 1992 are recorded as external authority tokens, not local proofs"
        ∷ "The Monster connection is observed but not used as a first-principles derivation of the carrier"
        ∷ "primeSetForcedFromFirstPrinciples, oggOriginalQuestionResolved, standardModelGaugeGroupDerived, and terminalClaimPromoted remain false"
        ∷ []
    }

dashiPrimeSetIsP-SS :
  Bool
dashiPrimeSetIsP-SS =
  SupersingularPrimeLaneBridgeReceipt.DASHIPrimeSetIsP-SS
    canonicalSupersingularPrimeLaneBridgeReceipt

dashiPrimeSetIsP-SS-isTrue :
  dashiPrimeSetIsP-SS ≡ true
dashiPrimeSetIsP-SS-isTrue =
  refl

dashiPrimeSetForcedFromFirstPrinciples :
  Bool
dashiPrimeSetForcedFromFirstPrinciples =
  SupersingularPrimeLaneBridgeReceipt.primeSetForcedFromFirstPrinciples
    canonicalSupersingularPrimeLaneBridgeReceipt

dashiPrimeSetForcedFromFirstPrinciplesIsFalse :
  dashiPrimeSetForcedFromFirstPrinciples ≡ false
dashiPrimeSetForcedFromFirstPrinciplesIsFalse =
  refl

dashiOggOriginalQuestionResolved :
  Bool
dashiOggOriginalQuestionResolved =
  SupersingularPrimeLaneBridgeReceipt.oggOriginalQuestionResolved
    canonicalSupersingularPrimeLaneBridgeReceipt

dashiOggOriginalQuestionResolvedIsFalse :
  dashiOggOriginalQuestionResolved ≡ false
dashiOggOriginalQuestionResolvedIsFalse =
  refl

dashiStandardModelGaugeGroupDerived :
  Bool
dashiStandardModelGaugeGroupDerived =
  SupersingularPrimeLaneBridgeReceipt.standardModelGaugeGroupDerived
    canonicalSupersingularPrimeLaneBridgeReceipt

dashiStandardModelGaugeGroupDerivedIsFalse :
  dashiStandardModelGaugeGroupDerived ≡ false
dashiStandardModelGaugeGroupDerivedIsFalse =
  refl
