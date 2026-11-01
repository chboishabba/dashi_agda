module DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Chen / Monstrous Moonshine prime-lane receipt surface.
--
-- This module records a bounded observation lane only.  It does not prove
-- Chen primality, supersingular-prime classification, genus-zero moonshine,
-- Hauptmodulicity, McKay-Thompson identities, or any DASHI closure theorem.

data MoonshinePrimeLanePromotionAuthorityToken : Set where

data MonsterPrimeLane : Set where
  p2 p3 p5 p7 p11 p13 p17 p19 p23 p29 p31 p41 p47 p59 p71 :
    MonsterPrimeLane

data MonsterPrimeLaneAtLeast11 : MonsterPrimeLane → Set where
  p11AtLeast11 :
    MonsterPrimeLaneAtLeast11 p11

  p13AtLeast11 :
    MonsterPrimeLaneAtLeast11 p13

  p17AtLeast11 :
    MonsterPrimeLaneAtLeast11 p17

  p19AtLeast11 :
    MonsterPrimeLaneAtLeast11 p19

  p23AtLeast11 :
    MonsterPrimeLaneAtLeast11 p23

  p29AtLeast11 :
    MonsterPrimeLaneAtLeast11 p29

  p31AtLeast11 :
    MonsterPrimeLaneAtLeast11 p31

  p41AtLeast11 :
    MonsterPrimeLaneAtLeast11 p41

  p47AtLeast11 :
    MonsterPrimeLaneAtLeast11 p47

  p59AtLeast11 :
    MonsterPrimeLaneAtLeast11 p59

  p71AtLeast11 :
    MonsterPrimeLaneAtLeast11 p71

monsterPrimeLaneToNat :
  MonsterPrimeLane →
  Nat
monsterPrimeLaneToNat p2 =
  2
monsterPrimeLaneToNat p3 =
  3
monsterPrimeLaneToNat p5 =
  5
monsterPrimeLaneToNat p7 =
  7
monsterPrimeLaneToNat p11 =
  11
monsterPrimeLaneToNat p13 =
  13
monsterPrimeLaneToNat p17 =
  17
monsterPrimeLaneToNat p19 =
  19
monsterPrimeLaneToNat p23 =
  23
monsterPrimeLaneToNat p29 =
  29
monsterPrimeLaneToNat p31 =
  31
monsterPrimeLaneToNat p41 =
  41
monsterPrimeLaneToNat p47 =
  47
monsterPrimeLaneToNat p59 =
  59
monsterPrimeLaneToNat p71 =
  71

monsterPrimeLaneConjecturalDHRDimension :
  MonsterPrimeLane →
  Nat
monsterPrimeLaneConjecturalDHRDimension p2 =
  1
monsterPrimeLaneConjecturalDHRDimension p3 =
  2
monsterPrimeLaneConjecturalDHRDimension p5 =
  3
monsterPrimeLaneConjecturalDHRDimension p7 =
  2
monsterPrimeLaneConjecturalDHRDimension p11 =
  0
monsterPrimeLaneConjecturalDHRDimension p13 =
  0
monsterPrimeLaneConjecturalDHRDimension p17 =
  0
monsterPrimeLaneConjecturalDHRDimension p19 =
  0
monsterPrimeLaneConjecturalDHRDimension p23 =
  0
monsterPrimeLaneConjecturalDHRDimension p29 =
  0
monsterPrimeLaneConjecturalDHRDimension p31 =
  0
monsterPrimeLaneConjecturalDHRDimension p41 =
  0
monsterPrimeLaneConjecturalDHRDimension p47 =
  0
monsterPrimeLaneConjecturalDHRDimension p59 =
  0
monsterPrimeLaneConjecturalDHRDimension p71 =
  0

monsterPrimeLaneDHRDimension2Is1 :
  monsterPrimeLaneConjecturalDHRDimension p2 ≡ 1
monsterPrimeLaneDHRDimension2Is1 =
  refl

monsterPrimeLaneDHRDimension3Is2 :
  monsterPrimeLaneConjecturalDHRDimension p3 ≡ 2
monsterPrimeLaneDHRDimension3Is2 =
  refl

monsterPrimeLaneDHRDimension5Is3 :
  monsterPrimeLaneConjecturalDHRDimension p5 ≡ 3
monsterPrimeLaneDHRDimension5Is3 =
  refl

monsterPrimeLaneDHRDimension7Is2 :
  monsterPrimeLaneConjecturalDHRDimension p7 ≡ 2
monsterPrimeLaneDHRDimension7Is2 =
  refl

monsterPrimeLaneDHRDimensionAtLeast11Is0 :
  (p : MonsterPrimeLane) →
  MonsterPrimeLaneAtLeast11 p →
  monsterPrimeLaneConjecturalDHRDimension p ≡ 0
monsterPrimeLaneDHRDimensionAtLeast11Is0 p11 p11AtLeast11 =
  refl
monsterPrimeLaneDHRDimensionAtLeast11Is0 p13 p13AtLeast11 =
  refl
monsterPrimeLaneDHRDimensionAtLeast11Is0 p17 p17AtLeast11 =
  refl
monsterPrimeLaneDHRDimensionAtLeast11Is0 p19 p19AtLeast11 =
  refl
monsterPrimeLaneDHRDimensionAtLeast11Is0 p23 p23AtLeast11 =
  refl
monsterPrimeLaneDHRDimensionAtLeast11Is0 p29 p29AtLeast11 =
  refl
monsterPrimeLaneDHRDimensionAtLeast11Is0 p31 p31AtLeast11 =
  refl
monsterPrimeLaneDHRDimensionAtLeast11Is0 p41 p41AtLeast11 =
  refl
monsterPrimeLaneDHRDimensionAtLeast11Is0 p47 p47AtLeast11 =
  refl
monsterPrimeLaneDHRDimensionAtLeast11Is0 p59 p59AtLeast11 =
  refl
monsterPrimeLaneDHRDimensionAtLeast11Is0 p71 p71AtLeast11 =
  refl

canonicalMonsterPrimeLane :
  List MonsterPrimeLane
canonicalMonsterPrimeLane =
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

canonicalMonsterPrimeLaneNats :
  List Nat
canonicalMonsterPrimeLaneNats =
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

data PrimeLaneObservationTarget : Set where
  chenPrimeTarget :
    PrimeLaneObservationTarget

  supersingularMonsterPrimeTarget :
    PrimeLaneObservationTarget

  genusZeroHauptmodulTarget :
    PrimeLaneObservationTarget

  mckayThompsonLaneAmplitudeObservationTarget :
    PrimeLaneObservationTarget

canonicalPrimeLaneObservationTargets :
  List PrimeLaneObservationTarget
canonicalPrimeLaneObservationTargets =
  chenPrimeTarget
  ∷ supersingularMonsterPrimeTarget
  ∷ genusZeroHauptmodulTarget
  ∷ mckayThompsonLaneAmplitudeObservationTarget
  ∷ []

data PrimeLaneOpenObligation : Set where
  missingChenPrimeNumberTheoryWitness :
    PrimeLaneOpenObligation

  missingSupersingularPrimeClassificationAdapter :
    PrimeLaneOpenObligation

  missingMonsterGroupBinding :
    PrimeLaneOpenObligation

  missingGenusZeroHauptmodulProof :
    PrimeLaneOpenObligation

  missingMcKayThompsonAmplitudeConstruction :
    PrimeLaneOpenObligation

canonicalPrimeLaneOpenObligations :
  List PrimeLaneOpenObligation
canonicalPrimeLaneOpenObligations =
  missingChenPrimeNumberTheoryWitness
  ∷ missingSupersingularPrimeClassificationAdapter
  ∷ missingMonsterGroupBinding
  ∷ missingGenusZeroHauptmodulProof
  ∷ missingMcKayThompsonAmplitudeConstruction
  ∷ []

record ChenPrimeObservation (p : MonsterPrimeLane) : Set where
  field
    primeValue :
      Nat

    primeValue-v :
      primeValue ≡ monsterPrimeLaneToNat p

    chenPrimeStatus :
      String

    chenPrimeStatus-v :
      chenPrimeStatus
      ≡
      "target-only-DASHI-tracked-prime-recorded-on-Chen-prime-lane"

    supersingularMonsterLaneStatus :
      String

    supersingularMonsterLaneStatus-v :
      supersingularMonsterLaneStatus
      ≡
      "target-only-prime-recorded-on-supersingular-Monster-prime-lane"

    chenProofPromoted :
      Bool

    chenProofPromoted-v :
      chenProofPromoted ≡ false

open ChenPrimeObservation public

canonicalChenPrimeObservation :
  (p : MonsterPrimeLane) →
  ChenPrimeObservation p
canonicalChenPrimeObservation p =
  record
    { primeValue =
        monsterPrimeLaneToNat p
    ; primeValue-v =
        refl
    ; chenPrimeStatus =
        "target-only-DASHI-tracked-prime-recorded-on-Chen-prime-lane"
    ; chenPrimeStatus-v =
        refl
    ; supersingularMonsterLaneStatus =
        "target-only-prime-recorded-on-supersingular-Monster-prime-lane"
    ; supersingularMonsterLaneStatus-v =
        refl
    ; chenProofPromoted =
        false
    ; chenProofPromoted-v =
        refl
    }

record MoonshinePrimeLaneReceiptSurface : Setω where
  field
    receiptStatus :
      String

    receiptStatus-v :
      receiptStatus
      ≡
      "target-only-Chen-Moonshine-prime-lane-observation-surface"

    trackedPrimeLane :
      List MonsterPrimeLane

    trackedPrimeLane-v :
      trackedPrimeLane
      ≡
      canonicalMonsterPrimeLane

    trackedPrimeLaneNats :
      List Nat

    trackedPrimeLaneNats-v :
      trackedPrimeLaneNats
      ≡
      canonicalMonsterPrimeLaneNats

    observationTargets :
      List PrimeLaneObservationTarget

    observationTargets-v :
      observationTargets
      ≡
      canonicalPrimeLaneObservationTargets

    allDASHITrackedPrimesChenTarget :
      String

    allDASHITrackedPrimesChenTarget-v :
      allDASHITrackedPrimesChenTarget
      ≡
      "target-only-all-DASHI-tracked-primes-are-Chen-prime-lane-observations"

    chenObservationAt :
      (p : MonsterPrimeLane) →
      ChenPrimeObservation p

    supersingularMonsterPrimeLaneSet :
      List Nat

    supersingularMonsterPrimeLaneSet-v :
      supersingularMonsterPrimeLaneSet
      ≡
      canonicalMonsterPrimeLaneNats

    genusZeroHauptmodulObservation :
      String

    genusZeroHauptmodulObservation-v :
      genusZeroHauptmodulObservation
      ≡
      "target-only-Monster-prime-lane-suggests-genus-zero-Hauptmodul-observation"

    McKayThompsonLaneClass :
      Set

    LaneAmplitude :
      McKayThompsonLaneClass →
      MonsterPrimeLane →
      Set

    mckayThompsonLaneAmplitudeTarget :
      String

    mckayThompsonLaneAmplitudeTarget-v :
      mckayThompsonLaneAmplitudeTarget
      ≡
      "target-only-McKay-Thompson-class-amplitude-over-Chen-Moonshine-prime-lane"

    conjecturalDHRDimension :
      MonsterPrimeLane →
      Nat

    dhrDimension2Is1 :
      conjecturalDHRDimension p2 ≡ 1

    dhrDimension3Is2 :
      conjecturalDHRDimension p3 ≡ 2

    dhrDimension5Is3 :
      conjecturalDHRDimension p5 ≡ 3

    dhrDimension7Is2 :
      conjecturalDHRDimension p7 ≡ 2

    dhrDimensionAtLeast11Is0 :
      (p : MonsterPrimeLane) →
      MonsterPrimeLaneAtLeast11 p →
      conjecturalDHRDimension p ≡ 0

    dhrDimensionConjecturalOpen :
      Bool

    dhrDimensionConjecturalOpen-v :
      dhrDimensionConjecturalOpen ≡ true

    openObligations :
      List PrimeLaneOpenObligation

    openObligations-v :
      openObligations
      ≡
      canonicalPrimeLaneOpenObligations

    noChenTheoremPromoted :
      Bool

    noChenTheoremPromoted-v :
      noChenTheoremPromoted ≡ true

    noMoonshineTheoremPromoted :
      Bool

    noMoonshineTheoremPromoted-v :
      noMoonshineTheoremPromoted ≡ true

    noClosurePromotionFromThisReceipt :
      Bool

    noClosurePromotionFromThisReceipt-v :
      noClosurePromotionFromThisReceipt ≡ true

    noPromotionWithoutAuthority :
      MoonshinePrimeLanePromotionAuthorityToken →
      ⊥

    governanceBoundary :
      List String

open MoonshinePrimeLaneReceiptSurface public

canonicalMoonshinePrimeLaneReceiptSurface :
  MoonshinePrimeLaneReceiptSurface
canonicalMoonshinePrimeLaneReceiptSurface =
  record
    { receiptStatus =
        "target-only-Chen-Moonshine-prime-lane-observation-surface"
    ; receiptStatus-v =
        refl
    ; trackedPrimeLane =
        canonicalMonsterPrimeLane
    ; trackedPrimeLane-v =
        refl
    ; trackedPrimeLaneNats =
        canonicalMonsterPrimeLaneNats
    ; trackedPrimeLaneNats-v =
        refl
    ; observationTargets =
        canonicalPrimeLaneObservationTargets
    ; observationTargets-v =
        refl
    ; allDASHITrackedPrimesChenTarget =
        "target-only-all-DASHI-tracked-primes-are-Chen-prime-lane-observations"
    ; allDASHITrackedPrimesChenTarget-v =
        refl
    ; chenObservationAt =
        canonicalChenPrimeObservation
    ; supersingularMonsterPrimeLaneSet =
        canonicalMonsterPrimeLaneNats
    ; supersingularMonsterPrimeLaneSet-v =
        refl
    ; genusZeroHauptmodulObservation =
        "target-only-Monster-prime-lane-suggests-genus-zero-Hauptmodul-observation"
    ; genusZeroHauptmodulObservation-v =
        refl
    ; McKayThompsonLaneClass =
        MonsterPrimeLane
    ; LaneAmplitude =
        λ _ _ →
          Bool
    ; mckayThompsonLaneAmplitudeTarget =
        "target-only-McKay-Thompson-class-amplitude-over-Chen-Moonshine-prime-lane"
    ; mckayThompsonLaneAmplitudeTarget-v =
        refl
    ; conjecturalDHRDimension =
        monsterPrimeLaneConjecturalDHRDimension
    ; dhrDimension2Is1 =
        refl
    ; dhrDimension3Is2 =
        refl
    ; dhrDimension5Is3 =
        refl
    ; dhrDimension7Is2 =
        refl
    ; dhrDimensionAtLeast11Is0 =
        monsterPrimeLaneDHRDimensionAtLeast11Is0
    ; dhrDimensionConjecturalOpen =
        true
    ; dhrDimensionConjecturalOpen-v =
        refl
    ; openObligations =
        canonicalPrimeLaneOpenObligations
    ; openObligations-v =
        refl
    ; noChenTheoremPromoted =
        true
    ; noChenTheoremPromoted-v =
        refl
    ; noMoonshineTheoremPromoted =
        true
    ; noMoonshineTheoremPromoted-v =
        refl
    ; noClosurePromotionFromThisReceipt =
        true
    ; noClosurePromotionFromThisReceipt-v =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; governanceBoundary =
        "This receipt records Chen-prime and Monstrous-Moonshine prime-lane targets only"
        ∷ "The tracked prime lane is the supersingular Monster prime set 2,3,5,7,11,13,17,19,23,29,31,41,47,59,71"
        ∷ "Each tracked prime has a Chen-prime observation target, but no Chen number-theory proof is constructed here"
        ∷ "Genus-zero and Hauptmodul language is recorded as an observation target, not as a Moonshine theorem"
        ∷ "McKay-Thompson lane amplitude is a target socket over the tracked prime lane, not an amplitude construction"
        ∷ "Conjectural DHR lane dimension is recorded as 2->1, 3->2, 5->3, 7->2, and primes >=11 -> 0, explicitly open and non-promoting in this base observation surface"
        ∷ "This module does not import into Everything and does not promote a closure theorem"
        ∷ []
    }
