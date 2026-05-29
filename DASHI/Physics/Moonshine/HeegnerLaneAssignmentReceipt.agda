module DASHI.Physics.Moonshine.HeegnerLaneAssignmentReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Heegner lane assignment receipt.
--
-- This module records the small CM/Heegner lane assignment used by the
-- p2/p3/p5 moonshine-carrier bookkeeping.  The positive claim is deliberately
-- narrow: the three active lanes are assigned the classical CM j-values,
-- discriminants, conductors, finite point counts, modular curves, and
-- hyperbolic X0(N) volumes listed below.
--
-- It does not derive the assignments from first principles, construct a
-- carrier-to-physics promotion, or promote the sterile -8 candidate.

data HeegnerLaneAssignmentStatus : Set where
  heegnerLaneAssignmentsRecordedNoPromotion :
    HeegnerLaneAssignmentStatus

data HeegnerPrimeLane : Set where
  p2 :
    HeegnerPrimeLane

  p3 :
    HeegnerPrimeLane

  p5 :
    HeegnerPrimeLane

data HeegnerDiscriminant : Set where
  D-3 :
    HeegnerDiscriminant

  D-4 :
    HeegnerDiscriminant

  D-7 :
    HeegnerDiscriminant

  D-8 :
    HeegnerDiscriminant

data HeegnerLaneCitationAuthority : Set where
  classicalCMJInvariantAuthority :
    HeegnerLaneCitationAuthority

  classNumberOneDiscriminantAuthority :
    HeegnerLaneCitationAuthority

  hasseSupersingularPointCountAuthority :
    HeegnerLaneCitationAuthority

  modularCurveVolumeAuthority :
    HeegnerLaneCitationAuthority

data HeegnerLaneBlocker : Set where
  missingFirstPrinciplesLaneDerivation :
    HeegnerLaneBlocker

  missingCarrierPromotionBridge :
    HeegnerLaneBlocker

  sterileDMinusEightNotPromoted :
    HeegnerLaneBlocker

data HeegnerLaneConsequence : Set where
  p2GaussianLaneRecorded :
    HeegnerLaneConsequence

  p3EisensteinLaneRecorded :
    HeegnerLaneConsequence

  p5HeegnerSevenLaneRecorded :
    HeegnerLaneConsequence

  smallClassNumberOneWindowClosed :
    HeegnerLaneConsequence

  dMinusEightSterileCandidateRecorded :
    HeegnerLaneConsequence

canonicalHeegnerPrimeLanes :
  List HeegnerPrimeLane
canonicalHeegnerPrimeLanes =
  p2
  ∷ p3
  ∷ p5
  ∷ []

canonicalHeegnerLaneCitationAuthorities :
  List HeegnerLaneCitationAuthority
canonicalHeegnerLaneCitationAuthorities =
  classicalCMJInvariantAuthority
  ∷ classNumberOneDiscriminantAuthority
  ∷ hasseSupersingularPointCountAuthority
  ∷ modularCurveVolumeAuthority
  ∷ []

canonicalHeegnerLaneBlockers :
  List HeegnerLaneBlocker
canonicalHeegnerLaneBlockers =
  missingFirstPrinciplesLaneDerivation
  ∷ missingCarrierPromotionBridge
  ∷ sterileDMinusEightNotPromoted
  ∷ []

canonicalHeegnerLaneConsequences :
  List HeegnerLaneConsequence
canonicalHeegnerLaneConsequences =
  p2GaussianLaneRecorded
  ∷ p3EisensteinLaneRecorded
  ∷ p5HeegnerSevenLaneRecorded
  ∷ smallClassNumberOneWindowClosed
  ∷ dMinusEightSterileCandidateRecorded
  ∷ []

activeSmallClassNumberOneDiscriminantsAbsLe7 :
  List HeegnerDiscriminant
activeSmallClassNumberOneDiscriminantsAbsLe7 =
  D-4
  ∷ D-3
  ∷ D-7
  ∷ []

smallClassNumberOneDiscriminantsAbsLe8 :
  List HeegnerDiscriminant
smallClassNumberOneDiscriminantsAbsLe8 =
  D-4
  ∷ D-3
  ∷ D-7
  ∷ D-8
  ∷ []

sterileSmallClassNumberOneDiscriminantsAbsLe8 :
  List HeegnerDiscriminant
sterileSmallClassNumberOneDiscriminantsAbsLe8 =
  D-8
  ∷ []

discriminantAbs :
  HeegnerDiscriminant →
  Nat
discriminantAbs D-3 =
  3
discriminantAbs D-4 =
  4
discriminantAbs D-7 =
  7
discriminantAbs D-8 =
  8

p2AssignmentLabel : String
p2AssignmentLabel =
  "p2 -> j=1728, discriminant -4, conductor 4, |E(F2)|=3, X0(4), vol=2*pi"

p3AssignmentLabel : String
p3AssignmentLabel =
  "p3 -> j=0, discriminant -3, conductor 3, |E(F3)|=4, X0(3), vol=4*pi/3"

p5AssignmentLabel : String
p5AssignmentLabel =
  "p5 -> j=-3375, discriminant -7, conductor 7, |E(F7)|=8, X0(7), vol=8*pi/3"

activeSmallDiscriminantUniquenessLabel : String
activeSmallDiscriminantUniquenessLabel =
  "The active class-number-1 discriminants with |D|<=7 are exactly -4, -3, and -7"

sterileSmallDiscriminantWindowLabel : String
sterileSmallDiscriminantWindowLabel =
  "With |D|<=8, -8 is the fourth class-number-1 discriminant and is recorded only as a sterile generation candidate"

record HeegnerLaneAssignment : Set where
  field
    lane :
      HeegnerPrimeLane

    jInvariantAbs :
      Nat

    jInvariantLabel :
      String

    discriminant :
      HeegnerDiscriminant

    discriminantLabel :
      String

    conductor :
      Nat

    finiteFieldPointCount :
      Nat

    modularCurve :
      String

    volumeNumerator :
      Nat

    volumeDenominator :
      Nat

    volumeSymbol :
      String

    assignmentStatement :
      String

open HeegnerLaneAssignment public

p2HeegnerLaneAssignment :
  HeegnerLaneAssignment
p2HeegnerLaneAssignment =
  record
    { lane =
        p2
    ; jInvariantAbs =
        1728
    ; jInvariantLabel =
        "1728"
    ; discriminant =
        D-4
    ; discriminantLabel =
        "-4"
    ; conductor =
        4
    ; finiteFieldPointCount =
        3
    ; modularCurve =
        "X0(4)"
    ; volumeNumerator =
        2
    ; volumeDenominator =
        1
    ; volumeSymbol =
        "pi"
    ; assignmentStatement =
        p2AssignmentLabel
    }

p3HeegnerLaneAssignment :
  HeegnerLaneAssignment
p3HeegnerLaneAssignment =
  record
    { lane =
        p3
    ; jInvariantAbs =
        0
    ; jInvariantLabel =
        "0"
    ; discriminant =
        D-3
    ; discriminantLabel =
        "-3"
    ; conductor =
        3
    ; finiteFieldPointCount =
        4
    ; modularCurve =
        "X0(3)"
    ; volumeNumerator =
        4
    ; volumeDenominator =
        3
    ; volumeSymbol =
        "pi"
    ; assignmentStatement =
        p3AssignmentLabel
    }

p5HeegnerLaneAssignment :
  HeegnerLaneAssignment
p5HeegnerLaneAssignment =
  record
    { lane =
        p5
    ; jInvariantAbs =
        3375
    ; jInvariantLabel =
        "-3375"
    ; discriminant =
        D-7
    ; discriminantLabel =
        "-7"
    ; conductor =
        7
    ; finiteFieldPointCount =
        8
    ; modularCurve =
        "X0(7)"
    ; volumeNumerator =
        8
    ; volumeDenominator =
        3
    ; volumeSymbol =
        "pi"
    ; assignmentStatement =
        p5AssignmentLabel
    }

canonicalHeegnerLaneAssignments :
  List HeegnerLaneAssignment
canonicalHeegnerLaneAssignments =
  p2HeegnerLaneAssignment
  ∷ p3HeegnerLaneAssignment
  ∷ p5HeegnerLaneAssignment
  ∷ []

record HeegnerLaneAssignmentReceipt : Setω where
  field
    status :
      HeegnerLaneAssignmentStatus

    citationAuthorities :
      List HeegnerLaneCitationAuthority

    citationAuthoritiesAreCanonical :
      citationAuthorities ≡ canonicalHeegnerLaneCitationAuthorities

    lanes :
      List HeegnerPrimeLane

    lanesAreCanonical :
      lanes ≡ canonicalHeegnerPrimeLanes

    assignments :
      List HeegnerLaneAssignment

    assignmentsAreCanonical :
      assignments ≡ canonicalHeegnerLaneAssignments

    p2Assignment :
      HeegnerLaneAssignment

    p2AssignmentIsCanonical :
      p2Assignment ≡ p2HeegnerLaneAssignment

    p2JInvariantIs1728 :
      jInvariantAbs p2Assignment ≡ 1728

    p2DiscriminantIsMinusFour :
      discriminant p2Assignment ≡ D-4

    p2ConductorIsFour :
      conductor p2Assignment ≡ 4

    p2EF2CountIsThree :
      finiteFieldPointCount p2Assignment ≡ 3

    p2ModularCurveIsX04 :
      modularCurve p2Assignment ≡ "X0(4)"

    p2VolumeIsTwoPi :
      volumeNumerator p2Assignment ≡ 2

    p3Assignment :
      HeegnerLaneAssignment

    p3AssignmentIsCanonical :
      p3Assignment ≡ p3HeegnerLaneAssignment

    p3JInvariantIsZero :
      jInvariantAbs p3Assignment ≡ 0

    p3DiscriminantIsMinusThree :
      discriminant p3Assignment ≡ D-3

    p3ConductorIsThree :
      conductor p3Assignment ≡ 3

    p3EF3CountIsFour :
      finiteFieldPointCount p3Assignment ≡ 4

    p3ModularCurveIsX03 :
      modularCurve p3Assignment ≡ "X0(3)"

    p3VolumeNumeratorIsFour :
      volumeNumerator p3Assignment ≡ 4

    p3VolumeDenominatorIsThree :
      volumeDenominator p3Assignment ≡ 3

    p5Assignment :
      HeegnerLaneAssignment

    p5AssignmentIsCanonical :
      p5Assignment ≡ p5HeegnerLaneAssignment

    p5JInvariantAbsIs3375 :
      jInvariantAbs p5Assignment ≡ 3375

    p5JInvariantLabelIsNegative3375 :
      jInvariantLabel p5Assignment ≡ "-3375"

    p5DiscriminantIsMinusSeven :
      discriminant p5Assignment ≡ D-7

    p5ConductorIsSeven :
      conductor p5Assignment ≡ 7

    p5EF7CountIsEight :
      finiteFieldPointCount p5Assignment ≡ 8

    p5ModularCurveIsX07 :
      modularCurve p5Assignment ≡ "X0(7)"

    p5VolumeNumeratorIsEight :
      volumeNumerator p5Assignment ≡ 8

    p5VolumeDenominatorIsThree :
      volumeDenominator p5Assignment ≡ 3

    activeClassNumberOneDiscriminantsAbsLe7 :
      List HeegnerDiscriminant

    activeClassNumberOneDiscriminantsAbsLe7AreCanonical :
      activeClassNumberOneDiscriminantsAbsLe7
      ≡
      activeSmallClassNumberOneDiscriminantsAbsLe7

    classNumberOneDiscriminantsAbsLe8 :
      List HeegnerDiscriminant

    classNumberOneDiscriminantsAbsLe8AreCanonical :
      classNumberOneDiscriminantsAbsLe8
      ≡
      smallClassNumberOneDiscriminantsAbsLe8

    sterileCandidateDiscriminantsAbsLe8 :
      List HeegnerDiscriminant

    sterileCandidateDiscriminantsAbsLe8AreCanonical :
      sterileCandidateDiscriminantsAbsLe8
      ≡
      sterileSmallClassNumberOneDiscriminantsAbsLe8

    activeSmallDiscriminantUniqueness :
      String

    activeSmallDiscriminantUniquenessIsCanonical :
      activeSmallDiscriminantUniqueness
      ≡
      activeSmallDiscriminantUniquenessLabel

    sterileSmallDiscriminantWindow :
      String

    sterileSmallDiscriminantWindowIsCanonical :
      sterileSmallDiscriminantWindow
      ≡
      sterileSmallDiscriminantWindowLabel

    dMinusEightSterileGenerationCandidate :
      Bool

    dMinusEightSterileGenerationCandidateIsTrue :
      dMinusEightSterileGenerationCandidate ≡ true

    dMinusEightPromotedToActiveLane :
      Bool

    dMinusEightPromotedToActiveLaneIsFalse :
      dMinusEightPromotedToActiveLane ≡ false

    firstPrinciplesDerivationConstructed :
      Bool

    firstPrinciplesDerivationConstructedIsFalse :
      firstPrinciplesDerivationConstructed ≡ false

    fullPromotionConstructed :
      Bool

    fullPromotionConstructedIsFalse :
      fullPromotionConstructed ≡ false

    consequences :
      List HeegnerLaneConsequence

    consequencesAreCanonical :
      consequences ≡ canonicalHeegnerLaneConsequences

    blockers :
      List HeegnerLaneBlocker

    blockersAreCanonical :
      blockers ≡ canonicalHeegnerLaneBlockers

    receiptBoundary :
      List String

open HeegnerLaneAssignmentReceipt public

canonicalHeegnerLaneAssignmentReceipt :
  HeegnerLaneAssignmentReceipt
canonicalHeegnerLaneAssignmentReceipt =
  record
    { status =
        heegnerLaneAssignmentsRecordedNoPromotion
    ; citationAuthorities =
        canonicalHeegnerLaneCitationAuthorities
    ; citationAuthoritiesAreCanonical =
        refl
    ; lanes =
        canonicalHeegnerPrimeLanes
    ; lanesAreCanonical =
        refl
    ; assignments =
        canonicalHeegnerLaneAssignments
    ; assignmentsAreCanonical =
        refl
    ; p2Assignment =
        p2HeegnerLaneAssignment
    ; p2AssignmentIsCanonical =
        refl
    ; p2JInvariantIs1728 =
        refl
    ; p2DiscriminantIsMinusFour =
        refl
    ; p2ConductorIsFour =
        refl
    ; p2EF2CountIsThree =
        refl
    ; p2ModularCurveIsX04 =
        refl
    ; p2VolumeIsTwoPi =
        refl
    ; p3Assignment =
        p3HeegnerLaneAssignment
    ; p3AssignmentIsCanonical =
        refl
    ; p3JInvariantIsZero =
        refl
    ; p3DiscriminantIsMinusThree =
        refl
    ; p3ConductorIsThree =
        refl
    ; p3EF3CountIsFour =
        refl
    ; p3ModularCurveIsX03 =
        refl
    ; p3VolumeNumeratorIsFour =
        refl
    ; p3VolumeDenominatorIsThree =
        refl
    ; p5Assignment =
        p5HeegnerLaneAssignment
    ; p5AssignmentIsCanonical =
        refl
    ; p5JInvariantAbsIs3375 =
        refl
    ; p5JInvariantLabelIsNegative3375 =
        refl
    ; p5DiscriminantIsMinusSeven =
        refl
    ; p5ConductorIsSeven =
        refl
    ; p5EF7CountIsEight =
        refl
    ; p5ModularCurveIsX07 =
        refl
    ; p5VolumeNumeratorIsEight =
        refl
    ; p5VolumeDenominatorIsThree =
        refl
    ; activeClassNumberOneDiscriminantsAbsLe7 =
        activeSmallClassNumberOneDiscriminantsAbsLe7
    ; activeClassNumberOneDiscriminantsAbsLe7AreCanonical =
        refl
    ; classNumberOneDiscriminantsAbsLe8 =
        smallClassNumberOneDiscriminantsAbsLe8
    ; classNumberOneDiscriminantsAbsLe8AreCanonical =
        refl
    ; sterileCandidateDiscriminantsAbsLe8 =
        sterileSmallClassNumberOneDiscriminantsAbsLe8
    ; sterileCandidateDiscriminantsAbsLe8AreCanonical =
        refl
    ; activeSmallDiscriminantUniqueness =
        activeSmallDiscriminantUniquenessLabel
    ; activeSmallDiscriminantUniquenessIsCanonical =
        refl
    ; sterileSmallDiscriminantWindow =
        sterileSmallDiscriminantWindowLabel
    ; sterileSmallDiscriminantWindowIsCanonical =
        refl
    ; dMinusEightSterileGenerationCandidate =
        true
    ; dMinusEightSterileGenerationCandidateIsTrue =
        refl
    ; dMinusEightPromotedToActiveLane =
        false
    ; dMinusEightPromotedToActiveLaneIsFalse =
        refl
    ; firstPrinciplesDerivationConstructed =
        false
    ; firstPrinciplesDerivationConstructedIsFalse =
        refl
    ; fullPromotionConstructed =
        false
    ; fullPromotionConstructedIsFalse =
        refl
    ; consequences =
        canonicalHeegnerLaneConsequences
    ; consequencesAreCanonical =
        refl
    ; blockers =
        canonicalHeegnerLaneBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "p2 is recorded as the Gaussian CM lane: j=1728, discriminant -4, conductor 4, |E(F2)|=3, X0(4), vol=2*pi"
        ∷ "p3 is recorded as the Eisenstein CM lane: j=0, discriminant -3, conductor 3, |E(F3)|=4, X0(3), vol=4*pi/3"
        ∷ "p5 is recorded as the Heegner-seven lane: j=-3375, discriminant -7, conductor 7, |E(F7)|=8, X0(7), vol=8*pi/3"
        ∷ "The active small class-number-1 discriminant window |D|<=7 is exactly {-4,-3,-7}"
        ∷ "For |D|<=8, -8 is also class-number-1 but is recorded only as a sterile generation candidate"
        ∷ "firstPrinciplesDerivationConstructed remains false"
        ∷ "fullPromotionConstructed remains false"
        ∷ []
    }

heegnerLaneReceiptRecordsP2Assignment :
  assignmentStatement
    (p2Assignment canonicalHeegnerLaneAssignmentReceipt)
  ≡
  p2AssignmentLabel
heegnerLaneReceiptRecordsP2Assignment =
  refl

heegnerLaneReceiptRecordsP3Assignment :
  assignmentStatement
    (p3Assignment canonicalHeegnerLaneAssignmentReceipt)
  ≡
  p3AssignmentLabel
heegnerLaneReceiptRecordsP3Assignment =
  refl

heegnerLaneReceiptRecordsP5Assignment :
  assignmentStatement
    (p5Assignment canonicalHeegnerLaneAssignmentReceipt)
  ≡
  p5AssignmentLabel
heegnerLaneReceiptRecordsP5Assignment =
  refl

heegnerLaneReceiptRecordsActiveSmallDiscriminants :
  activeClassNumberOneDiscriminantsAbsLe7
    canonicalHeegnerLaneAssignmentReceipt
  ≡
  activeSmallClassNumberOneDiscriminantsAbsLe7
heegnerLaneReceiptRecordsActiveSmallDiscriminants =
  refl

heegnerLaneReceiptRecordsSterileDMinusEight :
  sterileCandidateDiscriminantsAbsLe8
    canonicalHeegnerLaneAssignmentReceipt
  ≡
  sterileSmallClassNumberOneDiscriminantsAbsLe8
heegnerLaneReceiptRecordsSterileDMinusEight =
  refl

heegnerLaneReceiptKeepsFirstPrinciplesFalse :
  firstPrinciplesDerivationConstructed
    canonicalHeegnerLaneAssignmentReceipt
  ≡
  false
heegnerLaneReceiptKeepsFirstPrinciplesFalse =
  refl

heegnerLaneReceiptKeepsFullPromotionFalse :
  fullPromotionConstructed canonicalHeegnerLaneAssignmentReceipt
  ≡
  false
heegnerLaneReceiptKeepsFullPromotionFalse =
  refl
