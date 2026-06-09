module DASHI.Physics.Closure.DistributedTensionFieldReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Distributed tension field receipt.
--
-- This receipt records social/dialectical bookkeeping only.  Tension is
-- typed as a distributed constraint field carried across a braid, not as a
-- scalar pressure.  The head/source determinant asks where the braid is
-- going; the tail/sink determinant asks what history must remain coherent;
-- braid transport maintains the negotiated middle tension.
--
-- No physics theorem, continuum theorem, Navier-Stokes theorem, Yang-Mills
-- theorem, Clay claim, or terminal promotion is introduced here.

data DistributedTensionFieldStatus : Set where
  distributedTensionFieldRecorded_bookkeepingOnly :
    DistributedTensionFieldStatus

data TensionFieldKind : Set where
  distributedConstraintField :
    TensionFieldKind

data ScalarPressureReading : Set where

scalarPressureReadingImpossibleHere :
  ScalarPressureReading →
  ⊥
scalarPressureReadingImpossibleHere ()

data TensionDeterminant : Set where
  headSourceAsksWhereBraidIsGoing :
    TensionDeterminant

  tailSinkAsksWhatHistoryMustRemainCoherent :
    TensionDeterminant

  braidTransportMaintainsMiddleTension :
    TensionDeterminant

canonicalTensionDeterminants :
  List TensionDeterminant
canonicalTensionDeterminants =
  headSourceAsksWhereBraidIsGoing
  ∷ tailSinkAsksWhatHistoryMustRemainCoherent
  ∷ braidTransportMaintainsMiddleTension
  ∷ []

data SweetgrassBraidConstraint : Set where
  tooLooseCollapses :
    SweetgrassBraidConstraint

  tooTightSnaps :
    SweetgrassBraidConstraint

  stableBraidExistsInNegotiatedMiddle :
    SweetgrassBraidConstraint

canonicalSweetgrassBraidConstraints :
  List SweetgrassBraidConstraint
canonicalSweetgrassBraidConstraints =
  tooLooseCollapses
  ∷ tooTightSnaps
  ∷ stableBraidExistsInNegotiatedMiddle
  ∷ []

data TensionBookkeepingBoundary : Set where
  socialDialecticFormalismOnly :
    TensionBookkeepingBoundary

  noPhysicsTheorem :
    TensionBookkeepingBoundary

  noContinuumTheorem :
    TensionBookkeepingBoundary

  noClayPromotion :
    TensionBookkeepingBoundary

  noTerminalPromotion :
    TensionBookkeepingBoundary

canonicalTensionBookkeepingBoundaries :
  List TensionBookkeepingBoundary
canonicalTensionBookkeepingBoundaries =
  socialDialecticFormalismOnly
  ∷ noPhysicsTheorem
  ∷ noContinuumTheorem
  ∷ noClayPromotion
  ∷ noTerminalPromotion
  ∷ []

data DistributedTensionPromotion : Set where

distributedTensionPromotionImpossibleHere :
  DistributedTensionPromotion →
  ⊥
distributedTensionPromotionImpossibleHere ()

tensionFieldStatement :
  String
tensionFieldStatement =
  "Tension is recorded as a distributed constraint field across the braid, not scalar pressure."

determinantStatement :
  String
determinantStatement =
  "Head/source asks where the braid is going; tail/sink asks what history must remain coherent; braid transport maintains middle tension."

sweetgrassStatement :
  String
sweetgrassStatement =
  "Sweetgrass braid constraint: too loose collapses, too tight snaps, and stable braid exists in the negotiated middle."

boundaryStatement :
  String
boundaryStatement =
  "This is social/dialectical formalism bookkeeping only: no physics theorem, no continuum theorem, no Clay theorem, and no terminal promotion."

record DistributedTensionFieldReceipt : Setω where
  field
    status :
      DistributedTensionFieldStatus

    statusIsBookkeepingOnly :
      status ≡ distributedTensionFieldRecorded_bookkeepingOnly

    tensionFieldKind :
      TensionFieldKind

    tensionFieldKindIsDistributedConstraint :
      tensionFieldKind ≡ distributedConstraintField

    scalarPressurePromoted :
      Bool

    scalarPressurePromotedIsFalse :
      scalarPressurePromoted ≡ false

    headSourceDeterminant :
      TensionDeterminant

    headSourceDeterminantIsCanonical :
      headSourceDeterminant ≡ headSourceAsksWhereBraidIsGoing

    tailSinkDeterminant :
      TensionDeterminant

    tailSinkDeterminantIsCanonical :
      tailSinkDeterminant
      ≡
      tailSinkAsksWhatHistoryMustRemainCoherent

    middleTransport :
      TensionDeterminant

    middleTransportIsCanonical :
      middleTransport ≡ braidTransportMaintainsMiddleTension

    determinants :
      List TensionDeterminant

    determinantsAreCanonical :
      determinants ≡ canonicalTensionDeterminants

    sweetgrassConstraints :
      List SweetgrassBraidConstraint

    sweetgrassConstraintsAreCanonical :
      sweetgrassConstraints ≡ canonicalSweetgrassBraidConstraints

    boundaries :
      List TensionBookkeepingBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalTensionBookkeepingBoundaries

    physicsTheoremPromoted :
      Bool

    physicsTheoremPromotedIsFalse :
      physicsTheoremPromoted ≡ false

    continuumTheoremPromoted :
      Bool

    continuumTheoremPromotedIsFalse :
      continuumTheoremPromoted ≡ false

    clayTheoremPromoted :
      Bool

    clayTheoremPromotedIsFalse :
      clayTheoremPromoted ≡ false

    terminalPromotionPromoted :
      Bool

    terminalPromotionPromotedIsFalse :
      terminalPromotionPromoted ≡ false

    promotionFlags :
      List DistributedTensionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    tensionFieldReading :
      String

    tensionFieldReadingIsCanonical :
      tensionFieldReading ≡ tensionFieldStatement

    determinantReading :
      String

    determinantReadingIsCanonical :
      determinantReading ≡ determinantStatement

    sweetgrassReading :
      String

    sweetgrassReadingIsCanonical :
      sweetgrassReading ≡ sweetgrassStatement

    boundaryReading :
      String

    boundaryReadingIsCanonical :
      boundaryReading ≡ boundaryStatement

canonicalDistributedTensionFieldReceipt :
  DistributedTensionFieldReceipt
canonicalDistributedTensionFieldReceipt =
  record
    { status =
        distributedTensionFieldRecorded_bookkeepingOnly
    ; statusIsBookkeepingOnly =
        refl
    ; tensionFieldKind =
        distributedConstraintField
    ; tensionFieldKindIsDistributedConstraint =
        refl
    ; scalarPressurePromoted =
        false
    ; scalarPressurePromotedIsFalse =
        refl
    ; headSourceDeterminant =
        headSourceAsksWhereBraidIsGoing
    ; headSourceDeterminantIsCanonical =
        refl
    ; tailSinkDeterminant =
        tailSinkAsksWhatHistoryMustRemainCoherent
    ; tailSinkDeterminantIsCanonical =
        refl
    ; middleTransport =
        braidTransportMaintainsMiddleTension
    ; middleTransportIsCanonical =
        refl
    ; determinants =
        canonicalTensionDeterminants
    ; determinantsAreCanonical =
        refl
    ; sweetgrassConstraints =
        canonicalSweetgrassBraidConstraints
    ; sweetgrassConstraintsAreCanonical =
        refl
    ; boundaries =
        canonicalTensionBookkeepingBoundaries
    ; boundariesAreCanonical =
        refl
    ; physicsTheoremPromoted =
        false
    ; physicsTheoremPromotedIsFalse =
        refl
    ; continuumTheoremPromoted =
        false
    ; continuumTheoremPromotedIsFalse =
        refl
    ; clayTheoremPromoted =
        false
    ; clayTheoremPromotedIsFalse =
        refl
    ; terminalPromotionPromoted =
        false
    ; terminalPromotionPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; tensionFieldReading =
        tensionFieldStatement
    ; tensionFieldReadingIsCanonical =
        refl
    ; determinantReading =
        determinantStatement
    ; determinantReadingIsCanonical =
        refl
    ; sweetgrassReading =
        sweetgrassStatement
    ; sweetgrassReadingIsCanonical =
        refl
    ; boundaryReading =
        boundaryStatement
    ; boundaryReadingIsCanonical =
        refl
    }

canonicalTensionIsDistributedNotScalar :
  DistributedTensionFieldReceipt.tensionFieldKind
    canonicalDistributedTensionFieldReceipt
  ≡
  distributedConstraintField
canonicalTensionIsDistributedNotScalar =
  refl

canonicalMiddleTensionMaintainedByTransport :
  DistributedTensionFieldReceipt.middleTransport
    canonicalDistributedTensionFieldReceipt
  ≡
  braidTransportMaintainsMiddleTension
canonicalMiddleTensionMaintainedByTransport =
  refl

canonicalSweetgrassNegotiatedMiddle :
  DistributedTensionFieldReceipt.sweetgrassConstraints
    canonicalDistributedTensionFieldReceipt
  ≡
  canonicalSweetgrassBraidConstraints
canonicalSweetgrassNegotiatedMiddle =
  refl

canonicalDistributedTensionClayPromotionIsFalse :
  DistributedTensionFieldReceipt.clayTheoremPromoted
    canonicalDistributedTensionFieldReceipt
  ≡
  false
canonicalDistributedTensionClayPromotionIsFalse =
  refl
