module DASHI.Physics.Closure.YMLatticeAnimalCountingBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- YM lattice-animal counting bound receipt.
--
-- This module records the d=4 lattice-animal counting surface used by the
-- weak-coupling polymer proof.  It captures the Cayley/tree-envelope shape,
-- the standard N_n <= (8e)^n counting statement, the local dependency
-- inventory, and the fail-closed boundary that prevents promotion to any
-- continuum/KP/Clay claim.

data YMLatticeAnimalCountingStatus : Set where
  latticeAnimalCountingBoundReceiptedNoPromotion :
    YMLatticeAnimalCountingStatus

data YMLatticeAnimalCountingSurface : Set where
  rootedAnimalsOnZ4 :
    YMLatticeAnimalCountingSurface

  cayleyTreeEnvelopeForRootedAnimals :
    YMLatticeAnimalCountingSurface

  stirlingEFactorEnvelope :
    YMLatticeAnimalCountingSurface

  degreeFourNearestNeighbourGraph :
    YMLatticeAnimalCountingSurface

  exactEightETargetSurface :
    YMLatticeAnimalCountingSurface

canonicalYMLatticeAnimalCountingSurface :
  List YMLatticeAnimalCountingSurface
canonicalYMLatticeAnimalCountingSurface =
  rootedAnimalsOnZ4
  ∷ cayleyTreeEnvelopeForRootedAnimals
  ∷ stirlingEFactorEnvelope
  ∷ degreeFourNearestNeighbourGraph
  ∷ exactEightETargetSurface
  ∷ []

data YMLatticeAnimalCountingIngredient : Set where
  dimensionFourSpecialization :
    YMLatticeAnimalCountingIngredient

  rootedAnimalEnumerationBySize :
    YMLatticeAnimalCountingIngredient

  cayleyRootedTreeOvercount :
    YMLatticeAnimalCountingIngredient

  localDegreeEightBranching :
    YMLatticeAnimalCountingIngredient

  stirlingExponentialEnvelope :
    YMLatticeAnimalCountingIngredient

  weakCouplingPolymerContext :
    YMLatticeAnimalCountingIngredient

  boundStatementRecordedAsSurface :
    YMLatticeAnimalCountingIngredient

canonicalYMLatticeAnimalCountingIngredients :
  List YMLatticeAnimalCountingIngredient
canonicalYMLatticeAnimalCountingIngredients =
  dimensionFourSpecialization
  ∷ rootedAnimalEnumerationBySize
  ∷ cayleyRootedTreeOvercount
  ∷ localDegreeEightBranching
  ∷ stirlingExponentialEnvelope
  ∷ weakCouplingPolymerContext
  ∷ boundStatementRecordedAsSurface
  ∷ []

data YMLatticeAnimalCountingDependency : Set where
  d4NearestNeighbourAdjacency :
    YMLatticeAnimalCountingDependency

  rootedAnimalRootingScheme :
    YMLatticeAnimalCountingDependency

  cayleyTreeCountingShape :
    YMLatticeAnimalCountingDependency

  stirlingEnvelopeControl :
    YMLatticeAnimalCountingDependency

  polymerWeakCouplingSurface :
    YMLatticeAnimalCountingDependency

  exactEightEBoundSurface :
    YMLatticeAnimalCountingDependency

canonicalYMLatticeAnimalCountingDependencies :
  List YMLatticeAnimalCountingDependency
canonicalYMLatticeAnimalCountingDependencies =
  d4NearestNeighbourAdjacency
  ∷ rootedAnimalRootingScheme
  ∷ cayleyTreeCountingShape
  ∷ stirlingEnvelopeControl
  ∷ polymerWeakCouplingSurface
  ∷ exactEightEBoundSurface
  ∷ []

data YMLatticeAnimalCountingNonClaim : Set where
  noContinuumLimitClaim :
    YMLatticeAnimalCountingNonClaim

  noKPTheoremClaim :
    YMLatticeAnimalCountingNonClaim

  noClayYangMillsPromotion :
    YMLatticeAnimalCountingNonClaim

  noSharpConstantOptimizationClaim :
    YMLatticeAnimalCountingNonClaim

  noProofOfActualPolymerConvergence :
    YMLatticeAnimalCountingNonClaim

canonicalYMLatticeAnimalCountingNonClaims :
  List YMLatticeAnimalCountingNonClaim
canonicalYMLatticeAnimalCountingNonClaims =
  noContinuumLimitClaim
  ∷ noKPTheoremClaim
  ∷ noClayYangMillsPromotion
  ∷ noSharpConstantOptimizationClaim
  ∷ noProofOfActualPolymerConvergence
  ∷ []

data YMLatticeAnimalCountingPromotion : Set where

ymlatticeAnimalCountingPromotionImpossibleHere :
  YMLatticeAnimalCountingPromotion →
  ⊥
ymlatticeAnimalCountingPromotionImpossibleHere ()

four : Nat
four = 4

eight : Nat
eight = 8

countingSurfaceStatement : String
countingSurfaceStatement =
  "In d=4 the lattice-animal surface is recorded through a Cayley/tree envelope on rooted animals, with the standard counting shape N_n <= (8e)^n."

treeEstimateStatement : String
treeEstimateStatement =
  "The Cayley/tree estimate shape is rooted-animal overcounting by rooted trees, with degree-8 branching and the Stirling e-factor kept explicit."

boundaryStatement : String
boundaryStatement =
  "This receipt is fail-closed: it records the counting surface only, and it does not promote any continuum, KP, or Clay Yang-Mills claim."

receiptSummary : String
receiptSummary =
  "YM5 lattice-animal counting receipt for d=4: rooted trees, degree-8 branching, and the N_n <= (8e)^n bound surface are recorded without promotion."

record YMLatticeAnimalCountingBoundReceipt : Setω where
  field
    status :
      YMLatticeAnimalCountingStatus

    statusIsCanonical :
      status ≡ latticeAnimalCountingBoundReceiptedNoPromotion

    dimension :
      Nat

    dimensionIsFour :
      dimension ≡ four

    nearestNeighbourDegree :
      Nat

    nearestNeighbourDegreeIsEight :
      nearestNeighbourDegree ≡ eight

    countingSurface :
      List YMLatticeAnimalCountingSurface

    countingSurfaceIsCanonical :
      countingSurface ≡ canonicalYMLatticeAnimalCountingSurface

    ingredients :
      List YMLatticeAnimalCountingIngredient

    ingredientsAreCanonical :
      ingredients ≡ canonicalYMLatticeAnimalCountingIngredients

    dependencyInventory :
      List YMLatticeAnimalCountingDependency

    dependencyInventoryAreCanonical :
      dependencyInventory ≡ canonicalYMLatticeAnimalCountingDependencies

    countingSurfaceRecorded :
      Bool

    countingSurfaceRecordedIsTrue :
      countingSurfaceRecorded ≡ true

    treeEstimatePromoted :
      Bool

    treeEstimatePromotedIsFalse :
      treeEstimatePromoted ≡ false

    boundPromoted :
      Bool

    boundPromotedIsFalse :
      boundPromoted ≡ false

    continuumPromoted :
      Bool

    continuumPromotedIsFalse :
      continuumPromoted ≡ false

    kpPromoted :
      Bool

    kpPromotedIsFalse :
      kpPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    nonClaims :
      List YMLatticeAnimalCountingNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMLatticeAnimalCountingNonClaims

    countingSurfaceStatementRecorded :
      String

    countingSurfaceStatementRecordedIsCanonical :
      countingSurfaceStatementRecorded ≡ countingSurfaceStatement

    treeEstimateStatementRecorded :
      String

    treeEstimateStatementRecordedIsCanonical :
      treeEstimateStatementRecorded ≡ treeEstimateStatement

    boundaryStatementRecorded :
      String

    boundaryStatementRecordedIsCanonical :
      boundaryStatementRecorded ≡ boundaryStatement

    summary :
      String

    summaryIsCanonical :
      summary ≡ receiptSummary

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡
      (
        "No continuum-limit claim follows from the counting receipt."
        ∷ "No KP theorem claim follows from the counting receipt."
        ∷ "No Clay Yang-Mills promotion follows from the counting receipt."
        ∷ "The Cayley/tree estimate shape is recorded only as a counting envelope."
        ∷ "The exact N_n <= (8e)^n statement is a non-promoting surface entry."
        ∷ []
      )

    noPromotionPossibleHere :
      YMLatticeAnimalCountingPromotion →
      ⊥

open YMLatticeAnimalCountingBoundReceipt public

canonicalYMLatticeAnimalCountingBoundReceipt :
  YMLatticeAnimalCountingBoundReceipt
canonicalYMLatticeAnimalCountingBoundReceipt =
  record
    { status =
        latticeAnimalCountingBoundReceiptedNoPromotion
    ; statusIsCanonical =
        refl
    ; dimension =
        four
    ; dimensionIsFour =
        refl
    ; nearestNeighbourDegree =
        eight
    ; nearestNeighbourDegreeIsEight =
        refl
    ; countingSurface =
        canonicalYMLatticeAnimalCountingSurface
    ; countingSurfaceIsCanonical =
        refl
    ; ingredients =
        canonicalYMLatticeAnimalCountingIngredients
    ; ingredientsAreCanonical =
        refl
    ; dependencyInventory =
        canonicalYMLatticeAnimalCountingDependencies
    ; dependencyInventoryAreCanonical =
        refl
    ; countingSurfaceRecorded =
        true
    ; countingSurfaceRecordedIsTrue =
        refl
    ; treeEstimatePromoted =
        false
    ; treeEstimatePromotedIsFalse =
        refl
    ; boundPromoted =
        false
    ; boundPromotedIsFalse =
        refl
    ; continuumPromoted =
        false
    ; continuumPromotedIsFalse =
        refl
    ; kpPromoted =
        false
    ; kpPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; nonClaims =
        canonicalYMLatticeAnimalCountingNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; countingSurfaceStatementRecorded =
        countingSurfaceStatement
    ; countingSurfaceStatementRecordedIsCanonical =
        refl
    ; treeEstimateStatementRecorded =
        treeEstimateStatement
    ; treeEstimateStatementRecordedIsCanonical =
        refl
    ; boundaryStatementRecorded =
        boundaryStatement
    ; boundaryStatementRecordedIsCanonical =
        refl
    ; summary =
        receiptSummary
    ; summaryIsCanonical =
        refl
    ; receiptBoundary =
        "No continuum-limit claim follows from the counting receipt."
        ∷ "No KP theorem claim follows from the counting receipt."
        ∷ "No Clay Yang-Mills promotion follows from the counting receipt."
        ∷ "The Cayley/tree estimate shape is recorded only as a counting envelope."
        ∷ "The exact N_n <= (8e)^n statement is a non-promoting surface entry."
        ∷ []
    ; receiptBoundaryIsCanonical =
        refl
    ; noPromotionPossibleHere =
        ymlatticeAnimalCountingPromotionImpossibleHere
    }

ymlatticeAnimalCountingBoundKeepsContinuumFalse :
  continuumPromoted canonicalYMLatticeAnimalCountingBoundReceipt ≡ false
ymlatticeAnimalCountingBoundKeepsContinuumFalse = refl

ymlatticeAnimalCountingBoundKeepsKPFalse :
  kpPromoted canonicalYMLatticeAnimalCountingBoundReceipt ≡ false
ymlatticeAnimalCountingBoundKeepsKPFalse = refl

ymlatticeAnimalCountingBoundKeepsClayFalse :
  clayPromoted canonicalYMLatticeAnimalCountingBoundReceipt ≡ false
ymlatticeAnimalCountingBoundKeepsClayFalse = refl
