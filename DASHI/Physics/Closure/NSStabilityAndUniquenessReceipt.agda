module DASHI.Physics.Closure.NSStabilityAndUniquenessReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes H^{11/8} stability and uniqueness gap receipt.
--
-- This receipt records the standard conditional uniqueness route:
-- subtract two solutions, estimate the difference equation in a lower energy
-- norm, use a global H^{11/8} bound in the coefficient, and close uniqueness
-- by Gronwall.  The receipt also records the obstruction: deriving the
-- global H^{11/8} bound from uniqueness would be circular.  The standard way
-- out is to obtain existence and stability together by a contraction mapping
-- or equivalent fixed-point scheme before applying Gronwall.  This file is a
-- candidate/gap ledger only; it does not promote Clay Navier-Stokes, global
-- regularity, or a terminal theorem.

data NSStabilityUniquenessStatus : Set where
  candidate :
    NSStabilityUniquenessStatus

  gap :
    NSStabilityUniquenessStatus

canonicalNSStabilityUniquenessStatus :
  List NSStabilityUniquenessStatus
canonicalNSStabilityUniquenessStatus =
  candidate
  ∷ gap
  ∷ []

data NSStabilityUniquenessIngredient : Set where
  differenceEquationEstimate :
    NSStabilityUniquenessIngredient

  gronwallUniquenessUsingGlobalH118Bound :
    NSStabilityUniquenessIngredient

  circularDependencyRecorded :
    NSStabilityUniquenessIngredient

  contractionMappingResolution :
    NSStabilityUniquenessIngredient

canonicalNSStabilityUniquenessIngredients :
  List NSStabilityUniquenessIngredient
canonicalNSStabilityUniquenessIngredients =
  differenceEquationEstimate
  ∷ gronwallUniquenessUsingGlobalH118Bound
  ∷ circularDependencyRecorded
  ∷ contractionMappingResolution
  ∷ []

data NSStabilityUniquenessGap : Set where
  globalH118BoundCannotBeDerivedFromUniqueness :
    NSStabilityUniquenessGap

  contractionMappingProofStillRequired :
    NSStabilityUniquenessGap

canonicalNSStabilityUniquenessGaps :
  List NSStabilityUniquenessGap
canonicalNSStabilityUniquenessGaps =
  globalH118BoundCannotBeDerivedFromUniqueness
  ∷ contractionMappingProofStillRequired
  ∷ []

data NSStabilityUniquenessPromotion : Set where

nsStabilityUniquenessPromotionImpossibleHere :
  NSStabilityUniquenessPromotion →
  ⊥
nsStabilityUniquenessPromotionImpossibleHere ()

h118SobolevNumerator :
  Nat
h118SobolevNumerator =
  11

h118SobolevDenominator :
  Nat
h118SobolevDenominator =
  8

differenceEquationEstimateFormula :
  String
differenceEquationEstimateFormula =
  "d/dt ||w||_L2^2 + nu ||nabla w||_L2^2 <= C ||u||_H^{11/8}^alpha ||w||_L2^2"

gronwallUniquenessFormula :
  String
gronwallUniquenessFormula =
  "global H^{11/8} bound plus zero initial difference implies w(t) = 0 by Gronwall"

circularDependencyStatement :
  String
circularDependencyStatement =
  "Uniqueness cannot be used to obtain the global H^{11/8} bound that the uniqueness estimate itself requires."

contractionMappingResolutionStatement :
  String
contractionMappingResolutionStatement =
  "Resolve the circle by constructing existence and stability in a closed H^{11/8} ball via contraction mapping, then apply Gronwall for uniqueness."

nsStabilityUniquenessStatement :
  String
nsStabilityUniquenessStatement =
  "Candidate/gap receipt: the difference equation gives a Gronwall uniqueness route assuming a global H^{11/8} bound; using uniqueness to obtain that bound is circular; the standard non-circular resolution is a contraction-mapping construction of existence and stability before the uniqueness step.  No Clay, global regularity, or terminal promotion is made."

record NSStabilityAndUniquenessReceipt : Setω where
  field
    status :
      List NSStabilityUniquenessStatus

    statusIsCanonical :
      status ≡ canonicalNSStabilityUniquenessStatus

    ingredients :
      List NSStabilityUniquenessIngredient

    ingredientsAreCanonical :
      ingredients ≡ canonicalNSStabilityUniquenessIngredients

    gaps :
      List NSStabilityUniquenessGap

    gapsAreCanonical :
      gaps ≡ canonicalNSStabilityUniquenessGaps

    h118Numerator :
      Nat

    h118NumeratorIs11 :
      h118Numerator ≡ h118SobolevNumerator

    h118Denominator :
      Nat

    h118DenominatorIs8 :
      h118Denominator ≡ h118SobolevDenominator

    differenceEquationEstimateRecorded :
      Bool

    differenceEquationEstimateRecordedIsTrue :
      differenceEquationEstimateRecorded ≡ true

    differenceEstimateFormula :
      String

    differenceEstimateFormulaIsCanonical :
      differenceEstimateFormula ≡ differenceEquationEstimateFormula

    globalH118BoundAssumedForUniqueness :
      Bool

    globalH118BoundAssumedForUniquenessIsTrue :
      globalH118BoundAssumedForUniqueness ≡ true

    gronwallUniquenessRecorded :
      Bool

    gronwallUniquenessRecordedIsTrue :
      gronwallUniquenessRecorded ≡ true

    gronwallFormula :
      String

    gronwallFormulaIsCanonical :
      gronwallFormula ≡ gronwallUniquenessFormula

    uniquenessFromZeroInitialDifference :
      Bool

    uniquenessFromZeroInitialDifferenceIsCandidate :
      uniquenessFromZeroInitialDifference ≡ true

    circularDependencyDetected :
      Bool

    circularDependencyDetectedIsTrue :
      circularDependencyDetected ≡ true

    circularDependencyText :
      String

    circularDependencyTextIsCanonical :
      circularDependencyText ≡ circularDependencyStatement

    contractionMappingResolutionRequired :
      Bool

    contractionMappingResolutionRequiredIsTrue :
      contractionMappingResolutionRequired ≡ true

    contractionMappingResolutionText :
      String

    contractionMappingResolutionTextIsCanonical :
      contractionMappingResolutionText ≡ contractionMappingResolutionStatement

    contractionMappingConstructedHere :
      Bool

    contractionMappingConstructedHereIsFalse :
      contractionMappingConstructedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsStabilityUniquenessStatement

    promotionFlags :
      List NSStabilityUniquenessPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSStabilityAndUniquenessReceipt public

canonicalNSStabilityAndUniquenessReceipt :
  NSStabilityAndUniquenessReceipt
canonicalNSStabilityAndUniquenessReceipt =
  record
    { status =
        canonicalNSStabilityUniquenessStatus
    ; statusIsCanonical =
        refl
    ; ingredients =
        canonicalNSStabilityUniquenessIngredients
    ; ingredientsAreCanonical =
        refl
    ; gaps =
        canonicalNSStabilityUniquenessGaps
    ; gapsAreCanonical =
        refl
    ; h118Numerator =
        11
    ; h118NumeratorIs11 =
        refl
    ; h118Denominator =
        8
    ; h118DenominatorIs8 =
        refl
    ; differenceEquationEstimateRecorded =
        true
    ; differenceEquationEstimateRecordedIsTrue =
        refl
    ; differenceEstimateFormula =
        differenceEquationEstimateFormula
    ; differenceEstimateFormulaIsCanonical =
        refl
    ; globalH118BoundAssumedForUniqueness =
        true
    ; globalH118BoundAssumedForUniquenessIsTrue =
        refl
    ; gronwallUniquenessRecorded =
        true
    ; gronwallUniquenessRecordedIsTrue =
        refl
    ; gronwallFormula =
        gronwallUniquenessFormula
    ; gronwallFormulaIsCanonical =
        refl
    ; uniquenessFromZeroInitialDifference =
        true
    ; uniquenessFromZeroInitialDifferenceIsCandidate =
        refl
    ; circularDependencyDetected =
        true
    ; circularDependencyDetectedIsTrue =
        refl
    ; circularDependencyText =
        circularDependencyStatement
    ; circularDependencyTextIsCanonical =
        refl
    ; contractionMappingResolutionRequired =
        true
    ; contractionMappingResolutionRequiredIsTrue =
        refl
    ; contractionMappingResolutionText =
        contractionMappingResolutionStatement
    ; contractionMappingResolutionTextIsCanonical =
        refl
    ; contractionMappingConstructedHere =
        false
    ; contractionMappingConstructedHereIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; statement =
        nsStabilityUniquenessStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "status = candidate/gap"
        ∷ "difference equation estimate recorded"
        ∷ "uniqueness by Gronwall requires global H^{11/8} bound"
        ∷ "circular dependency recorded: uniqueness cannot supply its own bound"
        ∷ "standard resolution recorded: contraction mapping before Gronwall"
        ∷ "contractionMappingConstructedHere = false"
        ∷ "No Clay Navier-Stokes, global regularity, or terminal promotion is made"
        ∷ []
    }

canonicalNSStabilityUniquenessStatusIsCandidateGap :
  status canonicalNSStabilityAndUniquenessReceipt
  ≡
  canonicalNSStabilityUniquenessStatus
canonicalNSStabilityUniquenessStatusIsCandidateGap =
  refl

canonicalDifferenceEquationEstimateRecorded :
  differenceEquationEstimateRecorded canonicalNSStabilityAndUniquenessReceipt
  ≡
  true
canonicalDifferenceEquationEstimateRecorded =
  refl

canonicalGlobalH118BoundAssumedForUniqueness :
  globalH118BoundAssumedForUniqueness canonicalNSStabilityAndUniquenessReceipt
  ≡
  true
canonicalGlobalH118BoundAssumedForUniqueness =
  refl

canonicalCircularDependencyDetected :
  circularDependencyDetected canonicalNSStabilityAndUniquenessReceipt
  ≡
  true
canonicalCircularDependencyDetected =
  refl

canonicalContractionMappingRequired :
  contractionMappingResolutionRequired canonicalNSStabilityAndUniquenessReceipt
  ≡
  true
canonicalContractionMappingRequired =
  refl

canonicalContractionMappingNotConstructedHere :
  contractionMappingConstructedHere canonicalNSStabilityAndUniquenessReceipt
  ≡
  false
canonicalContractionMappingNotConstructedHere =
  refl

canonicalNSStabilityUniquenessNoClayPromotion :
  clayNavierStokesPromoted canonicalNSStabilityAndUniquenessReceipt
  ≡
  false
canonicalNSStabilityUniquenessNoClayPromotion =
  refl

canonicalNSStabilityUniquenessNoTerminalPromotion :
  terminalClaimPromoted canonicalNSStabilityAndUniquenessReceipt
  ≡
  false
canonicalNSStabilityUniquenessNoTerminalPromotion =
  refl

nsStabilityUniquenessNoPromotion :
  NSStabilityUniquenessPromotion →
  ⊥
nsStabilityUniquenessNoPromotion =
  nsStabilityUniquenessPromotionImpossibleHere
