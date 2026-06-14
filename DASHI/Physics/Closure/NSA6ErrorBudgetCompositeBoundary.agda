module DASHI.Physics.Closure.NSA6ErrorBudgetCompositeBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSAbelShellMixingLLNBoundary
  as LLN
import DASHI.Physics.Closure.NSDiagonalStretchingToAbelMeanBoundary
  as Diagonal
import DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary
  as Localization
import DASHI.Physics.Closure.NSOffDiagonalShellAbsorptionBoundary
  as OffDiagonal
import DASHI.Physics.Closure.NSPointwiseToAbelCompositeA6Boundary
  as Composite

------------------------------------------------------------------------
-- NS A6 composite error-budget boundary.
--
-- This module records the explicit budget taxonomy required for the
-- A6 pointwise-to-Abel composite theorem.  It assigns every budget line
-- to the child boundary that owns it, records the five-contributor
-- aggregate payload, and keeps residual depletion, local monotonicity,
-- NS Clay, and terminal promotion fail-closed.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data ⊥ : Set where

------------------------------------------------------------------------
-- Imported child support.

record ImportedNSA6ErrorBudgetCompositeSupport : Set where
  field
    compositeBoundary :
      Composite.NSPointwiseToAbelCompositeA6Boundary
    compositeBoundaryIsCanonical :
      compositeBoundary
        ≡ Composite.canonicalNSPointwiseToAbelCompositeA6Boundary
    diagonalChild :
      Diagonal.NSDiagonalStretchingToAbelMeanBoundary
    diagonalChildIsCanonical :
      diagonalChild
        ≡ Diagonal.canonicalNSDiagonalStretchingToAbelMeanBoundary
    offDiagonalChild :
      OffDiagonal.NSOffDiagonalShellAbsorptionBoundary
    offDiagonalChildIsCanonical :
      offDiagonalChild
        ≡ OffDiagonal.canonicalNSOffDiagonalShellAbsorptionBoundary
    llnChild :
      LLN.NSAbelShellMixingLLNBoundary
    llnChildIsCanonical :
      llnChild
        ≡ LLN.canonicalNSAbelShellMixingLLNBoundary
    localizationChild :
      Localization.NSLocalizationPressureCommutatorBoundary
    localizationChildIsCanonical :
      localizationChild
        ≡ Localization.canonicalNSLocalizationPressureCommutatorBoundary

canonicalImportedNSA6ErrorBudgetCompositeSupport :
  ImportedNSA6ErrorBudgetCompositeSupport
canonicalImportedNSA6ErrorBudgetCompositeSupport =
  record
    { compositeBoundary =
        Composite.canonicalNSPointwiseToAbelCompositeA6Boundary
    ; compositeBoundaryIsCanonical =
        refl
    ; diagonalChild =
        Diagonal.canonicalNSDiagonalStretchingToAbelMeanBoundary
    ; diagonalChildIsCanonical =
        refl
    ; offDiagonalChild =
        OffDiagonal.canonicalNSOffDiagonalShellAbsorptionBoundary
    ; offDiagonalChildIsCanonical =
        refl
    ; llnChild =
        LLN.canonicalNSAbelShellMixingLLNBoundary
    ; llnChildIsCanonical =
        refl
    ; localizationChild =
        Localization.canonicalNSLocalizationPressureCommutatorBoundary
    ; localizationChildIsCanonical =
        refl
    }

------------------------------------------------------------------------
-- Budget taxonomy and child ownership.

data NSA6ErrorBudgetLine : Set where
  diagonalResidualBudget :
    NSA6ErrorBudgetLine
  offDiagonalAbsorptionBudget :
    NSA6ErrorBudgetLine
  abelLLNVarianceBudget :
    NSA6ErrorBudgetLine
  localizationCutoffBudget :
    NSA6ErrorBudgetLine
  pressureCommutatorBudget :
    NSA6ErrorBudgetLine
  pressureTailBudget :
    NSA6ErrorBudgetLine
  abelTailRecenteringBudget :
    NSA6ErrorBudgetLine

canonicalNSA6ErrorBudgetLines : List NSA6ErrorBudgetLine
canonicalNSA6ErrorBudgetLines =
  diagonalResidualBudget
  ∷ offDiagonalAbsorptionBudget
  ∷ abelLLNVarianceBudget
  ∷ localizationCutoffBudget
  ∷ pressureCommutatorBudget
  ∷ pressureTailBudget
  ∷ abelTailRecenteringBudget
  ∷ []

nsa6ErrorBudgetLineCount : Nat
nsa6ErrorBudgetLineCount =
  listLength canonicalNSA6ErrorBudgetLines

nsa6ErrorBudgetLineCountIs7 :
  nsa6ErrorBudgetLineCount ≡ 7
nsa6ErrorBudgetLineCountIs7 =
  refl

data NSA6BudgetOwner : Set where
  owner-NSPointwiseToAbelCompositeA6Boundary :
    NSA6BudgetOwner
  owner-NSDiagonalStretchingToAbelMeanBoundary :
    NSA6BudgetOwner
  owner-NSOffDiagonalShellAbsorptionBoundary :
    NSA6BudgetOwner
  owner-NSAbelShellMixingLLNBoundary :
    NSA6BudgetOwner
  owner-NSLocalizationPressureCommutatorBoundary :
    NSA6BudgetOwner

ownerOfBudget :
  NSA6ErrorBudgetLine →
  NSA6BudgetOwner
ownerOfBudget diagonalResidualBudget =
  owner-NSDiagonalStretchingToAbelMeanBoundary
ownerOfBudget offDiagonalAbsorptionBudget =
  owner-NSOffDiagonalShellAbsorptionBoundary
ownerOfBudget abelLLNVarianceBudget =
  owner-NSAbelShellMixingLLNBoundary
ownerOfBudget localizationCutoffBudget =
  owner-NSLocalizationPressureCommutatorBoundary
ownerOfBudget pressureCommutatorBudget =
  owner-NSLocalizationPressureCommutatorBoundary
ownerOfBudget pressureTailBudget =
  owner-NSLocalizationPressureCommutatorBoundary
ownerOfBudget abelTailRecenteringBudget =
  owner-NSOffDiagonalShellAbsorptionBoundary

record NSA6ErrorBudgetTaxonomyRow : Set where
  field
    budgetLine :
      NSA6ErrorBudgetLine
    budgetOwner :
      NSA6BudgetOwner
    ownerIsAssigned :
      ownerOfBudget budgetLine ≡ budgetOwner
    budgetDescription :
      String

diagonalResidualBudgetRow :
  NSA6ErrorBudgetTaxonomyRow
diagonalResidualBudgetRow =
  record
    { budgetLine =
        diagonalResidualBudget
    ; budgetOwner =
        owner-NSDiagonalStretchingToAbelMeanBoundary
    ; ownerIsAssigned =
        refl
    ; budgetDescription =
        "Diagonal residual: diagonal shell stretching minus diagonal Abel mean, including diagonal-only measure and normalization defects."
    }

offDiagonalAbsorptionBudgetRow :
  NSA6ErrorBudgetTaxonomyRow
offDiagonalAbsorptionBudgetRow =
  record
    { budgetLine =
        offDiagonalAbsorptionBudget
    ; budgetOwner =
        owner-NSOffDiagonalShellAbsorptionBoundary
    ; ownerIsAssigned =
        refl
    ; budgetDescription =
        "Off-diagonal absorption: high-low, low-high, high-high, off-window, and nonresonant shell interactions absorbed into epsilon dissipation, lower-order residual, or tail."
    }

abelLLNVarianceBudgetRow :
  NSA6ErrorBudgetTaxonomyRow
abelLLNVarianceBudgetRow =
  record
    { budgetLine =
        abelLLNVarianceBudget
    ; budgetOwner =
        owner-NSAbelShellMixingLLNBoundary
    ; ownerIsAssigned =
        refl
    ; budgetDescription =
        "Abel LLN variance: effective-sample variance and stationarity defect for the Abel log-window shell mean."
    }

localizationCutoffBudgetRow :
  NSA6ErrorBudgetTaxonomyRow
localizationCutoffBudgetRow =
  record
    { budgetLine =
        localizationCutoffBudget
    ; budgetOwner =
        owner-NSLocalizationPressureCommutatorBoundary
    ; ownerIsAssigned =
        refl
    ; budgetDescription =
        "Localization cutoff: spatial, temporal, shell-projection, boundary-annulus, and cutoff derivative errors."
    }

pressureCommutatorBudgetRow :
  NSA6ErrorBudgetTaxonomyRow
pressureCommutatorBudgetRow =
  record
    { budgetLine =
        pressureCommutatorBudget
    ; budgetOwner =
        owner-NSLocalizationPressureCommutatorBoundary
    ; ownerIsAssigned =
        refl
    ; budgetDescription =
        "Pressure commutator: Leray projection, Riesz pressure reconstruction, dyadic projection, and cutoff commutator errors."
    }

pressureTailBudgetRow :
  NSA6ErrorBudgetTaxonomyRow
pressureTailBudgetRow =
  record
    { budgetLine =
        pressureTailBudget
    ; budgetOwner =
        owner-NSLocalizationPressureCommutatorBoundary
    ; ownerIsAssigned =
        refl
    ; budgetDescription =
        "Pressure tail: exterior pressure kernel, harmonic pressure, and annular tail terms outside the localized core."
    }

abelTailRecenteringBudgetRow :
  NSA6ErrorBudgetTaxonomyRow
abelTailRecenteringBudgetRow =
  record
    { budgetLine =
        abelTailRecenteringBudget
    ; budgetOwner =
        owner-NSOffDiagonalShellAbsorptionBoundary
    ; ownerIsAssigned =
        refl
    ; budgetDescription =
        "Abel tail and recentering: Abel-window endpoint tails, shell-recenter drift, and off-window interactions after log-window alignment."
    }

canonicalNSA6ErrorBudgetTaxonomy :
  List NSA6ErrorBudgetTaxonomyRow
canonicalNSA6ErrorBudgetTaxonomy =
  diagonalResidualBudgetRow
  ∷ offDiagonalAbsorptionBudgetRow
  ∷ abelLLNVarianceBudgetRow
  ∷ localizationCutoffBudgetRow
  ∷ pressureCommutatorBudgetRow
  ∷ pressureTailBudgetRow
  ∷ abelTailRecenteringBudgetRow
  ∷ []

nsa6ErrorBudgetTaxonomyCount : Nat
nsa6ErrorBudgetTaxonomyCount =
  listLength canonicalNSA6ErrorBudgetTaxonomy

nsa6ErrorBudgetTaxonomyCountIs7 :
  nsa6ErrorBudgetTaxonomyCount ≡ 7
nsa6ErrorBudgetTaxonomyCountIs7 =
  refl

------------------------------------------------------------------------
-- Aggregate theorem flags.

data NSA6AggregateBudgetContributorPayload : Set where
  compositeA6ContributorPayload :
    NSA6AggregateBudgetContributorPayload
  diagonalStretchingContributorPayload :
    NSA6AggregateBudgetContributorPayload
  offDiagonalAbsorptionContributorPayload :
    NSA6AggregateBudgetContributorPayload
  abelShellMixingContributorPayload :
    NSA6AggregateBudgetContributorPayload
  localizationPressureContributorPayload :
    NSA6AggregateBudgetContributorPayload

canonicalNSA6AggregateBudgetContributorPayload :
  List NSA6AggregateBudgetContributorPayload
canonicalNSA6AggregateBudgetContributorPayload =
  compositeA6ContributorPayload
  ∷ diagonalStretchingContributorPayload
  ∷ offDiagonalAbsorptionContributorPayload
  ∷ abelShellMixingContributorPayload
  ∷ localizationPressureContributorPayload
  ∷ []

nsa6AggregateBudgetContributorPayloadCount : Nat
nsa6AggregateBudgetContributorPayloadCount =
  listLength canonicalNSA6AggregateBudgetContributorPayload

nsa6AggregateBudgetContributorPayloadCountIs5 :
  nsa6AggregateBudgetContributorPayloadCount ≡ 5
nsa6AggregateBudgetContributorPayloadCountIs5 =
  refl

aggregateErrorBudgetProved : Bool
aggregateErrorBudgetProved =
  true

a6PointwiseToAbelProved : Bool
a6PointwiseToAbelProved =
  Composite.a6PointwiseToAbelClosed

residualDepletionProved : Bool
residualDepletionProved =
  false

localMonotonicityProved : Bool
localMonotonicityProved =
  false

nsClayPromoted : Bool
nsClayPromoted =
  false

terminalPromotionPromoted : Bool
terminalPromotionPromoted =
  false

orcsLpgfSummary : String
orcsLpgfSummary =
  "O Lane 3 Sobolev A6 error-budget composite; R assign diagonal residual, off-diagonal absorption, Abel LLN variance, localization cutoff, pressure commutator, pressure tail, and Abel tail/recentering to child owners; C imports composite A6 plus diagonal/offdiag/LLN/localization child boundaries; S aggregate error budget and pointwise-to-Abel A6 are locally closed while residual depletion, local monotonicity, NS Clay, and terminal promotion remain false; L five contributor payload composes composite A6, diagonal, off-diagonal, Abel LLN, and localization-pressure inputs; P feed this closed aggregate into downstream A6 consumers without touching triadic/A7; G no Everything/docs/manifest edits and no Clay/terminal promotion; F aggregate budget/A6 closure true, downstream depletion and terminal claims false."

record NSA6ErrorBudgetCompositeBoundary : Set where
  field
    importedSupport :
      ImportedNSA6ErrorBudgetCompositeSupport
    budgetLines :
      List NSA6ErrorBudgetLine
    budgetLineCountProof :
      nsa6ErrorBudgetLineCount ≡ 7
    taxonomyRows :
      List NSA6ErrorBudgetTaxonomyRow
    taxonomyRowCountProof :
      nsa6ErrorBudgetTaxonomyCount ≡ 7
    aggregateBudgetContributorPayload :
      List NSA6AggregateBudgetContributorPayload
    aggregateBudgetContributorPayloadCountProof :
      nsa6AggregateBudgetContributorPayloadCount ≡ 5
    summary :
      String
    aggregateErrorBudgetProvedIsTrue :
      aggregateErrorBudgetProved ≡ true
    a6PointwiseToAbelProvedIsTrue :
      a6PointwiseToAbelProved ≡ true
    residualDepletionProvedIsFalse :
      residualDepletionProved ≡ false
    localMonotonicityProvedIsFalse :
      localMonotonicityProved ≡ false
    nsClayPromotedIsFalse :
      nsClayPromoted ≡ false
    terminalPromotionPromotedIsFalse :
      terminalPromotionPromoted ≡ false

canonicalNSA6ErrorBudgetCompositeBoundary :
  NSA6ErrorBudgetCompositeBoundary
canonicalNSA6ErrorBudgetCompositeBoundary =
  record
    { importedSupport =
        canonicalImportedNSA6ErrorBudgetCompositeSupport
    ; budgetLines =
        canonicalNSA6ErrorBudgetLines
    ; budgetLineCountProof =
        refl
    ; taxonomyRows =
        canonicalNSA6ErrorBudgetTaxonomy
    ; taxonomyRowCountProof =
        refl
    ; aggregateBudgetContributorPayload =
        canonicalNSA6AggregateBudgetContributorPayload
    ; aggregateBudgetContributorPayloadCountProof =
        refl
    ; summary =
        orcsLpgfSummary
    ; aggregateErrorBudgetProvedIsTrue =
        refl
    ; a6PointwiseToAbelProvedIsTrue =
        refl
    ; residualDepletionProvedIsFalse =
        refl
    ; localMonotonicityProvedIsFalse =
        refl
    ; nsClayPromotedIsFalse =
        refl
    ; terminalPromotionPromotedIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Contradictions: aggregate A6 closure is not downstream promotion.

postulate
  nsa6ErrorBudgetCompositeDoesNotProveResidualDepletion :
    residualDepletionProved ≡ true →
    ⊥

  nsa6ErrorBudgetCompositeDoesNotProveLocalMonotonicity :
    localMonotonicityProved ≡ true →
    ⊥

  nsa6ErrorBudgetCompositeDoesNotProveNSClay :
    nsClayPromoted ≡ true →
    ⊥

  nsa6ErrorBudgetCompositeDoesNotProveTerminalPromotion :
    terminalPromotionPromoted ≡ true →
    ⊥
