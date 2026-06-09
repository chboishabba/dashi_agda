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
-- This module records the explicit budget taxonomy required before the
-- A6 pointwise-to-Abel composite can become a theorem.  It assigns every
-- budget line to the child boundary that owns it.  It is fail-closed:
-- aggregate budget proof, A6, residual depletion, local monotonicity,
-- NS Clay, and terminal promotion all remain false.

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
-- Fail-closed theorem flags.

aggregateErrorBudgetProved : Bool
aggregateErrorBudgetProved =
  false

a6PointwiseToAbelProved : Bool
a6PointwiseToAbelProved =
  false

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
  "O Lane 3 Sobolev A6 error-budget composite; R assign diagonal residual, off-diagonal absorption, Abel LLN variance, localization cutoff, pressure commutator, pressure tail, and Abel tail/recentering to child owners; C imports composite A6 plus diagonal/offdiag/LLN/localization child boundaries; S all theorem and promotion flags false; L error-budget rows feed aggregate A6 only after each owner upgrades from boundary to theorem; P prove child-owned estimates then aggregate the budget; G no Everything/docs/manifest edits and no Clay/terminal promotion; F aggregate error budget, A6, residual depletion, local monotonicity, NS Clay, and terminal promotion remain false."

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
    summary :
      String
    aggregateErrorBudgetProvedIsFalse :
      aggregateErrorBudgetProved ≡ false
    a6PointwiseToAbelProvedIsFalse :
      a6PointwiseToAbelProved ≡ false
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
    ; summary =
        orcsLpgfSummary
    ; aggregateErrorBudgetProvedIsFalse =
        refl
    ; a6PointwiseToAbelProvedIsFalse =
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
-- Contradictions: taxonomy ownership is not theorem promotion.

postulate
  nsa6ErrorBudgetCompositeDoesNotProveAggregateBudget :
    aggregateErrorBudgetProved ≡ true →
    ⊥

  nsa6ErrorBudgetCompositeDoesNotProveA6 :
    a6PointwiseToAbelProved ≡ true →
    ⊥

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
