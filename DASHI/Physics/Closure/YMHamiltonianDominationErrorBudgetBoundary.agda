module DASHI.Physics.Closure.YMHamiltonianDominationErrorBudgetBoundary where

-- Yang-Mills Hamiltonian domination error-budget boundary.
--
-- This module records the finite error surfaces that must be controlled before
-- the composite domination route can promote
--
--   H_d >= c Delta_YM,d + c' Hol_d - E_d.
--
-- It is a boundary ledger only.  It imports the composite boundary and proxy
-- harness result as provenance, optionally carries the finite self-adjoint and
-- Hodge-defect domination boundaries, and keeps every theorem/promotion flag
-- explicitly false.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMHamiltonianDominationCompositeBoundary
  as Composite
import DASHI.Physics.Closure.YMHamiltonianDominationProxyHarnessResult
  as Proxy
import DASHI.Physics.Closure.YMSelfAdjointFiniteHamiltonianBoundary
  as SelfAdjoint
import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary
  as Domination

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported boundary support.

data YMHamiltonianDominationErrorBudgetImport : Set where
  compositeBoundaryImported :
    YMHamiltonianDominationErrorBudgetImport

  proxyHarnessResultImported :
    YMHamiltonianDominationErrorBudgetImport

  selfAdjointFiniteHamiltonianBoundaryImported :
    YMHamiltonianDominationErrorBudgetImport

  hamiltonianDominatesFiniteHodgeDefectBoundaryImported :
    YMHamiltonianDominationErrorBudgetImport

canonicalYMHamiltonianDominationErrorBudgetImports :
  List YMHamiltonianDominationErrorBudgetImport
canonicalYMHamiltonianDominationErrorBudgetImports =
  compositeBoundaryImported
  ∷ proxyHarnessResultImported
  ∷ selfAdjointFiniteHamiltonianBoundaryImported
  ∷ hamiltonianDominatesFiniteHodgeDefectBoundaryImported
  ∷ []

------------------------------------------------------------------------
-- Error-budget surfaces.

data YMHamiltonianDominationErrorBudgetStatus : Set where
  errorBudgetBoundaryRecordedResidualsStillOpen :
    YMHamiltonianDominationErrorBudgetStatus

data YMHamiltonianDominationErrorSurface : Set where
  finiteSelfAdjointDefectSurface :
    YMHamiltonianDominationErrorSurface

  quotientDomainResidualSurface :
    YMHamiltonianDominationErrorSurface

  holonomyCarrierResidualSurface :
    YMHamiltonianDominationErrorSurface

  holonomyActionResidualSurface :
    YMHamiltonianDominationErrorSurface

  negativeErrorEdBudgetSurface :
    YMHamiltonianDominationErrorSurface

  spectralMarginSurface :
    YMHamiltonianDominationErrorSurface

  reflectionPositiveTransferResidualSurface :
    YMHamiltonianDominationErrorSurface

  osContinuumNoSpectralPollutionResidualSurface :
    YMHamiltonianDominationErrorSurface

canonicalYMHamiltonianDominationErrorSurfaces :
  List YMHamiltonianDominationErrorSurface
canonicalYMHamiltonianDominationErrorSurfaces =
  finiteSelfAdjointDefectSurface
  ∷ quotientDomainResidualSurface
  ∷ holonomyCarrierResidualSurface
  ∷ holonomyActionResidualSurface
  ∷ negativeErrorEdBudgetSurface
  ∷ spectralMarginSurface
  ∷ reflectionPositiveTransferResidualSurface
  ∷ osContinuumNoSpectralPollutionResidualSurface
  ∷ []

data YMHamiltonianDominationErrorBudgetBlocker : Set where
  missingFiniteSelfAdjointDefectBound :
    YMHamiltonianDominationErrorBudgetBlocker

  missingQuotientDomainResidualBound :
    YMHamiltonianDominationErrorBudgetBlocker

  missingHolonomyCarrierConstructionResidual :
    YMHamiltonianDominationErrorBudgetBlocker

  missingHolonomyActionResidualBound :
    YMHamiltonianDominationErrorBudgetBlocker

  missingNegativeEdAbsorptionInequality :
    YMHamiltonianDominationErrorBudgetBlocker

  missingUniformSpectralMarginAfterErrors :
    YMHamiltonianDominationErrorBudgetBlocker

  missingReflectionPositiveTransferResidualBound :
    YMHamiltonianDominationErrorBudgetBlocker

  missingOSContinuumNoSpectralPollutionResidualBound :
    YMHamiltonianDominationErrorBudgetBlocker

  missingClayYangMillsAuthorityToken :
    YMHamiltonianDominationErrorBudgetBlocker

canonicalYMHamiltonianDominationErrorBudgetBlockers :
  List YMHamiltonianDominationErrorBudgetBlocker
canonicalYMHamiltonianDominationErrorBudgetBlockers =
  missingFiniteSelfAdjointDefectBound
  ∷ missingQuotientDomainResidualBound
  ∷ missingHolonomyCarrierConstructionResidual
  ∷ missingHolonomyActionResidualBound
  ∷ missingNegativeEdAbsorptionInequality
  ∷ missingUniformSpectralMarginAfterErrors
  ∷ missingReflectionPositiveTransferResidualBound
  ∷ missingOSContinuumNoSpectralPollutionResidualBound
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

record YMHamiltonianDominationErrorBudgetLine : Set where
  field
    surface :
      YMHamiltonianDominationErrorSurface

    label :
      String

    residualText :
      String

    budgetText :
      String

    blocker :
      YMHamiltonianDominationErrorBudgetBlocker

    closed :
      Bool

    closedIsFalse :
      closed ≡ false

open YMHamiltonianDominationErrorBudgetLine public

finiteSelfAdjointDefectLine :
  YMHamiltonianDominationErrorBudgetLine
finiteSelfAdjointDefectLine =
  record
    { surface =
        finiteSelfAdjointDefectSurface
    ; label =
        "finite self-adjoint defect"
    ; residualText =
        "Residual between the finite symmetric form, quotient descent, and self-adjoint matrix/operator theorem."
    ; budgetText =
        "Must be bounded before the finite Hamiltonian can feed domination."
    ; blocker =
        missingFiniteSelfAdjointDefectBound
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

quotientDomainResidualLine :
  YMHamiltonianDominationErrorBudgetLine
quotientDomainResidualLine =
  record
    { surface =
        quotientDomainResidualSurface
    ; label =
        "quotient-domain residual"
    ; residualText =
        "Residual for gauge quotient domain construction, invariant subspace projection, and domain compatibility."
    ; budgetText =
        "Must vanish or be absorbed uniformly across the selected finite quotient."
    ; blocker =
        missingQuotientDomainResidualBound
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

holonomyCarrierResidualLine :
  YMHamiltonianDominationErrorBudgetLine
holonomyCarrierResidualLine =
  record
    { surface =
        holonomyCarrierResidualSurface
    ; label =
        "holonomy carrier residual"
    ; residualText =
        "Residual for constructing the holonomy/topological-sector carrier on the finite quotient."
    ; budgetText =
        "Must provide the positive Hol_d carrier used by the comparison operator."
    ; blocker =
        missingHolonomyCarrierConstructionResidual
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

holonomyActionResidualLine :
  YMHamiltonianDominationErrorBudgetLine
holonomyActionResidualLine =
  record
    { surface =
        holonomyActionResidualSurface
    ; label =
        "holonomy action residual"
    ; residualText =
        "Residual for positive action on nontrivial holonomy or topological sectors."
    ; budgetText =
        "Must be controlled before c' Hol_d can offset near-zero Hamiltonian sectors."
    ; blocker =
        missingHolonomyActionResidualBound
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

negativeErrorEdBudgetLine :
  YMHamiltonianDominationErrorBudgetLine
negativeErrorEdBudgetLine =
  record
    { surface =
        negativeErrorEdBudgetSurface
    ; label =
        "negative error E_d budget"
    ; residualText =
        "Residual negative allowance E_d in H_d >= c Delta_YM,d + c' Hol_d - E_d."
    ; budgetText =
        "Must be small enough to be absorbed by the finite spectral margin."
    ; blocker =
        missingNegativeEdAbsorptionInequality
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

spectralMarginLine :
  YMHamiltonianDominationErrorBudgetLine
spectralMarginLine =
  record
    { surface =
        spectralMarginSurface
    ; label =
        "spectral margin"
    ; residualText =
        "Margin left after defect, holonomy, quotient-domain, and negative E_d errors."
    ; budgetText =
        "Must remain uniformly positive before spectral lift or continuum transfer."
    ; blocker =
        missingUniformSpectralMarginAfterErrors
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

reflectionPositiveTransferResidualLine :
  YMHamiltonianDominationErrorBudgetLine
reflectionPositiveTransferResidualLine =
  record
    { surface =
        reflectionPositiveTransferResidualSurface
    ; label =
        "reflection-positive transfer residual"
    ; residualText =
        "Residual between the finite domination estimate and reflection-positive transfer-matrix construction."
    ; budgetText =
        "Must be closed before the finite estimate can become an OS/reflection-positive transfer theorem."
    ; blocker =
        missingReflectionPositiveTransferResidualBound
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

osContinuumNoSpectralPollutionResidualLine :
  YMHamiltonianDominationErrorBudgetLine
osContinuumNoSpectralPollutionResidualLine =
  record
    { surface =
        osContinuumNoSpectralPollutionResidualSurface
    ; label =
        "OS/continuum no-spectral-pollution residual"
    ; residualText =
        "Residual for OS reconstruction, continuum passage, and no bottom-spectrum pollution."
    ; budgetText =
        "Must close before a continuum mass-gap or Clay-facing promotion can be asserted."
    ; blocker =
        missingOSContinuumNoSpectralPollutionResidualBound
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

canonicalYMHamiltonianDominationErrorBudgetLines :
  List YMHamiltonianDominationErrorBudgetLine
canonicalYMHamiltonianDominationErrorBudgetLines =
  finiteSelfAdjointDefectLine
  ∷ quotientDomainResidualLine
  ∷ holonomyCarrierResidualLine
  ∷ holonomyActionResidualLine
  ∷ negativeErrorEdBudgetLine
  ∷ spectralMarginLine
  ∷ reflectionPositiveTransferResidualLine
  ∷ osContinuumNoSpectralPollutionResidualLine
  ∷ []

------------------------------------------------------------------------
-- Fail-closed theorem flags requested by the boundary.

errorBudgetClosed : Bool
errorBudgetClosed =
  false

hamiltonianDominatesDefectPlusHolonomyProved : Bool
hamiltonianDominatesDefectPlusHolonomyProved =
  false

reflectionPositiveTransferProved : Bool
reflectionPositiveTransferProved =
  false

osContinuumTransferProved : Bool
osContinuumTransferProved =
  false

ymClayPromoted : Bool
ymClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

errorBudgetClosedIsFalse :
  errorBudgetClosed ≡ false
errorBudgetClosedIsFalse =
  refl

hamiltonianDominatesDefectPlusHolonomyProvedIsFalse :
  hamiltonianDominatesDefectPlusHolonomyProved ≡ false
hamiltonianDominatesDefectPlusHolonomyProvedIsFalse =
  refl

reflectionPositiveTransferProvedIsFalse :
  reflectionPositiveTransferProved ≡ false
reflectionPositiveTransferProvedIsFalse =
  refl

osContinuumTransferProvedIsFalse :
  osContinuumTransferProved ≡ false
osContinuumTransferProvedIsFalse =
  refl

ymClayPromotedIsFalse :
  ymClayPromoted ≡ false
ymClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

------------------------------------------------------------------------
-- Boundary receipt.

record YMHamiltonianDominationErrorBudgetBoundary : Setω where
  field
    status :
      YMHamiltonianDominationErrorBudgetStatus

    compositeBoundary :
      Composite.YMHamiltonianDominationCompositeBoundary

    proxyHarnessResult :
      Proxy.YMHamiltonianDominationProxyHarnessResult

    selfAdjointBoundary :
      SelfAdjoint.YMSelfAdjointFiniteHamiltonianBoundary

    hodgeDefectDominationBoundary :
      Domination.YMHamiltonianDominatesFiniteHodgeDefectBoundary

    imports :
      List YMHamiltonianDominationErrorBudgetImport

    importsAreCanonical :
      imports ≡ canonicalYMHamiltonianDominationErrorBudgetImports

    importCount :
      Nat

    importCountIs4 :
      importCount ≡ 4

    surfaces :
      List YMHamiltonianDominationErrorSurface

    surfacesAreCanonical :
      surfaces ≡ canonicalYMHamiltonianDominationErrorSurfaces

    surfaceCount :
      Nat

    surfaceCountIs8 :
      surfaceCount ≡ 8

    budgetLines :
      List YMHamiltonianDominationErrorBudgetLine

    budgetLinesAreCanonical :
      budgetLines ≡ canonicalYMHamiltonianDominationErrorBudgetLines

    budgetLineCount :
      Nat

    budgetLineCountIs8 :
      budgetLineCount ≡ 8

    blockers :
      List YMHamiltonianDominationErrorBudgetBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMHamiltonianDominationErrorBudgetBlockers

    blockerCount :
      Nat

    blockerCountIs9 :
      blockerCount ≡ 9

    importedCompositeDominationStillFalse :
      Composite.dominationTheoremField compositeBoundary ≡ false

    importedCompositeOSTransferStillFalse :
      Composite.osTransferTheoremField compositeBoundary ≡ false

    importedCompositeContinuumStillFalse :
      Composite.continuumNoSpectralPollutionTheoremField
        compositeBoundary
      ≡
      false

    importedProxyPromotionStillFalse :
      Proxy.promotionField proxyHarnessResult ≡ false

    importedProxyDominationStillFalse :
      Proxy.hamiltonianDominationTheoremProvedField
        proxyHarnessResult
      ≡
      false

    importedSelfAdjointDefectStillOpen :
      SelfAdjoint.selfAdjointFiniteHamiltonianProvedField
        selfAdjointBoundary
      ≡
      false

    importedHodgeDefectPlusHolonomyStillFalse :
      Domination.dominationPlusHolonomyProvedField
        hodgeDefectDominationBoundary
      ≡
      false

    importedHodgeReflectionOSStillFalse :
      Domination.reflectionPositivityOSOnGaugeQuotientProvedField
        hodgeDefectDominationBoundary
      ≡
      false

    importedHodgeContinuumStillFalse :
      Domination.continuumTransferNoSpectralPollutionProvedField
        hodgeDefectDominationBoundary
      ≡
      false

    errorBudgetClosedField :
      Bool

    errorBudgetClosedFieldIsFalse :
      errorBudgetClosedField ≡ false

    hamiltonianDominatesDefectPlusHolonomyProvedField :
      Bool

    hamiltonianDominatesDefectPlusHolonomyProvedFieldIsFalse :
      hamiltonianDominatesDefectPlusHolonomyProvedField ≡ false

    reflectionPositiveTransferProvedField :
      Bool

    reflectionPositiveTransferProvedFieldIsFalse :
      reflectionPositiveTransferProvedField ≡ false

    osContinuumTransferProvedField :
      Bool

    osContinuumTransferProvedFieldIsFalse :
      osContinuumTransferProvedField ≡ false

    ymClayPromotedField :
      Bool

    ymClayPromotedFieldIsFalse :
      ymClayPromotedField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

    notes :
      List String

open YMHamiltonianDominationErrorBudgetBoundary public

canonicalYMHamiltonianDominationErrorBudgetBoundary :
  YMHamiltonianDominationErrorBudgetBoundary
canonicalYMHamiltonianDominationErrorBudgetBoundary =
  record
    { status =
        errorBudgetBoundaryRecordedResidualsStillOpen
    ; compositeBoundary =
        Composite.canonicalYMHamiltonianDominationCompositeBoundary
    ; proxyHarnessResult =
        Proxy.canonicalYMHamiltonianDominationProxyHarnessResult
    ; selfAdjointBoundary =
        SelfAdjoint.canonicalYMSelfAdjointFiniteHamiltonianBoundary
    ; hodgeDefectDominationBoundary =
        Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; imports =
        canonicalYMHamiltonianDominationErrorBudgetImports
    ; importsAreCanonical =
        refl
    ; importCount =
        listCount canonicalYMHamiltonianDominationErrorBudgetImports
    ; importCountIs4 =
        refl
    ; surfaces =
        canonicalYMHamiltonianDominationErrorSurfaces
    ; surfacesAreCanonical =
        refl
    ; surfaceCount =
        listCount canonicalYMHamiltonianDominationErrorSurfaces
    ; surfaceCountIs8 =
        refl
    ; budgetLines =
        canonicalYMHamiltonianDominationErrorBudgetLines
    ; budgetLinesAreCanonical =
        refl
    ; budgetLineCount =
        listCount canonicalYMHamiltonianDominationErrorBudgetLines
    ; budgetLineCountIs8 =
        refl
    ; blockers =
        canonicalYMHamiltonianDominationErrorBudgetBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalYMHamiltonianDominationErrorBudgetBlockers
    ; blockerCountIs9 =
        refl
    ; importedCompositeDominationStillFalse =
        Composite.canonicalCompositeDominationFalse
    ; importedCompositeOSTransferStillFalse =
        Composite.canonicalCompositeOSTransferFalse
    ; importedCompositeContinuumStillFalse =
        Composite.canonicalCompositeContinuumNoSpectralPollutionFalse
    ; importedProxyPromotionStillFalse =
        Proxy.canonicalHamiltonianDominationProxyPromotionFalse
    ; importedProxyDominationStillFalse =
        Proxy.canonicalHamiltonianDominationProxyTheoremFalse
    ; importedSelfAdjointDefectStillOpen =
        SelfAdjoint.canonicalSelfAdjointFiniteHamiltonianProvedFalse
    ; importedHodgeDefectPlusHolonomyStillFalse =
        Domination.canonicalYMHamiltonianDominationPlusHolonomyProvedFalse
    ; importedHodgeReflectionOSStillFalse =
        Domination.reflectionPositivityOSOnGaugeQuotientProvedFieldIsFalse
          Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; importedHodgeContinuumStillFalse =
        Domination.continuumTransferNoSpectralPollutionProvedFieldIsFalse
          Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; errorBudgetClosedField =
        errorBudgetClosed
    ; errorBudgetClosedFieldIsFalse =
        errorBudgetClosedIsFalse
    ; hamiltonianDominatesDefectPlusHolonomyProvedField =
        hamiltonianDominatesDefectPlusHolonomyProved
    ; hamiltonianDominatesDefectPlusHolonomyProvedFieldIsFalse =
        hamiltonianDominatesDefectPlusHolonomyProvedIsFalse
    ; reflectionPositiveTransferProvedField =
        reflectionPositiveTransferProved
    ; reflectionPositiveTransferProvedFieldIsFalse =
        reflectionPositiveTransferProvedIsFalse
    ; osContinuumTransferProvedField =
        osContinuumTransferProved
    ; osContinuumTransferProvedFieldIsFalse =
        osContinuumTransferProvedIsFalse
    ; ymClayPromotedField =
        ymClayPromoted
    ; ymClayPromotedFieldIsFalse =
        ymClayPromotedIsFalse
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        terminalPromotionIsFalse
    ; notes =
        "Error budget records finite self-adjoint defect, quotient-domain residual, holonomy carrier/action residuals, negative E_d budget, spectral margin, reflection-positive transfer residual, and OS/continuum no-spectral-pollution residual."
        ∷ "The proxy harness is retained as a finite diagnostic only; it does not close the analytic domination budget."
        ∷ "All closure and promotion flags are held false until uniform residual bounds and transfer theorems are supplied."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas.

canonicalErrorBudgetClosedFalse :
  errorBudgetClosedField
    canonicalYMHamiltonianDominationErrorBudgetBoundary
  ≡
  false
canonicalErrorBudgetClosedFalse =
  refl

canonicalErrorBudgetDominationFalse :
  hamiltonianDominatesDefectPlusHolonomyProvedField
    canonicalYMHamiltonianDominationErrorBudgetBoundary
  ≡
  false
canonicalErrorBudgetDominationFalse =
  refl

canonicalErrorBudgetReflectionPositiveTransferFalse :
  reflectionPositiveTransferProvedField
    canonicalYMHamiltonianDominationErrorBudgetBoundary
  ≡
  false
canonicalErrorBudgetReflectionPositiveTransferFalse =
  refl

canonicalErrorBudgetOSContinuumTransferFalse :
  osContinuumTransferProvedField
    canonicalYMHamiltonianDominationErrorBudgetBoundary
  ≡
  false
canonicalErrorBudgetOSContinuumTransferFalse =
  refl

canonicalErrorBudgetYMClayFalse :
  ymClayPromotedField canonicalYMHamiltonianDominationErrorBudgetBoundary
  ≡
  false
canonicalErrorBudgetYMClayFalse =
  refl

canonicalErrorBudgetTerminalFalse :
  terminalPromotionField canonicalYMHamiltonianDominationErrorBudgetBoundary
  ≡
  false
canonicalErrorBudgetTerminalFalse =
  refl

noErrorBudgetClosureFromBoundaryAlone :
  errorBudgetClosedField
    canonicalYMHamiltonianDominationErrorBudgetBoundary
  ≡
  true →
  ⊥
noErrorBudgetClosureFromBoundaryAlone ()

noTerminalPromotionFromErrorBudgetBoundaryAlone :
  terminalPromotionField canonicalYMHamiltonianDominationErrorBudgetBoundary
  ≡
  true →
  ⊥
noTerminalPromotionFromErrorBudgetBoundaryAlone ()
