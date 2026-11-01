module DASHI.Physics.Closure.YMSpectralMarginErrorBudgetCompositeBoundary where

-- Yang-Mills spectral-margin error-budget composite boundary.
--
-- This module consumes the current Hamiltonian-domination budget and proxy
-- diagnostic surfaces, and records the remaining chain
--
--   spectral margin -> domination -> reflection positivity -> OS/continuum.
--
-- It is a fail-closed ledger only.  Every theorem and promotion flag remains
-- false.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMHamiltonianDominationErrorBudgetBoundary
  as ErrorBudget
import DASHI.Physics.Closure.YMHamiltonianDominationProxyHarnessResult
  as DominationProxy
import DASHI.Physics.Closure.YMDominationSpectralMarginProxyHarnessResult
  as SpectralProxy

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported and cited support.

data YMSpectralMarginCompositeSupport : Set where
  hamiltonianDominationErrorBudgetImported :
    YMSpectralMarginCompositeSupport

  hamiltonianDominationProxyHarnessImported :
    YMSpectralMarginCompositeSupport

  dominationSpectralMarginProxyHarnessImported :
    YMSpectralMarginCompositeSupport

canonicalYMSpectralMarginCompositeSupport :
  List YMSpectralMarginCompositeSupport
canonicalYMSpectralMarginCompositeSupport =
  hamiltonianDominationErrorBudgetImported
  ∷ hamiltonianDominationProxyHarnessImported
  ∷ dominationSpectralMarginProxyHarnessImported
  ∷ []

supportCount : Nat
supportCount =
  listCount canonicalYMSpectralMarginCompositeSupport

supportCountIs3 : supportCount ≡ 3
supportCountIs3 =
  refl

spectralMarginProxyReceiptReference : String
spectralMarginProxyReceiptReference =
  "DASHI.Physics.Closure.YMDominationSpectralMarginProxyHarnessResult"

spectralMarginProxyReceiptImported : Bool
spectralMarginProxyReceiptImported =
  true

spectralMarginProxyReceiptImportedIsTrue :
  spectralMarginProxyReceiptImported ≡ true
spectralMarginProxyReceiptImportedIsTrue =
  refl

dominationProxyObservedOk :
  DominationProxy.ok_observed ≡ true
dominationProxyObservedOk =
  refl

dominationProxyPromotionStillFalse :
  DominationProxy.promotion ≡ false
dominationProxyPromotionStillFalse =
  DominationProxy.promotion_is_false

spectralProxyObservedOk :
  SpectralProxy.ok_observed ≡ true
spectralProxyObservedOk =
  SpectralProxy.ok_observed_is_true

spectralProxyPromotionStillFalse :
  SpectralProxy.promotion ≡ false
spectralProxyPromotionStillFalse =
  SpectralProxy.promotion_is_false

spectralProxyTheoremStillFalse :
  SpectralProxy.spectralMarginTheoremProved ≡ false
spectralProxyTheoremStillFalse =
  SpectralProxy.spectralMarginTheoremProvedIsFalse

spectralProxyDominationStillFalse :
  SpectralProxy.hamiltonianDominationProved ≡ false
spectralProxyDominationStillFalse =
  SpectralProxy.hamiltonianDominationProvedIsFalse

------------------------------------------------------------------------
-- Spectral margin -> domination -> OS/continuum chain.

data YMSpectralMarginChainStep : Set where
  finiteSelfAdjointQuotientStep :
    YMSpectralMarginChainStep

  spectralMarginAfterErrorBudgetStep :
    YMSpectralMarginChainStep

  dominationByDefectPlusHolonomyStep :
    YMSpectralMarginChainStep

  reflectionPositiveTransferMatrixStep :
    YMSpectralMarginChainStep

  osterwalderSchraderContinuumTransferStep :
    YMSpectralMarginChainStep

  noSpectralPollutionContinuumLimitStep :
    YMSpectralMarginChainStep

canonicalYMSpectralMarginChain :
  List YMSpectralMarginChainStep
canonicalYMSpectralMarginChain =
  finiteSelfAdjointQuotientStep
  ∷ spectralMarginAfterErrorBudgetStep
  ∷ dominationByDefectPlusHolonomyStep
  ∷ reflectionPositiveTransferMatrixStep
  ∷ osterwalderSchraderContinuumTransferStep
  ∷ noSpectralPollutionContinuumLimitStep
  ∷ []

chainStepCount : Nat
chainStepCount =
  listCount canonicalYMSpectralMarginChain

chainStepCountIs6 : chainStepCount ≡ 6
chainStepCountIs6 =
  refl

------------------------------------------------------------------------
-- Budget rows requested for the composite.

data YMSpectralMarginBudgetSurface : Set where
  selfAdjointDefectSurface :
    YMSpectralMarginBudgetSurface

  quotientDomainResidualSurface :
    YMSpectralMarginBudgetSurface

  kineticGapSurface :
    YMSpectralMarginBudgetSurface

  holonomyFloorSurface :
    YMSpectralMarginBudgetSurface

  negativeEdBudgetSurface :
    YMSpectralMarginBudgetSurface

  spectralPollutionResidualSurface :
    YMSpectralMarginBudgetSurface

  transferResidualSurface :
    YMSpectralMarginBudgetSurface

data YMSpectralMarginBudgetBlocker : Set where
  missingSelfAdjointDefectClosure :
    YMSpectralMarginBudgetBlocker

  missingQuotientDomainResidualClosure :
    YMSpectralMarginBudgetBlocker

  missingUniformKineticGap :
    YMSpectralMarginBudgetBlocker

  missingUniformHolonomyFloor :
    YMSpectralMarginBudgetBlocker

  missingNegativeEdAbsorption :
    YMSpectralMarginBudgetBlocker

  missingNoSpectralPollutionBound :
    YMSpectralMarginBudgetBlocker

  missingReflectionPositiveOSTransferBound :
    YMSpectralMarginBudgetBlocker

record YMSpectralMarginBudgetRow : Set where
  field
    surface :
      YMSpectralMarginBudgetSurface

    label :
      String

    residualText :
      String

    chainRole :
      String

    blocker :
      YMSpectralMarginBudgetBlocker

    closed :
      Bool

    closedIsFalse :
      closed ≡ false

open YMSpectralMarginBudgetRow public

selfAdjointDefectBudgetRow : YMSpectralMarginBudgetRow
selfAdjointDefectBudgetRow =
  record
    { surface =
        selfAdjointDefectSurface
    ; label =
        "self-adjoint defect"
    ; residualText =
        "Finite Hamiltonian symmetry, closed-domain, and quotient descent defects still require a theorem."
    ; chainRole =
        "Input gate before any spectral-margin statement can be promoted."
    ; blocker =
        missingSelfAdjointDefectClosure
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

quotientDomainResidualBudgetRow : YMSpectralMarginBudgetRow
quotientDomainResidualBudgetRow =
  record
    { surface =
        quotientDomainResidualSurface
    ; label =
        "quotient-domain residual"
    ; residualText =
        "Gauge-quotient carrier, invariant projection, and domain compatibility residuals remain open."
    ; chainRole =
        "Prevents the finite matrix/proxy margin from becoming a quotient Hamiltonian theorem."
    ; blocker =
        missingQuotientDomainResidualClosure
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

kineticGapBudgetRow : YMSpectralMarginBudgetRow
kineticGapBudgetRow =
  record
    { surface =
        kineticGapSurface
    ; label =
        "kinetic gap"
    ; residualText =
        "Uniform positive lower bound for the finite gauge-Hodge kinetic sector is not yet proved."
    ; chainRole =
        "Feeds the spectral margin side of H_d >= c1 Delta_YM,d + c2 Hol_d - E_d."
    ; blocker =
        missingUniformKineticGap
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

holonomyFloorBudgetRow : YMSpectralMarginBudgetRow
holonomyFloorBudgetRow =
  record
    { surface =
        holonomyFloorSurface
    ; label =
        "holonomy floor"
    ; residualText =
        "Non-vacuum holonomy or topological sectors still need a uniform positive action floor."
    ; chainRole =
        "Supplies the c2 Hol_d term and rules out non-vacuum zero-mode escape."
    ; blocker =
        missingUniformHolonomyFloor
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

negativeEdBudgetRow : YMSpectralMarginBudgetRow
negativeEdBudgetRow =
  record
    { surface =
        negativeEdBudgetSurface
    ; label =
        "negative Ed budget"
    ; residualText =
        "The finite error E_d still needs an absorption inequality against kinetic and holonomy margins."
    ; chainRole =
        "Protects the domination inequality from losing its positive spectral margin."
    ; blocker =
        missingNegativeEdAbsorption
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

spectralPollutionResidualBudgetRow : YMSpectralMarginBudgetRow
spectralPollutionResidualBudgetRow =
  record
    { surface =
        spectralPollutionResidualSurface
    ; label =
        "spectral pollution residual"
    ; residualText =
        "Continuum and depth-limit near-zero spectral pollution has not been excluded."
    ; chainRole =
        "Blocks transfer of the finite margin into a continuum mass-gap statement."
    ; blocker =
        missingNoSpectralPollutionBound
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

transferResidualBudgetRow : YMSpectralMarginBudgetRow
transferResidualBudgetRow =
  record
    { surface =
        transferResidualSurface
    ; label =
        "transfer residual"
    ; residualText =
        "Reflection positivity, OS reconstruction, and BT-to-continuum transfer residuals remain open."
    ; chainRole =
        "Final bridge from finite Hamiltonian domination to OS/Wightman continuum authority."
    ; blocker =
        missingReflectionPositiveOSTransferBound
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

canonicalYMSpectralMarginBudgetRows :
  List YMSpectralMarginBudgetRow
canonicalYMSpectralMarginBudgetRows =
  selfAdjointDefectBudgetRow
  ∷ quotientDomainResidualBudgetRow
  ∷ kineticGapBudgetRow
  ∷ holonomyFloorBudgetRow
  ∷ negativeEdBudgetRow
  ∷ spectralPollutionResidualBudgetRow
  ∷ transferResidualBudgetRow
  ∷ []

budgetRowCount : Nat
budgetRowCount =
  listCount canonicalYMSpectralMarginBudgetRows

budgetRowCountIs7 : budgetRowCount ≡ 7
budgetRowCountIs7 =
  refl

------------------------------------------------------------------------
-- Composite theorem and promotion flags.

record YMSpectralMarginErrorBudgetCompositeBoundary : Set where
  field
    support :
      List YMSpectralMarginCompositeSupport

    chain :
      List YMSpectralMarginChainStep

    budgetRows :
      List YMSpectralMarginBudgetRow

    spectralMarginProxyReceipt :
      String

    spectralMarginTheoremProved :
      Bool

    hamiltonianDominationProved :
      Bool

    reflectionPositiveTransferProved :
      Bool

    osContinuumTransferProved :
      Bool

    noSpectralPollutionProved :
      Bool

    ymClayPromoted :
      Bool

    terminalPromotion :
      Bool

open YMSpectralMarginErrorBudgetCompositeBoundary public

canonicalYMSpectralMarginErrorBudgetCompositeBoundary :
  YMSpectralMarginErrorBudgetCompositeBoundary
canonicalYMSpectralMarginErrorBudgetCompositeBoundary =
  record
    { support =
        canonicalYMSpectralMarginCompositeSupport
    ; chain =
        canonicalYMSpectralMarginChain
    ; budgetRows =
        canonicalYMSpectralMarginBudgetRows
    ; spectralMarginProxyReceipt =
        spectralMarginProxyReceiptReference
    ; spectralMarginTheoremProved =
        false
    ; hamiltonianDominationProved =
        false
    ; reflectionPositiveTransferProved =
        false
    ; osContinuumTransferProved =
        false
    ; noSpectralPollutionProved =
        false
    ; ymClayPromoted =
        false
    ; terminalPromotion =
        false
    }

spectralMarginTheoremProvedIsFalse :
  spectralMarginTheoremProved
    canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
spectralMarginTheoremProvedIsFalse =
  refl

hamiltonianDominationProvedIsFalse :
  hamiltonianDominationProved
    canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
hamiltonianDominationProvedIsFalse =
  refl

reflectionPositiveTransferProvedIsFalse :
  reflectionPositiveTransferProved
    canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
reflectionPositiveTransferProvedIsFalse =
  refl

osContinuumTransferProvedIsFalse :
  osContinuumTransferProved
    canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
osContinuumTransferProvedIsFalse =
  refl

noSpectralPollutionProvedIsFalse :
  noSpectralPollutionProved
    canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
noSpectralPollutionProvedIsFalse =
  refl

ymClayPromotedIsFalse :
  ymClayPromoted
    canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
ymClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion
    canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
terminalPromotionIsFalse =
  refl

------------------------------------------------------------------------
-- Link back to the consumed error-budget surface.

consumedErrorBudgetRowCount : Nat
consumedErrorBudgetRowCount =
  listCount ErrorBudget.canonicalYMHamiltonianDominationErrorBudgetBlockers

consumedErrorBudgetStillOpen : Bool
consumedErrorBudgetStillOpen =
  true

consumedErrorBudgetStillOpenIsTrue :
  consumedErrorBudgetStillOpen ≡ true
consumedErrorBudgetStillOpenIsTrue =
  refl
