module DASHI.Physics.Closure.YMHamiltonianDominationCompositeBoundary where

-- Composite Yang-Mills Hamiltonian domination boundary.
--
-- This module records the dependency chain requested by Lane 5:
--
--   admissible boundary
--   -> finite self-adjoint operator
--   -> holonomy/action sector
--   -> domination inequality
--   -> reflection positivity/OS
--   -> continuum no spectral pollution.
--
-- It consumes the finite self-adjoint boundary, its proxy harness receipt, the
-- finite Hodge-defect domination boundary, and the finite gauge quotient /
-- Hamiltonian precondition boundary.  It is a fail-closed ledger only: it does
-- not prove domination, OS transfer, continuum transfer, Clay Yang-Mills, or
-- terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMSelfAdjointFiniteHamiltonianBoundary
  as SelfAdjoint
import DASHI.Physics.Closure.YMFiniteSelfAdjointHamiltonianProxyHarnessResult
  as Proxy
import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary
  as Domination
import DASHI.Physics.Closure.YMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  as Precondition

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Composite route shape.

data YMHamiltonianDominationCompositeStatus : Set where
  compositeBoundaryRecordedDominationChainStillOpen :
    YMHamiltonianDominationCompositeStatus

data YMHamiltonianDominationCompositeChainStep : Set where
  admissibleBoundaryStep :
    YMHamiltonianDominationCompositeChainStep

  finiteSelfAdjointOperatorStep :
    YMHamiltonianDominationCompositeChainStep

  holonomyActionSectorStep :
    YMHamiltonianDominationCompositeChainStep

  dominationInequalityStep :
    YMHamiltonianDominationCompositeChainStep

  reflectionPositivityOSStep :
    YMHamiltonianDominationCompositeChainStep

  continuumNoSpectralPollutionStep :
    YMHamiltonianDominationCompositeChainStep

canonicalYMHamiltonianDominationCompositeChain :
  List YMHamiltonianDominationCompositeChainStep
canonicalYMHamiltonianDominationCompositeChain =
  admissibleBoundaryStep
  ∷ finiteSelfAdjointOperatorStep
  ∷ holonomyActionSectorStep
  ∷ dominationInequalityStep
  ∷ reflectionPositivityOSStep
  ∷ continuumNoSpectralPollutionStep
  ∷ []

stepLabel :
  YMHamiltonianDominationCompositeChainStep →
  String
stepLabel admissibleBoundaryStep =
  "admissible boundary"
stepLabel finiteSelfAdjointOperatorStep =
  "finite self-adjoint operator"
stepLabel holonomyActionSectorStep =
  "holonomy/action sector"
stepLabel dominationInequalityStep =
  "domination inequality"
stepLabel reflectionPositivityOSStep =
  "reflection positivity/OS"
stepLabel continuumNoSpectralPollutionStep =
  "continuum no spectral pollution"

data YMHamiltonianDominationCompositeSupport : Set where
  finiteGaugeQuotientHamiltonianPreconditionImported :
    YMHamiltonianDominationCompositeSupport

  selfAdjointFiniteHamiltonianBoundaryImported :
    YMHamiltonianDominationCompositeSupport

  finiteSelfAdjointProxyHarnessImported :
    YMHamiltonianDominationCompositeSupport

  hamiltonianDominatesFiniteHodgeDefectBoundaryImported :
    YMHamiltonianDominationCompositeSupport

canonicalYMHamiltonianDominationCompositeSupport :
  List YMHamiltonianDominationCompositeSupport
canonicalYMHamiltonianDominationCompositeSupport =
  finiteGaugeQuotientHamiltonianPreconditionImported
  ∷ selfAdjointFiniteHamiltonianBoundaryImported
  ∷ finiteSelfAdjointProxyHarnessImported
  ∷ hamiltonianDominatesFiniteHodgeDefectBoundaryImported
  ∷ []

data YMHamiltonianDominationCompositeBlocker : Set where
  missingFiniteGaugeQuotientCarrier :
    YMHamiltonianDominationCompositeBlocker

  missingFiniteSelfAdjointOperatorTheorem :
    YMHamiltonianDominationCompositeBlocker

  missingHolonomyActionSectorConstruction :
    YMHamiltonianDominationCompositeBlocker

  missingHamiltonianDominationInequality :
    YMHamiltonianDominationCompositeBlocker

  missingReflectionPositivityOSTransfer :
    YMHamiltonianDominationCompositeBlocker

  missingContinuumNoSpectralPollutionTransfer :
    YMHamiltonianDominationCompositeBlocker

  missingClayYangMillsAuthorityToken :
    YMHamiltonianDominationCompositeBlocker

canonicalYMHamiltonianDominationCompositeBlockers :
  List YMHamiltonianDominationCompositeBlocker
canonicalYMHamiltonianDominationCompositeBlockers =
  missingFiniteGaugeQuotientCarrier
  ∷ missingFiniteSelfAdjointOperatorTheorem
  ∷ missingHolonomyActionSectorConstruction
  ∷ missingHamiltonianDominationInequality
  ∷ missingReflectionPositivityOSTransfer
  ∷ missingContinuumNoSpectralPollutionTransfer
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

------------------------------------------------------------------------
-- Fail-closed theorem flags.

dominationTheoremFlag : Bool
dominationTheoremFlag =
  false

osTransferTheoremFlag : Bool
osTransferTheoremFlag =
  false

continuumNoSpectralPollutionTheoremFlag : Bool
continuumNoSpectralPollutionTheoremFlag =
  false

ymClayTheoremFlag : Bool
ymClayTheoremFlag =
  false

terminalTheoremFlag : Bool
terminalTheoremFlag =
  false

dominationTheoremFlagIsFalse :
  dominationTheoremFlag ≡ false
dominationTheoremFlagIsFalse =
  refl

osTransferTheoremFlagIsFalse :
  osTransferTheoremFlag ≡ false
osTransferTheoremFlagIsFalse =
  refl

continuumNoSpectralPollutionTheoremFlagIsFalse :
  continuumNoSpectralPollutionTheoremFlag ≡ false
continuumNoSpectralPollutionTheoremFlagIsFalse =
  refl

ymClayTheoremFlagIsFalse :
  ymClayTheoremFlag ≡ false
ymClayTheoremFlagIsFalse =
  refl

terminalTheoremFlagIsFalse :
  terminalTheoremFlag ≡ false
terminalTheoremFlagIsFalse =
  refl

------------------------------------------------------------------------
-- Composite boundary receipt.

record YMHamiltonianDominationCompositeBoundary : Setω where
  field
    status :
      YMHamiltonianDominationCompositeStatus

    finiteGaugeQuotientPrecondition :
      Precondition.YMFiniteGaugeQuotientHamiltonianPreconditionBoundary

    finiteSelfAdjointBoundary :
      SelfAdjoint.YMSelfAdjointFiniteHamiltonianBoundary

    finiteSelfAdjointProxyHarness :
      Proxy.YMFiniteSelfAdjointHamiltonianProxyHarnessResult

    hamiltonianDominationBoundary :
      Domination.YMHamiltonianDominatesFiniteHodgeDefectBoundary

    support :
      List YMHamiltonianDominationCompositeSupport

    supportIsCanonical :
      support ≡ canonicalYMHamiltonianDominationCompositeSupport

    supportCount :
      Nat

    supportCountIs4 :
      supportCount ≡ 4

    chain :
      List YMHamiltonianDominationCompositeChainStep

    chainIsCanonical :
      chain ≡ canonicalYMHamiltonianDominationCompositeChain

    chainCount :
      Nat

    chainCountIs6 :
      chainCount ≡ 6

    blockers :
      List YMHamiltonianDominationCompositeBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMHamiltonianDominationCompositeBlockers

    blockerCount :
      Nat

    blockerCountIs7 :
      blockerCount ≡ 7

    chainText :
      List String

    chainTextIsCanonical :
      chainText
      ≡
      ( "admissible boundary"
        ∷ "finite self-adjoint operator"
        ∷ "holonomy/action sector"
        ∷ "domination inequality"
        ∷ "reflection positivity/OS"
        ∷ "continuum no spectral pollution"
        ∷ [] )

    preconditionFiniteQuotientStillFalse :
      Precondition.finiteQuotientConstructedField
        finiteGaugeQuotientPrecondition
      ≡
      false

    preconditionSelfAdjointStillFalse :
      Precondition.selfAdjointHamiltonianProvedField
        finiteGaugeQuotientPrecondition
      ≡
      false

    selfAdjointBoundaryTheoremStillFalse :
      SelfAdjoint.selfAdjointFiniteHamiltonianProvedField
        finiteSelfAdjointBoundary
      ≡
      false

    proxyHarnessDiagnosticOnly :
      Proxy.promotionField finiteSelfAdjointProxyHarness ≡ false

    proxyHarnessDominationStillFalse :
      Proxy.hamiltonianDominationUnlockedField
        finiteSelfAdjointProxyHarness
      ≡
      false

    dominationBoundaryInequalityStillFalse :
      Domination.dominationPlusHolonomyProvedField
        hamiltonianDominationBoundary
      ≡
      false

    dominationBoundaryOSStillFalse :
      Domination.reflectionPositivityOSOnGaugeQuotientProvedField
        hamiltonianDominationBoundary
      ≡
      false

    dominationBoundaryContinuumStillFalse :
      Domination.continuumTransferNoSpectralPollutionProvedField
        hamiltonianDominationBoundary
      ≡
      false

    dominationTheoremField :
      Bool

    dominationTheoremFieldIsFalse :
      dominationTheoremField ≡ false

    osTransferTheoremField :
      Bool

    osTransferTheoremFieldIsFalse :
      osTransferTheoremField ≡ false

    continuumNoSpectralPollutionTheoremField :
      Bool

    continuumNoSpectralPollutionTheoremFieldIsFalse :
      continuumNoSpectralPollutionTheoremField ≡ false

    ymClayTheoremField :
      Bool

    ymClayTheoremFieldIsFalse :
      ymClayTheoremField ≡ false

    terminalTheoremField :
      Bool

    terminalTheoremFieldIsFalse :
      terminalTheoremField ≡ false

    notes :
      List String

open YMHamiltonianDominationCompositeBoundary public

canonicalYMHamiltonianDominationCompositeBoundary :
  YMHamiltonianDominationCompositeBoundary
canonicalYMHamiltonianDominationCompositeBoundary =
  record
    { status =
        compositeBoundaryRecordedDominationChainStillOpen
    ; finiteGaugeQuotientPrecondition =
        Precondition.canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
    ; finiteSelfAdjointBoundary =
        SelfAdjoint.canonicalYMSelfAdjointFiniteHamiltonianBoundary
    ; finiteSelfAdjointProxyHarness =
        Proxy.canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
    ; hamiltonianDominationBoundary =
        Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; support =
        canonicalYMHamiltonianDominationCompositeSupport
    ; supportIsCanonical =
        refl
    ; supportCount =
        listCount canonicalYMHamiltonianDominationCompositeSupport
    ; supportCountIs4 =
        refl
    ; chain =
        canonicalYMHamiltonianDominationCompositeChain
    ; chainIsCanonical =
        refl
    ; chainCount =
        listCount canonicalYMHamiltonianDominationCompositeChain
    ; chainCountIs6 =
        refl
    ; blockers =
        canonicalYMHamiltonianDominationCompositeBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalYMHamiltonianDominationCompositeBlockers
    ; blockerCountIs7 =
        refl
    ; chainText =
        "admissible boundary"
        ∷ "finite self-adjoint operator"
        ∷ "holonomy/action sector"
        ∷ "domination inequality"
        ∷ "reflection positivity/OS"
        ∷ "continuum no spectral pollution"
        ∷ []
    ; chainTextIsCanonical =
        refl
    ; preconditionFiniteQuotientStillFalse =
        Precondition.canonicalFiniteQuotientConstructedFalse
    ; preconditionSelfAdjointStillFalse =
        Precondition.canonicalSelfAdjointHamiltonianProvedFalse
    ; selfAdjointBoundaryTheoremStillFalse =
        SelfAdjoint.canonicalSelfAdjointFiniteHamiltonianProvedFalse
    ; proxyHarnessDiagnosticOnly =
        Proxy.canonicalHarnessPromotionFalse
    ; proxyHarnessDominationStillFalse =
        Proxy.canonicalHarnessHamiltonianDominationFalse
    ; dominationBoundaryInequalityStillFalse =
        Domination.canonicalYMHamiltonianDominationPlusHolonomyProvedFalse
    ; dominationBoundaryOSStillFalse =
        Domination.reflectionPositivityOSOnGaugeQuotientProvedFieldIsFalse
          Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; dominationBoundaryContinuumStillFalse =
        Domination.continuumTransferNoSpectralPollutionProvedFieldIsFalse
          Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; dominationTheoremField =
        dominationTheoremFlag
    ; dominationTheoremFieldIsFalse =
        dominationTheoremFlagIsFalse
    ; osTransferTheoremField =
        osTransferTheoremFlag
    ; osTransferTheoremFieldIsFalse =
        osTransferTheoremFlagIsFalse
    ; continuumNoSpectralPollutionTheoremField =
        continuumNoSpectralPollutionTheoremFlag
    ; continuumNoSpectralPollutionTheoremFieldIsFalse =
        continuumNoSpectralPollutionTheoremFlagIsFalse
    ; ymClayTheoremField =
        ymClayTheoremFlag
    ; ymClayTheoremFieldIsFalse =
        ymClayTheoremFlagIsFalse
    ; terminalTheoremField =
        terminalTheoremFlag
    ; terminalTheoremFieldIsFalse =
        terminalTheoremFlagIsFalse
    ; notes =
        "Composite route records: admissible boundary -> finite self-adjoint operator -> holonomy/action sector -> domination inequality -> reflection positivity/OS -> continuum no spectral pollution."
        ∷ "The finite self-adjoint proxy harness is diagnostic evidence only and does not promote the analytic theorem."
        ∷ "Domination, OS transfer, continuum no-spectral-pollution, YM Clay, and terminal theorem flags remain false."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas.

canonicalCompositeChainCountIs6 :
  chainCount canonicalYMHamiltonianDominationCompositeBoundary ≡ 6
canonicalCompositeChainCountIs6 =
  refl

canonicalCompositeDominationFalse :
  dominationTheoremField canonicalYMHamiltonianDominationCompositeBoundary
  ≡
  false
canonicalCompositeDominationFalse =
  refl

canonicalCompositeOSTransferFalse :
  osTransferTheoremField canonicalYMHamiltonianDominationCompositeBoundary
  ≡
  false
canonicalCompositeOSTransferFalse =
  refl

canonicalCompositeContinuumNoSpectralPollutionFalse :
  continuumNoSpectralPollutionTheoremField
    canonicalYMHamiltonianDominationCompositeBoundary
  ≡
  false
canonicalCompositeContinuumNoSpectralPollutionFalse =
  refl

canonicalCompositeYMClayFalse :
  ymClayTheoremField canonicalYMHamiltonianDominationCompositeBoundary
  ≡
  false
canonicalCompositeYMClayFalse =
  refl

canonicalCompositeTerminalFalse :
  terminalTheoremField canonicalYMHamiltonianDominationCompositeBoundary
  ≡
  false
canonicalCompositeTerminalFalse =
  refl

noDominationPromotionFromCompositeBoundaryAlone :
  dominationTheoremField canonicalYMHamiltonianDominationCompositeBoundary
  ≡
  true →
  ⊥
noDominationPromotionFromCompositeBoundaryAlone ()

noYMClayPromotionFromCompositeBoundaryAlone :
  ymClayTheoremField canonicalYMHamiltonianDominationCompositeBoundary
  ≡
  true →
  ⊥
noYMClayPromotionFromCompositeBoundaryAlone ()
