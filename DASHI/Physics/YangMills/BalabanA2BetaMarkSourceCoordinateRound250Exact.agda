{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA2BetaMarkSourceCoordinateRound250Exact where

------------------------------------------------------------------------
-- ROUND250 / A2 HISTORY: SHELL SAME-OBJECT IS THE TRUE SOURCE WALL
--
-- `SharedMarkedAnalyticShellControl` already proves every finite partial-sum and
-- vanishing-tail estimate once `betaHistoryShell` is instantiated.  Therefore
-- the physical consumer must not ask separately for equality of all partial
-- sums.  The source-facing same-object coordinate is the shell itself:
--
--   literal generated-history derivative shell
--     = CMP116 betaHistoryShell.
--
-- Finite sums, half-constant bounds and Cauchy tails are compiler consequences.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanA2SharedMarkedHistoryDerivativeRound116Exact as R116

record LiteralBetaHistoryShellIdentification : Set₁ where
  field
    Scale Volume Root : Set
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    literalGeneratedHistoryShell : Nat → ℚ

    literalGeneratedHistoryShellIsCMP116BetaMark : ∀ depth →
      literalGeneratedHistoryShell depth
      ≡ Shared.betaHistoryShell shared scale volume root depth

open LiteralBetaHistoryShellIdentification public

-- The current R116 partial-sum carrier is a downstream summary.  This module
-- records the strictly earlier same-object coordinate; list/sum transport from
-- the shell identity is generic compiler work and not a new physical theorem.

a2BetaMarkSourceCoordinateCompilerBoundaryLevel : ProofLevel
a2BetaMarkSourceCoordinateCompilerBoundaryLevel = machineChecked

-- No concrete constructor of `betaHistoryShell` was found elsewhere in-repo.
-- This is the current literal CMP116/source-history realization wall.
literalCMP116BetaMarkIsGeneratedHistoryShellLevel : ProofLevel
literalCMP116BetaMarkIsGeneratedHistoryShellLevel = conditional

-- Compatibility: the older coarse partial-sum identification remains
-- conditional but is downstream of this shell-level same-object statement.
legacyPartialSumIdentificationLevel : ProofLevel
legacyPartialSumIdentificationLevel =
  R116.literalCMP116BetaMarkIsGeneratedHistoryDerivativeLevel
