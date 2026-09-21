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
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)

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



------------------------------------------------------------------------
-- Shell identity -> every finite partial sum, mechanically.
------------------------------------------------------------------------

literalGeneratedHistoryPartial :
  LiteralBetaHistoryShellIdentification → Nat → ℚ
literalGeneratedHistoryPartial dataSet zero = 0ℚ
literalGeneratedHistoryPartial dataSet (suc depth) =
  literalGeneratedHistoryPartial dataSet depth
  + literalGeneratedHistoryShell dataSet depth

literalGeneratedHistoryPartialIsCMP116BetaPartial :
  (dataSet : LiteralBetaHistoryShellIdentification) →
  ∀ depth →
  literalGeneratedHistoryPartial dataSet depth
  ≡ Shared.betaHistoryPartial
      (shared dataSet) (scale dataSet) (volume dataSet) (root dataSet) depth
literalGeneratedHistoryPartialIsCMP116BetaPartial dataSet zero = refl
literalGeneratedHistoryPartialIsCMP116BetaPartial dataSet (suc depth)
  rewrite literalGeneratedHistoryPartialIsCMP116BetaPartial dataSet depth
        | literalGeneratedHistoryShellIsCMP116BetaMark dataSet depth =
  refl

asRound116MarkedDerivative :
  LiteralBetaHistoryShellIdentification →
  R116.LiteralBetaHistoryMarkedDerivative
asRound116MarkedDerivative dataSet = record
  { R116.LiteralBetaHistoryMarkedDerivative.Scale = Scale dataSet
  ; R116.LiteralBetaHistoryMarkedDerivative.Volume = Volume dataSet
  ; R116.LiteralBetaHistoryMarkedDerivative.Root = Root dataSet
  ; R116.LiteralBetaHistoryMarkedDerivative.shared = shared dataSet
  ; R116.LiteralBetaHistoryMarkedDerivative.scale = scale dataSet
  ; R116.LiteralBetaHistoryMarkedDerivative.volume = volume dataSet
  ; R116.LiteralBetaHistoryMarkedDerivative.root = root dataSet
  ; R116.LiteralBetaHistoryMarkedDerivative.literalHistoryDerivativePartial =
      literalGeneratedHistoryPartial dataSet
  ; R116.LiteralBetaHistoryMarkedDerivative.literalHistoryDerivativeIsBetaMark =
      literalGeneratedHistoryPartialIsCMP116BetaPartial dataSet
  }

literalGeneratedHistoryPartialBound :
  (dataSet : LiteralBetaHistoryShellIdentification) →
  ∀ depth →
  literalGeneratedHistoryPartial dataSet depth
  Data.Rational.Base.≤
  R116.historyDerivativeConstant (asRound116MarkedDerivative dataSet)
literalGeneratedHistoryPartialBound dataSet =
  R116.literalHistoryDerivativePartialBound
    (asRound116MarkedDerivative dataSet)

-- The current R116 partial-sum carrier is a downstream summary.  This module
-- records the strictly earlier same-object coordinate; list/sum transport from
-- the shell identity is generic compiler work and not a new physical theorem.

a2BetaMarkSourceCoordinateCompilerBoundaryLevel : ProofLevel
a2BetaMarkSourceCoordinateCompilerBoundaryLevel = machineChecked

a2ShellIdentityToPartialSumCompilerLevel : ProofLevel
a2ShellIdentityToPartialSumCompilerLevel = machineChecked

-- No concrete constructor of `betaHistoryShell` was found elsewhere in-repo.
-- This is the current literal CMP116/source-history realization wall.
literalCMP116BetaMarkIsGeneratedHistoryShellLevel : ProofLevel
literalCMP116BetaMarkIsGeneratedHistoryShellLevel = conditional

-- Compatibility: the older coarse partial-sum equality is now constructed
-- directly from the shell-level same-object statement above.  It is no longer
-- an independent physical leaf.
legacyPartialSumIdentificationLevel : ProofLevel
legacyPartialSumIdentificationLevel = machineChecked
