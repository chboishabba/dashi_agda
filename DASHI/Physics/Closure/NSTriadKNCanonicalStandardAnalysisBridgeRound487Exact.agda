module DASHI.Physics.Closure.NSTriadKNCanonicalStandardAnalysisBridgeRound487Exact where

------------------------------------------------------------------------
-- ROUND487 / CANONICAL STANDARD-ANALYSIS BRIDGE
--
-- R486 isolates the only genuinely new periodic NS estimate as the R423
-- cutoff-uniform signed quadratic-companion budget.  This module removes a
-- different source of bookkeeping ambiguity: it factors the R393 temporal
-- realization into (a) all already-owned algebra/integrability data and
-- (b) exactly one ordinary FTC equality, so a Lean/mathlib proof can be
-- inserted without rebuilding the temporal carrier.
--
-- Lean source:
--   DASHI/output-final_aristotle/RequestProject/NavierStokes/
--     CanonicalCompletionLeaves.lean
-- theorem:
--   DASHI.NavierStokes.CanonicalLeaves.offDiagonalFundamentalTheorem
--
-- The Simon / weak-* source instances remain explicit R148/R104 obligations.
-- Nothing in this module manufactures the open R423 estimate.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_)

import DASHI.Physics.Closure.NSTriadKNLiteralR378TemporalIntegrationBoundaryRound393Exact as R393
import DASHI.Physics.Closure.NSTriadKNCriticalSimonUpgradeFollowsBarrierRound148Exact as R148
import DASHI.Physics.Closure.NSTriadKNCanonicalClayProofSearchRound486Exact as R486

record LiteralR378TemporalPreFTC {t : Level} (Time : Set t) : Set (lsuc t) where
  field
    initialTime finalTime : Time

    literalGlobalGramDebt : Time → ℚ
    literalOffDiagonalFlux : Time → ℚ
    literalOffDiagonalFluxTangent : Time → ℚ
    literalWeightedRemainder : Time → ℚ

    instantaneousR392Identity :
      (τ : Time) →
      literalGlobalGramDebt τ
      ≡ (0ℚ - literalOffDiagonalFluxTangent τ)
          + literalWeightedRemainder τ

    Integrable : (Time → ℚ) → Set
    Integral : (Time → ℚ) → ℚ

    gramDebtIntegrable : Integrable literalGlobalGramDebt
    fluxTangentIntegrable : Integrable literalOffDiagonalFluxTangent
    negatedFluxTangentIntegrable :
      Integrable (λ τ → 0ℚ - literalOffDiagonalFluxTangent τ)
    weightedRemainderIntegrable : Integrable literalWeightedRemainder

    integralCongruence :
      ∀ {f g} → ((τ : Time) → f τ ≡ g τ) → Integral f ≡ Integral g

    integralAdditive :
      ∀ {f g} → Integrable f → Integrable g →
      Integral (λ τ → f τ + g τ) ≡ Integral f + Integral g

    integralNegation :
      ∀ {f} → Integrable f →
      Integral (λ τ → 0ℚ - f τ) ≡ 0ℚ - Integral f

open LiteralR378TemporalPreFTC public

record LeanR393FTCReceipt {t : Level} {Time : Set t}
    (P : LiteralR378TemporalPreFTC Time) : Set where
  field
    offDiagonalFundamentalTheorem :
      Integral P (literalOffDiagonalFluxTangent P)
      ≡ literalOffDiagonalFlux P (finalTime P)
          - literalOffDiagonalFlux P (initialTime P)

open LeanR393FTCReceipt public

installLeanR393FTC :
  ∀ {t} {Time : Set t} →
  (P : LiteralR378TemporalPreFTC Time) →
  LeanR393FTCReceipt P →
  R393.LiteralR378TemporalRealization Time
installLeanR393FTC P ftc = record
  { R393.initialTime = initialTime P
  ; R393.finalTime = finalTime P
  ; R393.literalGlobalGramDebt = literalGlobalGramDebt P
  ; R393.literalOffDiagonalFlux = literalOffDiagonalFlux P
  ; R393.literalOffDiagonalFluxTangent = literalOffDiagonalFluxTangent P
  ; R393.literalWeightedRemainder = literalWeightedRemainder P
  ; R393.instantaneousR392Identity = instantaneousR392Identity P
  ; R393.Integrable = Integrable P
  ; R393.Integral = Integral P
  ; R393.gramDebtIntegrable = gramDebtIntegrable P
  ; R393.fluxTangentIntegrable = fluxTangentIntegrable P
  ; R393.negatedFluxTangentIntegrable = negatedFluxTangentIntegrable P
  ; R393.weightedRemainderIntegrable = weightedRemainderIntegrable P
  ; R393.integralCongruence = integralCongruence P
  ; R393.integralAdditive = integralAdditive P
  ; R393.integralNegation = integralNegation P
  ; R393.offDiagonalFundamentalTheorem =
      offDiagonalFundamentalTheorem ftc
  }

------------------------------------------------------------------------
-- Honest completion-state surface.
------------------------------------------------------------------------

round487LeanFTCSourceTheoremInstalled : Bool
round487LeanFTCSourceTheoremInstalled = true

round487R393SameObjectReceiptStillNeedsInstantiation : Bool
round487R393SameObjectReceiptStillNeedsInstantiation = true

round487SimonSourceInstanceInstalled : Bool
round487SimonSourceInstanceInstalled =
  R148.round148AgdaAnalyticSourceInstancesInstalled

round487WeakStarSourceInstanceInstalled : Bool
round487WeakStarSourceInstanceInstalled =
  R148.round148AgdaAnalyticSourceInstancesInstalled

round487R423StillCanonicalFirstNovelResidual : Bool
round487R423StillCanonicalFirstNovelResidual =
  R486.round486R423IsCanonicalShortestConsumer

round487LeanFTCSourceTheoremInstalledIsTrue :
  round487LeanFTCSourceTheoremInstalled ≡ true
round487LeanFTCSourceTheoremInstalledIsTrue = refl

round487R393SameObjectReceiptStillNeedsInstantiationIsTrue :
  round487R393SameObjectReceiptStillNeedsInstantiation ≡ true
round487R393SameObjectReceiptStillNeedsInstantiationIsTrue = refl

round487R423StillCanonicalFirstNovelResidualIsTrue :
  round487R423StillCanonicalFirstNovelResidual ≡ true
round487R423StillCanonicalFirstNovelResidualIsTrue =
  R486.round486R423IsCanonicalShortestConsumerIsTrue
