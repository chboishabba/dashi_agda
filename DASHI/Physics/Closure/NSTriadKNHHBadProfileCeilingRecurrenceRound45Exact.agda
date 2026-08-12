module DASHI.Physics.Closure.NSTriadKNHHBadProfileCeilingRecurrenceRound45Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 45 identified the scale-neutral bad profile C_q = 2^q g_q.  The
-- attached analysis suggested that the highest-alpha way to prove a uniform
-- ceiling may be a one-step shell recurrence rather than independent shell
-- estimates.  This module proves the exact ordered-field criterion.
--
-- If
--
--   0 <= C_q,
--   0 <= alpha < 1,
--   0 <= beta,
--   C_{q+1} <= alpha C_q + beta,
--   C_0 <= M,
--   beta <= (1-alpha) M,
--
-- then C_q <= M for every q.
--
-- No division by 1-alpha is required.  Thus a physical recurrence with a
-- subunit contraction and bounded forcing gives exactly the uniform normalized
-- profile needed by the HH-bad owner lane.  The still-open PDE task is to
-- derive such a recurrence (or a direct ceiling) on the literal physical C_q.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record ContractiveProfileRecurrence : Set where
  field
    profile : Nat → ℚ
    alpha beta ceiling : ℚ

    profileNonnegative : ∀ q → 0ℚ ≤ profile q
    alphaNonnegative : 0ℚ ≤ alpha
    alphaStrict : alpha < 1ℚ
    betaNonnegative : 0ℚ ≤ beta
    ceilingNonnegative : 0ℚ ≤ ceiling

    baseBelowCeiling : profile zero ≤ ceiling
    recurrence : ∀ q →
      profile (suc q) ≤ alpha * profile q + beta

    forcingFitsCeiling :
      beta ≤ (1ℚ - alpha) * ceiling

open ContractiveProfileRecurrence public

recurrenceStepPreservesCeiling :
  (data : ContractiveProfileRecurrence) →
  ∀ q →
  profile data q ≤ ceiling data →
  profile data (suc q) ≤ ceiling data
recurrenceStepPreservesCeiling data q currentBelow =
  let
    alphaScaled :
      alpha data * profile data q
      ≤ alpha data * ceiling data
    alphaScaled =
      let instance alphaNNI = nonNegative (alphaNonnegative data)
      in ℚP.*-monoˡ-≤-nonNeg (alpha data) currentBelow

    addBeta :
      alpha data * profile data q + beta data
      ≤ alpha data * ceiling data + beta data
    addBeta = ℚP.+-mono-≤ alphaScaled ℚP.≤-refl

    addForcingBound :
      alpha data * ceiling data + beta data
      ≤ alpha data * ceiling data
        + (1ℚ - alpha data) * ceiling data
    addForcingBound =
      ℚP.+-monoʳ-≤
        (alpha data * ceiling data)
        (forcingFitsCeiling data)

    collapse :
      alpha data * ceiling data
        + (1ℚ - alpha data) * ceiling data
      ≡ ceiling data
    collapse = solve (alpha data ∷ ceiling data ∷ [])
  in
  ℚP.≤-trans (recurrence data q)
    (ℚP.≤-trans addBeta
      (ℚP.≤-trans addForcingBound
        (subst
          (λ upper →
            alpha data * ceiling data
              + (1ℚ - alpha data) * ceiling data
            ≤ upper)
          collapse
          ℚP.≤-refl)))

contractiveRecurrenceUniformCeiling :
  (data : ContractiveProfileRecurrence) →
  ∀ q → profile data q ≤ ceiling data
contractiveRecurrenceUniformCeiling data zero = baseBelowCeiling data
contractiveRecurrenceUniformCeiling data (suc q) =
  recurrenceStepPreservesCeiling data q
    (contractiveRecurrenceUniformCeiling data q)

hhBadProfileRecurrenceCriterionClosed : Bool
hhBadProfileRecurrenceCriterionClosed = true

hhBadProfileRecurrenceCriterionClosedIsTrue :
  hhBadProfileRecurrenceCriterionClosed ≡ true
hhBadProfileRecurrenceCriterionClosedIsTrue = refl
