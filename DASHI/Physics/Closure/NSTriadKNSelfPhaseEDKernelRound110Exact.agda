module DASHI.Physics.Closure.NSTriadKNSelfPhaseEDKernelRound110Exact where

------------------------------------------------------------------------
-- ROUND110 / SELF-PHASE ENERGY-DISSIPATION KERNEL
--
-- Pure ordered rational algebra behind the physical Lean Round110 theorem.
-- If
--
--   M <= E_p E_q,
--   gap <= omega_p^2 + omega_q^2,
--
-- with all quantities nonnegative, then
--
--   gap M
--     <= (omega_p^2 E_p) E_q + E_p (omega_q^2 E_q).
--
-- Thus, once the physical helical-eigenvalue/frequency bound and projected
-- cross-mass bound are supplied, one self-phase leg is paid by the standard
-- modal D_p E_q + E_p D_q kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

productNonnegative : ∀ {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
productNonnegative {a} {b} aNN bNN =
  let
    instance
      aNNI = nonNegative aNN
      bNNI = nonNegative bNN
      abNNI = ℚP.nonNeg*nonNeg⇒nonNeg a b
  in ℚP.nonNegative⁻¹ (a * b)

selfPhaseBelowEDKernel :
  (gap omegaP2 omegaQ2 energyP energyQ crossMass : ℚ) →
  0ℚ ≤ gap → 0ℚ ≤ omegaP2 → 0ℚ ≤ omegaQ2 →
  0ℚ ≤ energyP → 0ℚ ≤ energyQ → 0ℚ ≤ crossMass →
  gap ≤ omegaP2 + omegaQ2 →
  crossMass ≤ energyP * energyQ →
  gap * crossMass
  ≤ (omegaP2 * energyP) * energyQ
      + energyP * (omegaQ2 * energyQ)
selfPhaseBelowEDKernel gap omegaP2 omegaQ2 energyP energyQ crossMass
    gapNN omegaPNN omegaQNN energyPNN energyQNN crossNN gapBound crossBound =
  let
    energyProductNN = productNonnegative energyPNN energyQNN

    first : gap * crossMass ≤ gap * (energyP * energyQ)
    first =
      let instance gapNNI = nonNegative gapNN
      in ℚP.*-monoˡ-≤-nonNeg gap crossBound

    second :
      gap * (energyP * energyQ)
      ≤ (omegaP2 + omegaQ2) * (energyP * energyQ)
    second =
      let instance energyProductNNI = nonNegative energyProductNN
      in ℚP.*-monoʳ-≤-nonNeg (energyP * energyQ) gapBound

    endpoint :
      (omegaP2 + omegaQ2) * (energyP * energyQ)
      ≡ (omegaP2 * energyP) * energyQ
          + energyP * (omegaQ2 * energyQ)
    endpoint = solve
      (omegaP2 ∷ omegaQ2 ∷ energyP ∷ energyQ ∷ [])
  in
  ℚP.≤-trans first
    (ℚP.≤-trans second
      (subst
        (λ upper →
          (omegaP2 + omegaQ2) * (energyP * energyQ) ≤ upper)
        endpoint ℚP.≤-refl))

round110SelfPhaseEDKernelClosed : Bool
round110SelfPhaseEDKernelClosed = true

round110SelfPhaseEDKernelClosedIsTrue :
  round110SelfPhaseEDKernelClosed ≡ true
round110SelfPhaseEDKernelClosedIsTrue = refl
