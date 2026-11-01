module DASHI.Physics.Closure.NSTriadKNGlobalDangerBarrierEquivalenceRound105Exact where

------------------------------------------------------------------------
-- ROUND105 / ANTI-CIRCULARITY THEOREM
--
-- The global positive part is the correct LAST place to discard sign, but it
-- is not by itself a new analytic mechanism.  Under the exact critical energy
-- identity
--
--   X_T + nu D = X_0 + N,
--
-- one has identically
--
--   N + delta D = X_T + (nu+delta)D - X_0.
--
-- Therefore an endpoint estimate
--
--   N + delta D <= F
--
-- is equivalent to
--
--   X_T + (nu+delta)D <= X_0 + F.
--
-- A physical proof must obtain the former from an INDEPENDENT mechanism such
-- as packet-boundary flux cancellation plus Waleffe phase residence/network
-- replenishment.  Merely packaging the left side as `globalDanger` would rename
-- the desired critical barrier and be circular.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

record ExactCriticalEnergyIdentity : Set where
  constructor exact-critical-energy-identity
  field
    initialCritical terminalCritical dissipation production viscosity : ℚ
    energyIdentity :
      terminalCritical + viscosity * dissipation
      ≡ initialCritical + production

open ExactCriticalEnergyIdentity public

criticalBarrierExcess : ℚ → ExactCriticalEnergyIdentity → ℚ
criticalBarrierExcess delta E =
  terminalCritical E + (viscosity E + delta) * dissipation E
    - initialCritical E

integratedSignedSurplus : ℚ → ExactCriticalEnergyIdentity → ℚ
integratedSignedSurplus delta E = production E + delta * dissipation E

signedSurplusIsCriticalBarrierExcess :
  (delta : ℚ) (E : ExactCriticalEnergyIdentity) →
  integratedSignedSurplus delta E ≡ criticalBarrierExcess delta E
signedSurplusIsCriticalBarrierExcess delta E =
  let
    base :
      terminalCritical E + viscosity E * dissipation E
      - initialCritical E
      ≡ production E
    base =
      trans
        (cong (_- initialCritical E) (energyIdentity E))
        (solve (initialCritical E ∷ production E ∷ []))
  in
  trans
    (sym
      (cong
        (λ p → p + delta * dissipation E)
        base))
    (solve
      ( terminalCritical E ∷ viscosity E ∷ dissipation E
      ∷ initialCritical E ∷ production E ∷ delta ∷ []))

signedSurplusBoundImpliesCriticalBarrier :
  (delta remainder : ℚ) (E : ExactCriticalEnergyIdentity) →
  integratedSignedSurplus delta E ≤ remainder →
  terminalCritical E + (viscosity E + delta) * dissipation E
    ≤ initialCritical E + remainder
signedSurplusBoundImpliesCriticalBarrier delta remainder E surplusBound =
  let
    excessBound : criticalBarrierExcess delta E ≤ remainder
    excessBound =
      subst
        (_≤ remainder)
        (signedSurplusIsCriticalBarrierExcess delta E)
        surplusBound

    shifted :
      criticalBarrierExcess delta E + initialCritical E
      ≤ remainder + initialCritical E
    shifted = ℚP.+-mono-≤ excessBound ℚP.≤-refl

    leftMeaning :
      criticalBarrierExcess delta E + initialCritical E
      ≡ terminalCritical E + (viscosity E + delta) * dissipation E
    leftMeaning =
      solve
        ( terminalCritical E ∷ viscosity E ∷ delta
        ∷ dissipation E ∷ initialCritical E ∷ [])

    rightMeaning :
      remainder + initialCritical E ≡ initialCritical E + remainder
    rightMeaning = solve (remainder ∷ initialCritical E ∷ [])
  in
  subst
    (λ left → left ≤ initialCritical E + remainder)
    leftMeaning
    (subst
      (λ right → criticalBarrierExcess delta E + initialCritical E ≤ right)
      rightMeaning shifted)

criticalBarrierImpliesSignedSurplusBound :
  (delta remainder : ℚ) (E : ExactCriticalEnergyIdentity) →
  terminalCritical E + (viscosity E + delta) * dissipation E
    ≤ initialCritical E + remainder →
  integratedSignedSurplus delta E ≤ remainder
criticalBarrierImpliesSignedSurplusBound delta remainder E barrier =
  let
    shifted :
      terminalCritical E + (viscosity E + delta) * dissipation E
        - initialCritical E
      ≤ initialCritical E + remainder - initialCritical E
    shifted = ℚP.+-mono-≤ barrier ℚP.≤-refl

    rightMeaning : initialCritical E + remainder - initialCritical E ≡ remainder
    rightMeaning = solve (initialCritical E ∷ remainder ∷ [])

    excessBound : criticalBarrierExcess delta E ≤ remainder
    excessBound =
      subst
        (λ right → criticalBarrierExcess delta E ≤ right)
        rightMeaning shifted
  in
  subst
    (_≤ remainder)
    (sym (signedSurplusIsCriticalBarrierExcess delta E))
    excessBound

round105GlobalSignedSurplusBarrierEquivalent : Bool
round105GlobalSignedSurplusBarrierEquivalent = true

round105GlobalDangerAloneIsIndependentMechanism : Bool
round105GlobalDangerAloneIsIndependentMechanism = false

round105IndependentPacketPhasePaymentStillRequired : Bool
round105IndependentPacketPhasePaymentStillRequired = true

round105GlobalSignedSurplusBarrierEquivalentIsTrue :
  round105GlobalSignedSurplusBarrierEquivalent ≡ true
round105GlobalSignedSurplusBarrierEquivalentIsTrue = refl

round105GlobalDangerAloneIsIndependentMechanismIsFalse :
  round105GlobalDangerAloneIsIndependentMechanism ≡ false
round105GlobalDangerAloneIsIndependentMechanismIsFalse = refl

round105IndependentPacketPhasePaymentStillRequiredIsTrue :
  round105IndependentPacketPhasePaymentStillRequired ≡ true
round105IndependentPacketPhasePaymentStillRequiredIsTrue = refl
