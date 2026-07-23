module DASHI.Physics.Closure.NSPeriodicPacketFractionQuotientSign where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact sign reduction for the normalized packet-fraction derivative.
--
-- For rho = E_packet / E_total,
--
--   rho' = (E_packet' E_total - E_packet E_total') / E_total^2.
--
-- The PDE estimate therefore belongs on the quotient numerator.  Once the
-- numerator is strictly positive and the total-energy square is positive, the
-- quotient derivative is strictly positive by ordered-field arithmetic.
------------------------------------------------------------------------

record PositiveQuotientArithmetic : Set₁ where
  field
    Scalar : Set
    _/_ : Scalar → Scalar → Scalar
    StrictlyPositive : Scalar → Set

    positiveQuotient : ∀ numerator denominator →
      StrictlyPositive numerator →
      StrictlyPositive denominator →
      StrictlyPositive (numerator / denominator)

open PositiveQuotientArithmetic public

record PacketFractionQuotientSignInputs
    (A : PositiveQuotientArithmetic) : Set₁ where
  field
    packetEnergy totalEnergy : Scalar A
    packetEnergyDerivative totalEnergyDerivative : Scalar A

    quotientDerivativeNumerator totalEnergySquared
      packetFractionDerivative : Scalar A

    quotientDerivativeFormula :
      packetFractionDerivative ≡
      _/_ A quotientDerivativeNumerator totalEnergySquared

    numeratorStrictlyPositive :
      StrictlyPositive A quotientDerivativeNumerator

    totalEnergySquaredStrictlyPositive :
      StrictlyPositive A totalEnergySquared

open PacketFractionQuotientSignInputs public

packetFractionDerivativeStrictlyPositive :
  ∀ {A : PositiveQuotientArithmetic} →
  (Q : PacketFractionQuotientSignInputs A) →
  StrictlyPositive A (packetFractionDerivative Q)
packetFractionDerivativeStrictlyPositive {A = A} Q =
  subst
    (StrictlyPositive A)
    (sym (quotientDerivativeFormula Q))
    (positiveQuotient A
      (quotientDerivativeNumerator Q)
      (totalEnergySquared Q)
      (numeratorStrictlyPositive Q)
      (totalEnergySquaredStrictlyPositive Q))

------------------------------------------------------------------------
-- Status: quotient-sign transport is checked.  The frontier PDE theorem is
-- now exactly strict positivity of
--   E_packet' E_total - E_packet E_total'
-- on the normalized packet-fraction face, with E_total nonzero.
------------------------------------------------------------------------

packetFractionQuotientSignAssemblyLevel : ProofLevel
packetFractionQuotientSignAssemblyLevel = machineChecked
