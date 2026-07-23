module DASHI.Physics.Closure.NSPeriodicPacketOffDerivativeDuality where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  (_+R_; _*R_; -R_)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using (Polynomial; _:=_; _:+_; _:*_; :-_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact derivative duality between normalized packet and off-packet ratios.
--
-- Let E be total energy and P packet energy.  The packet numerator is
--
--   P' E - P E'.
--
-- The off-packet energy is E-P, so its quotient numerator is
--
--   (E'-P') E - (E-P) E'.
--
-- Polynomial normalization proves that the second numerator is exactly the
-- negative of the first.  Therefore, when packet and off-packet fractions use
-- the same denominator and complementary thresholds, their inward boundary
-- signs are one PDE estimate rather than two independent estimates.
------------------------------------------------------------------------

subR : ℝ → ℝ → ℝ
subR a b = a +R (-R b)

packetQuotientNumeratorR : ℝ → ℝ → ℝ → ℝ → ℝ
packetQuotientNumeratorR packet total packetDerivative totalDerivative =
  subR
    (packetDerivative *R total)
    (packet *R totalDerivative)

offPacketQuotientNumeratorR : ℝ → ℝ → ℝ → ℝ → ℝ
offPacketQuotientNumeratorR packet total packetDerivative totalDerivative =
  subR
    (subR totalDerivative packetDerivative *R total)
    (subR total packet *R totalDerivative)

subP : ∀ {n} → Polynomial n → Polynomial n → Polynomial n
subP a b = a :+ (:- b)

packetQuotientNumeratorP :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
packetQuotientNumeratorP packet total packetDerivative totalDerivative =
  subP
    (packetDerivative :* total)
    (packet :* totalDerivative)

offPacketQuotientNumeratorP :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
offPacketQuotientNumeratorP packet total packetDerivative totalDerivative =
  subP
    (subP totalDerivative packetDerivative :* total)
    (subP total packet :* totalDerivative)

offPacketNumeratorIsNegativePacketNumerator :
  ∀ packet total packetDerivative totalDerivative →
  offPacketQuotientNumeratorR
    packet total packetDerivative totalDerivative
  ≡
  -R (packetQuotientNumeratorR
    packet total packetDerivative totalDerivative)
offPacketNumeratorIsNegativePacketNumerator =
  solveComputed 4
    (λ packet total packetDerivative totalDerivative →
      offPacketQuotientNumeratorP
        packet total packetDerivative totalDerivative
      :=
      (:- packetQuotientNumeratorP
        packet total packetDerivative totalDerivative))
    computed

record PacketOffSignArithmetic : Set₁ where
  field
    Scalar : Set
    negate : Scalar → Scalar
    StrictlyPositive StrictlyNegative : Scalar → Set

    negativeOfPositive : ∀ value →
      StrictlyPositive value →
      StrictlyNegative (negate value)

open PacketOffSignArithmetic public

record PacketOffDerivativeDualityInputs
    (A : PacketOffSignArithmetic) : Set₁ where
  field
    packetNumerator offPacketNumerator : Scalar A

    offIsNegativePacket :
      offPacketNumerator ≡ negate A packetNumerator

    packetNumeratorStrictlyPositive :
      StrictlyPositive A packetNumerator

open PacketOffDerivativeDualityInputs public

packetInwardImpliesOffPacketInward :
  ∀ {A : PacketOffSignArithmetic} →
  (D : PacketOffDerivativeDualityInputs A) →
  StrictlyNegative A (offPacketNumerator D)
packetInwardImpliesOffPacketInward {A = A} D =
  subst
    (StrictlyNegative A)
    (sym (offIsNegativePacket D))
    (negativeOfPositive A
      (packetNumerator D)
      (packetNumeratorStrictlyPositive D))

------------------------------------------------------------------------
-- Status: packet-fraction and off-packet quotient numerators are proved exact
-- negatives in the real carrier.  With the complementary 64/100 and 36/100
-- thresholds, only one strict quotient-numerator PDE estimate remains.
------------------------------------------------------------------------

packetOffDerivativeDualityLevel : ProofLevel
packetOffDerivativeDualityLevel = machineChecked
