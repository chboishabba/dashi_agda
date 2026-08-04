module DASHI.Physics.YangMills.BalabanP33WeightedNeumannHalfContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Specialize the existing weighted finite-Neumann induction to the explicit
-- rational target rho_mu = 1/2.  Once a physical weighted residual supplies
-- this contraction, the abstract monoid power becomes the literal geometric
-- power 2^{-n} and the repository theorem yields
--
--   ||R_mu^n x||_mu <= 2^{-n} ||x||_mu.
--
-- This does not assert the physical contraction; it removes all subsequent
-- algebraic ambiguity after that estimate is proved.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 1ℚ; _*_; _≤_; _<_; _/_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteNeumannParametrix as Neumann
import DASHI.Physics.YangMills.BalabanWeightedNeumannRemainder as Weighted

oneHalf : ℚ
oneHalf = + 1 / 2

halfPower : Nat → ℚ
halfPower zero = 1ℚ
halfPower (suc depth) = halfPower depth * oneHalf

boundPowerEqualsHalfPower :
  ∀ {Carrier}
    {bundle : Neumann.AdditiveParametrixData Carrier}
    (control : Weighted.WeightedResidualContraction Carrier ℚ bundle) →
  Weighted.oneBound control ≡ 1ℚ →
  (∀ left right →
    Weighted.multiplyBound control left right ≡ left * right) →
  Weighted.contractionFactor control ≡ oneHalf →
  ∀ depth →
  Weighted.boundPower control depth ≡ halfPower depth
boundPowerEqualsHalfPower control oneMeaning multiplyMeaning factorMeaning zero =
  oneMeaning
boundPowerEqualsHalfPower control oneMeaning multiplyMeaning factorMeaning
    (suc depth) =
  trans
    (cong₂ (Weighted.multiplyBound control)
      (boundPowerEqualsHalfPower
        control oneMeaning multiplyMeaning factorMeaning depth)
      factorMeaning)
    (multiplyMeaning (halfPower depth) oneHalf)

halfContractionIsStrict :
  ∀ {Carrier}
    {bundle : Neumann.AdditiveParametrixData Carrier}
    (control : Weighted.WeightedResidualContraction Carrier ℚ bundle) →
  Weighted.StrictLess control ≡ _<_ →
  Weighted.oneBound control ≡ 1ℚ →
  Weighted.contractionFactor control ≡ oneHalf →
  oneHalf < 1ℚ
halfContractionIsStrict control strictMeaning oneMeaning factorMeaning =
  subst
    (λ upper → oneHalf < upper)
    oneMeaning
    (subst
      (λ lower → lower < Weighted.oneBound control)
      factorMeaning
      (subst
        (λ relation → relation
          (Weighted.contractionFactor control)
          (Weighted.oneBound control))
        strictMeaning
        (Weighted.contractionStrict control)))

weightedResidualHalfPowerBound :
  ∀ {Carrier}
    {bundle : Neumann.AdditiveParametrixData Carrier}
    (control : Weighted.WeightedResidualContraction Carrier ℚ bundle) →
  Weighted.LessEqual control ≡ _≤_ →
  Weighted.oneBound control ≡ 1ℚ →
  (∀ left right →
    Weighted.multiplyBound control left right ≡ left * right) →
  Weighted.contractionFactor control ≡ oneHalf →
  ∀ depth value →
  Weighted.norm control (Neumann.residualPower bundle depth value)
  ≤ halfPower depth * Weighted.norm control value
weightedResidualHalfPowerBound
    {bundle = bundle}
    control orderMeaning oneMeaning multiplyMeaning factorMeaning depth value =
  subst
    (λ upper →
      Weighted.norm control (Neumann.residualPower bundle depth value)
      ≤ upper)
    (trans
      (multiplyMeaning
        (Weighted.boundPower control depth)
        (Weighted.norm control value))
      (cong
        (λ coefficient → coefficient * Weighted.norm control value)
        (boundPowerEqualsHalfPower
          control oneMeaning multiplyMeaning factorMeaning depth)))
    (subst
      (λ relation → relation
        (Weighted.norm control
          (Neumann.residualPower bundle depth value))
        (Weighted.multiplyBound control
          (Weighted.boundPower control depth)
          (Weighted.norm control value)))
      orderMeaning
      (Weighted.weightedResidualPowerBound control depth value))

weightedNeumannHalfContractionLevel : ProofLevel
weightedNeumannHalfContractionLevel = machineChecked

weightedNeumannHalfPowerLevel : ProofLevel
weightedNeumannHalfPowerLevel = machineChecked
