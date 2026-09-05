module DASHI.Physics.Plasma.MHDPseudoEnergyZeroToEnergyCrossHelicityExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

------------------------------------------------------------------------
-- EXACT DOWNSTREAM ALGEBRA
--
-- At the division-free directional-variation level already used in this lane,
-- total energy is proportional to plus+minus pseudo-energy variation and cross
-- helicity to plus-minus pseudo-energy variation.  Therefore literal zeros of
-- both Elsasser balances force literal zeros of both downstream combinations.
------------------------------------------------------------------------

private
  sub : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

energyCombination :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F
energyCombination {F = F} plus minus = C3.add F plus minus

crossHelicityCombination :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F
crossHelicityCombination plus minus = sub plus minus

pseudoEnergyZerosForceEnergyZero :
  ∀ {r} {F : C3.RealField r}
    (plus minus : C3.Carrier F) →
  plus ≡ C3.zero F →
  minus ≡ C3.zero F →
  energyCombination plus minus ≡ C3.zero F
pseudoEnergyZerosForceEnergyZero {F = F} plus minus hp hm
  rewrite hp | hm =
  R.solve 0
    ((R.Κ (C3.zero F) R.⊕ R.Κ (C3.zero F)) R.⊜ R.Κ (C3.zero F))
    refl
  where module R = Field.Solver F

pseudoEnergyZerosForceCrossHelicityZero :
  ∀ {r} {F : C3.RealField r}
    (plus minus : C3.Carrier F) →
  plus ≡ C3.zero F →
  minus ≡ C3.zero F →
  crossHelicityCombination plus minus ≡ C3.zero F
pseudoEnergyZerosForceCrossHelicityZero {F = F} plus minus hp hm
  rewrite hp | hm =
  R.solve 0
    ((R.Κ (C3.zero F) R.⊕ (R.⊝ R.Κ (C3.zero F)))
      R.⊜ R.Κ (C3.zero F))
    refl
  where module R = Field.Solver F

record PseudoEnergyDownstreamBoundary : Set where
  constructor pseudo-energy-downstream-boundary
  field
    plusZeroAloneForcesCrossHelicityZero : Bool
    plusZeroAloneForcesCrossHelicityZeroIsFalse :
      plusZeroAloneForcesCrossHelicityZero ≡ false

    bothPseudoEnergyZerosForceEnergyAndCrossHelicityZeros : Bool
    bothPseudoEnergyZerosForceEnergyAndCrossHelicityZerosIsTrue :
      bothPseudoEnergyZerosForceEnergyAndCrossHelicityZeros ≡ true

canonicalPseudoEnergyDownstreamBoundary : PseudoEnergyDownstreamBoundary
canonicalPseudoEnergyDownstreamBoundary =
  pseudo-energy-downstream-boundary false refl true refl
