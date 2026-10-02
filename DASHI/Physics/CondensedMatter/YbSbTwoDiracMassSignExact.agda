module DASHI.Physics.CondensedMatter.YbSbTwoDiracMassSignExact where

------------------------------------------------------------------------
-- ATTRIBUTION
--
-- SOURCE — Kataria et al., arXiv:2601.07460 / PRL accepted 3 Aug 2026:
-- * simplified effective model uses isotropic b and m;
-- * source criterion: mb > 0 trivial, mb < 0 nontrivial;
-- * Figure 3 parameters: b = 0.5, m = -0.7.
--
-- DASHI DERIVATION:
-- * encode the selected values with integer numerator / positive
--   denominator data;
-- * prove their product sign is negative by finite sign arithmetic.
--
-- We do NOT derive the physical topology criterion here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

data Sign : Set where
  negative zero positive : Sign

mulSign : Sign → Sign → Sign
mulSign negative negative = positive
mulSign negative zero = zero
mulSign negative positive = negative
mulSign zero s = zero
mulSign positive negative = negative
mulSign positive zero = zero
mulSign positive positive = positive

record SignedRationalParameter : Set where
  constructor parameter
  field
    sign : Sign
    numerator denominator : Set

open SignedRationalParameter public

-- Exact source decimal signs and rational magnitudes:
-- b = + 1/2, m = - 7/10.
data One : Set where one : One
data Two : Set where two : Two
data Seven : Set where seven : Seven
data Ten : Set where ten : Ten

paperB : SignedRationalParameter
paperB = parameter positive One Two

paperM : SignedRationalParameter
paperM = parameter negative Seven Ten

paperMassProductSign :
  mulSign (sign paperM) (sign paperB) ≡ negative
paperMassProductSign = refl

record DiracMassTopologySourceLaw : Set₁ where
  field
    TopologicallyNontrivial : Set
    negativeMassProductImpliesNontrivial :
      mulSign (sign paperM) (sign paperB) ≡ negative →
      TopologicallyNontrivial

open DiracMassTopologySourceLaw public

paperParametersSatisfySourceNontrivialRegime :
  (L : DiracMassTopologySourceLaw) →
  TopologicallyNontrivial L
paperParametersSatisfySourceNontrivialRegime L =
  negativeMassProductImpliesNontrivial L paperMassProductSign
