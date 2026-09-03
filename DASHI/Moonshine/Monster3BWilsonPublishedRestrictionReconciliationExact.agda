module DASHI.Moonshine.Monster3BWilsonPublishedRestrictionReconciliationExact where

------------------------------------------------------------------------
-- WILSON 1988 PUBLISHED 3B-NORMALIZER RESTRICTION
--
-- Primary source:
-- R. A. Wilson, "The odd-local subgroups of the Monster",
-- J. Austral. Math. Soc. 44 (1988), 1--16.
-- DOI: 10.1017/S1446788700031323.
--
-- Wilson states that the degree-196883 Monster character restricts to the
-- 3B-local subgroup in the degree pattern
--
--   143 + 65520 + (729 + 729') * (12 + 78).
--
-- with 12, 78, 143 faithful irreducibles at the indicated Suzuki-cover
-- levels, 729/729' extending the two faithful nonlinear extraspecial
-- characters, and 65520 a faithful monomial representation of 3^12:2Suz.
--
-- DASHI keeps this published normalizer decomposition distinct from the
-- central-C3 character decomposition
--
--   196883 = 53 + 3 * 65610.
--
-- Their dimensions reconcile through the arithmetic transfer quantity 90:
--
--   65610 = 65520 + 90,
--   143   = 90 + 53.
--
-- This DOES NOT construct a Suz-stable 90+53 split of the irreducible 143.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

------------------------------------------------------------------------
-- 1. Published degree pattern.
------------------------------------------------------------------------

suzTwelve : Nat
suzTwelve = 12

suzSeventyEight : Nat
suzSeventyEight = 78

suzOneFortyThree : Nat
suzOneFortyThree = 143

linearOrbitMonomial : Nat
linearOrbitMonomial = 65520

heisenbergDegree : Nat
heisenbergDegree = 729

multiplicityNinety : Nat
multiplicityNinety = suzTwelve + suzSeventyEight

twelvePlusSeventyEightIsNinety : multiplicityNinety ≡ 90
twelvePlusSeventyEightIsNinety = refl

pairedNontrivialPhaseDegree : Nat
pairedNontrivialPhaseDegree =
  (heisenbergDegree + heisenbergDegree) * multiplicityNinety

pairedNontrivialPhaseDegreeIs131220 :
  pairedNontrivialPhaseDegree ≡ 131220
pairedNontrivialPhaseDegreeIs131220 = refl

fixedNormalizerDegree : Nat
fixedNormalizerDegree = linearOrbitMonomial + suzOneFortyThree

fixedNormalizerDegreeIs65663 : fixedNormalizerDegree ≡ 65663
fixedNormalizerDegreeIs65663 = refl

wilsonRestrictionDegree : Nat
wilsonRestrictionDegree = fixedNormalizerDegree + pairedNontrivialPhaseDegree

wilsonRestrictionDegreeIs196883 : wilsonRestrictionDegree ≡ 196883
wilsonRestrictionDegreeIs196883 = refl

------------------------------------------------------------------------
-- 2. Reconciliation with the central-C3 character observer.
------------------------------------------------------------------------

balancedPhaseMultiplicity : Nat
balancedPhaseMultiplicity = 65610

centralResidual : Nat
centralResidual = 53

ninetyTransferFromLinearOrbit :
  linearOrbitMonomial + 90 ≡ balancedPhaseMultiplicity
ninetyTransferFromLinearOrbit = refl

ninetyTransferIntoOneFortyThree :
  90 + centralResidual ≡ suzOneFortyThree
ninetyTransferIntoOneFortyThree = refl

fixedObserverReconciliation :
  linearOrbitMonomial + suzOneFortyThree
  ≡ balancedPhaseMultiplicity + centralResidual
fixedObserverReconciliation = refl

centralC3WholeDegree :
  centralResidual + 3 * balancedPhaseMultiplicity ≡ 196883
centralC3WholeDegree = refl

------------------------------------------------------------------------
-- 3. Authority boundary.
------------------------------------------------------------------------

record WilsonRestrictionBoundary : Set where
  constructor wilsonRestrictionBoundary
  field
    wilsonRestrictionPatternSourceBacked : Bool
    twelvePlusSeventyEightSourceBacked : Bool
    fixed65520Plus143SourceBacked : Bool
    degree143SourceBackedAsSuzIrreducible : Bool
    degree65520SourceBackedAsCentreTrivialMonomial : Bool
    centralC3Residual53SourceBackedByTraceRestriction : Bool
    ninetyTransferArithmeticExact : Bool
    ninetyTransferIsPublishedAsInvariantSubmodule : Bool
    suzStableNinetyPlusFiftyThreeSplitOf143 : Bool
    fullNormalizerStableResidual53Owned : Bool

canonicalWilsonRestrictionBoundary : WilsonRestrictionBoundary
canonicalWilsonRestrictionBoundary =
  wilsonRestrictionBoundary
    true true true true true true true
    false false false

------------------------------------------------------------------------
-- 4. Consequence.
--
-- Normalizer-native observer:
--   W_1 = 65520 + 143.
--
-- Central-C3 multiplicity observer:
--   W_1 = 65610 + 53.
--
-- The second equality is a character/multiplicity balancing statement, not a
-- direct-sum refinement of the first under Suz.  Any future 53-module claim
-- must therefore name a smaller actor/subgroup and prove the restriction of
-- the 143 constituent actually admits the required invariant subspace.
------------------------------------------------------------------------
