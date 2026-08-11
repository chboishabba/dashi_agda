module DASHI.Moonshine.Monster3BBalancedRegularFibreExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Organize the certified 3B restriction as one representation-level carrier
-- observed in two ways.  Identity evaluation counts the residual plus all
-- three phases of every regular C3 fibre; nontrivial evaluation cancels the
-- complete regular fibres and retains the coarse residual.  This file records
-- the exact numerical specialization 53 + 3*65610 = 196883 and the conformal
-- extension 1 + 53 = 54.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Multiplicity

record ResidualRegularC3Carrier : Set where
  constructor residualRegularC3Carrier
  field
    residualMultiplicity : Nat
    regularMultiplicity : Nat

open ResidualRegularC3Carrier public

identityEvaluation : ResidualRegularC3Carrier → Nat
identityEvaluation carrier =
  residualMultiplicity carrier + 3 * regularMultiplicity carrier

nontrivialPhaseEvaluation : ResidualRegularC3Carrier → Nat
nontrivialPhaseEvaluation carrier = residualMultiplicity carrier

fixedPhaseMultiplicity : ResidualRegularC3Carrier → Nat
fixedPhaseMultiplicity carrier =
  residualMultiplicity carrier + regularMultiplicity carrier

zetaPhaseMultiplicity : ResidualRegularC3Carrier → Nat
zetaPhaseMultiplicity = regularMultiplicity

zetaSquaredPhaseMultiplicity : ResidualRegularC3Carrier → Nat
zetaSquaredPhaseMultiplicity = regularMultiplicity

balancedRegularFibreNontrivialContribution :
  ResidualRegularC3Carrier → Nat
balancedRegularFibreNontrivialContribution carrier = 0

monster3BRegularMultiplicity : Nat
monster3BRegularMultiplicity = Multiplicity.modelTensorDimension

monster3BRegularMultiplicityIs65610 :
  monster3BRegularMultiplicity ≡ 65610
monster3BRegularMultiplicityIs65610 =
  Multiplicity.modelTensorDimensionIs65610

monster3BResidualRegularCarrier : ResidualRegularC3Carrier
monster3BResidualRegularCarrier =
  residualRegularC3Carrier 53 monster3BRegularMultiplicity

monster3BIdentityEvaluationIs196883 :
  identityEvaluation monster3BResidualRegularCarrier ≡ 196883
monster3BIdentityEvaluationIs196883
  rewrite monster3BRegularMultiplicityIs65610 = refl

monster3BNontrivialEvaluationIs53 :
  nontrivialPhaseEvaluation monster3BResidualRegularCarrier ≡ 53
monster3BNontrivialEvaluationIs53 = refl

monster3BFixedMultiplicityIs65663 :
  fixedPhaseMultiplicity monster3BResidualRegularCarrier ≡ 65663
monster3BFixedMultiplicityIs65663
  rewrite monster3BRegularMultiplicityIs65610 = refl

monster3BZetaMultiplicityIs65610 :
  zetaPhaseMultiplicity monster3BResidualRegularCarrier ≡ 65610
monster3BZetaMultiplicityIs65610 =
  monster3BRegularMultiplicityIs65610

monster3BZetaSquaredMultiplicityIs65610 :
  zetaSquaredPhaseMultiplicity monster3BResidualRegularCarrier ≡ 65610
monster3BZetaSquaredMultiplicityIs65610 =
  monster3BRegularMultiplicityIs65610

monster3BBalancedFineContributionVanishes :
  balancedRegularFibreNontrivialContribution
    monster3BResidualRegularCarrier
  ≡ 0
monster3BBalancedFineContributionVanishes = refl

monster3BConformalDimension : Nat
monster3BConformalDimension =
  1 + identityEvaluation monster3BResidualRegularCarrier

monster3BConformalDimensionIs196884 :
  monster3BConformalDimension ≡ 196884
monster3BConformalDimensionIs196884
  rewrite monster3BIdentityEvaluationIs196883 = refl

monster3BConformalTrace : Nat
monster3BConformalTrace =
  1 + nontrivialPhaseEvaluation monster3BResidualRegularCarrier

monster3BConformalTraceIs54 :
  monster3BConformalTrace ≡ 54
monster3BConformalTraceIs54 = refl

------------------------------------------------------------------------
-- Fine state presence and coarse cancellation are deliberately separate.
------------------------------------------------------------------------

data RepresentationZeroKind : Set where
  emptyRepresentationZero
  balancedEvaluationZero
  invariantNeutralZero : RepresentationZeroKind

record PhaseCompleteFibreObservation : Set where
  constructor phaseCompleteFibreObservation
  field
    fineMultiplicity : Nat
    identityVisibleMultiplicity : Nat
    nontrivialVisibleMultiplicity : Nat
    zeroKindUnderNontrivialEvaluation : RepresentationZeroKind

monster3BBalancedFibreObservation : PhaseCompleteFibreObservation
monster3BBalancedFibreObservation =
  phaseCompleteFibreObservation
    monster3BRegularMultiplicity
    (3 * monster3BRegularMultiplicity)
    0
    balancedEvaluationZero
