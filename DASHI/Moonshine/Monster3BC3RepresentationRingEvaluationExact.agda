module DASHI.Moonshine.Monster3BC3RepresentationRingEvaluationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine", Bulletin of the London Mathematical Society
-- 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- DASHI CONTRIBUTION
--
-- Put the 3B arithmetic in the representation ring of C3.  A balanced
-- character has the form
--
--   residual * 1 + regularMultiplicity * (1 + x + x^2).
--
-- Augmentation gives its dimension; evaluation at a nontrivial generator
-- kills the regular summand and returns the residual.  The coefficient ten
-- is retained as a multiplicity input and is not claimed to be derived.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper
import DASHI.Biology.ReducedFiftyThreeFibreExact as Reduced
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Candidate

record BalancedC3Character : Set where
  constructor balancedC3Character
  field
    residualMultiplicity : Nat
    regularMultiplicity : Nat

open BalancedC3Character public

trivialMultiplicity : BalancedC3Character → Nat
trivialMultiplicity character =
  residualMultiplicity character + regularMultiplicity character

zetaMultiplicity : BalancedC3Character → Nat
zetaMultiplicity character =
  regularMultiplicity character

zetaSquaredMultiplicity : BalancedC3Character → Nat
zetaSquaredMultiplicity character =
  regularMultiplicity character

augmentation : BalancedC3Character → Nat
augmentation character =
  trivialMultiplicity character
  + zetaMultiplicity character
  + zetaSquaredMultiplicity character

generatorTrace : BalancedC3Character → Nat
generatorTrace character =
  residualMultiplicity character

tenFineBlocks : Nat
tenFineBlocks = 10

ternaryDepthEight : Nat
ternaryDepthEight = Hyper.ternaryLatticeCount 8

ternaryDepthEightIs6561 : ternaryDepthEight ≡ 6561
ternaryDepthEightIs6561 = refl

regularBlockMultiplicity : Nat
regularBlockMultiplicity = tenFineBlocks * ternaryDepthEight

regularBlockMultiplicityIs65610 :
  regularBlockMultiplicity ≡ 65610
regularBlockMultiplicityIs65610 = refl

monster3BCharacter : BalancedC3Character
monster3BCharacter =
  balancedC3Character
    Reduced.reducedDimension
    regularBlockMultiplicity

monster3BResidualIs53 :
  residualMultiplicity monster3BCharacter ≡ 53
monster3BResidualIs53 = refl

monster3BTrivialMultiplicityIs65663 :
  trivialMultiplicity monster3BCharacter ≡ 65663
monster3BTrivialMultiplicityIs65663 = refl

monster3BZetaMultiplicityIs65610 :
  zetaMultiplicity monster3BCharacter ≡ 65610
monster3BZetaMultiplicityIs65610 = refl

monster3BZetaSquaredMultiplicityIs65610 :
  zetaSquaredMultiplicity monster3BCharacter ≡ 65610
monster3BZetaSquaredMultiplicityIs65610 = refl

monster3BDimensionIs196883 :
  augmentation monster3BCharacter ≡ 196883
monster3BDimensionIs196883 = refl

monster3BGeneratorTraceIs53 :
  generatorTrace monster3BCharacter ≡ 53
monster3BGeneratorTraceIs53 = refl

moonshineV2Dimension : Nat
moonshineV2Dimension = 1 + augmentation monster3BCharacter

moonshineV2TraceAt3B : Nat
moonshineV2TraceAt3B = 1 + generatorTrace monster3BCharacter

moonshineV2DimensionIs196884 :
  moonshineV2Dimension ≡ 196884
moonshineV2DimensionIs196884 = refl

moonshineV2TraceAt3BIs54 :
  moonshineV2TraceAt3B ≡ 54
moonshineV2TraceAt3BIs54 = refl

candidateBulkMatchesRegularDimension :
  Candidate.bulkDimension
  ≡ 3 * regularBlockMultiplicity
candidateBulkMatchesRegularDimension = refl

characterDimensionMatchesExistingCandidate :
  augmentation monster3BCharacter
  ≡ Candidate.monsterCandidateDimension
characterDimensionMatchesExistingCandidate = refl

record C3EvaluationPair : Set where
  constructor c3EvaluationPair
  field
    identityValue : Nat
    generatorValue : Nat
    identityValueIsAugmentation :
      identityValue ≡ augmentation monster3BCharacter
    generatorValueIsTrace :
      generatorValue ≡ generatorTrace monster3BCharacter

canonicalC3EvaluationPair : C3EvaluationPair
canonicalC3EvaluationPair =
  c3EvaluationPair 196883 53 refl refl

record C3CharacterBoundary : Set where
  constructor c3CharacterBoundary
  field
    coefficientTenDerivedByRepresentationRing : Bool
    coefficientTenDerivedByRepresentationRingIsFalse :
      coefficientTenDerivedByRepresentationRing ≡ false
    dimensionIdentityConstructsMonsterAction : Bool
    dimensionIdentityConstructsMonsterActionIsFalse :
      dimensionIdentityConstructsMonsterAction ≡ false
    traceIdentityConstructsActual3BRestriction : Bool
    traceIdentityConstructsActual3BRestrictionIsFalse :
      traceIdentityConstructsActual3BRestriction ≡ false
    augmentationAndTraceAreTwoEvaluationsOfOneObject : Bool
    augmentationAndTraceAreTwoEvaluationsOfOneObjectIsTrue :
      augmentationAndTraceAreTwoEvaluationsOfOneObject ≡ true

canonicalC3CharacterBoundary : C3CharacterBoundary
canonicalC3CharacterBoundary =
  c3CharacterBoundary false refl false refl false refl true refl
