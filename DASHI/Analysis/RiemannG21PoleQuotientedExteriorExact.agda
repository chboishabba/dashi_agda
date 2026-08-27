module DASHI.Analysis.RiemannG21PoleQuotientedExteriorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannHermitianTopDownAssemblyExact as G1G4
import DASHI.Analysis.PoleQuotientedExteriorDeskTestExact as Exterior
import DASHI.Analysis.RiemannG21PrimePairKernelExact as Pair
import DASHI.Analysis.RiemannG21TwoByTwoMixedObstructionExact as Mixed2
import DASHI.Analysis.RiemannG21AugmentedDeterminantFiniteExact as Det3

data G21Obligation : Set where
  commonPoleProfileFactorization : G21Obligation
  augmentedDeterminantPoleQuotientIdentity : G21Obligation
  offLineZeroRankTwoInPoleQuotient : G21Obligation
  literalTwoChannelExplicitFormulaExpansion : G21Obligation
  literalPrimePairDiagonalZero : G21Obligation
  literalPrimePairRelationalNonseparability : G21Obligation
  exactSwapReindexBeforeMajorization : G21Obligation
  primePairScaleDecision : G21Obligation

data G21Status : Set where
  structurallyDerived : G21Status
  analyticInterfaceOpen : G21Status
  arithmeticInterfaceOpen : G21Status
  rejectedByExactCounterexample : G21Status

record G21ObligationEntry : Set where
  constructor g21ObligationEntry
  field
    obligation : G21Obligation
    status : G21Status
    reading : String

open G21ObligationEntry public

commonPoleEntry : G21ObligationEntry
commonPoleEntry =
  g21ObligationEntry commonPoleProfileFactorization analyticInterfaceOpen
    "Choose literal Weil channels whose deterministic pole responses factor through one common profile m(x)."

poleQuotientIdentityEntry : G21ObligationEntry
poleQuotientIdentityEntry =
  g21ObligationEntry augmentedDeterminantPoleQuotientIdentity analyticInterfaceOpen
    "Prove on the literal Weil carrier that the 3x3 augmented determinant equals det[E1;E2;m], annihilating pure-pole and mixed pole/error terms before estimation."

zeroRankEntry : G21ObligationEntry
zeroRankEntry =
  g21ObligationEntry offLineZeroRankTwoInPoleQuotient analyticInterfaceOpen
    "For an off-critical-line zero, prove the two residual zero channels remain rank two after quotienting by the pole profile, preferably with an explicit determinant floor."

explicitFormulaEntry : G21ObligationEntry
explicitFormulaEntry =
  g21ObligationEntry literalTwoChannelExplicitFormulaExpansion arithmeticInterfaceOpen
    "Substitute both literal explicit formulas before majorization and derive the surviving double von-Mangoldt pair expression exactly."

diagonalZeroEntry : G21ObligationEntry
diagonalZeroEntry =
  g21ObligationEntry literalPrimePairDiagonalZero arithmeticInterfaceOpen
    "For a derivative/contrastive channel derive the log(n/m)-type factor and prove K(n,n)=0 on the literal pair kernel."

nonseparableEntry : G21ObligationEntry
nonseparableEntry =
  g21ObligationEntry literalPrimePairRelationalNonseparability arithmeticInterfaceOpen
    "Prove a rectangle violation and preferably a nonzero 2x2 minor for the literal pair kernel."

swapEntry : G21ObligationEntry
swapEntry =
  g21ObligationEntry exactSwapReindexBeforeMajorization arithmeticInterfaceOpen
    "Split the exact pair carrier into diagonal and swapped off-diagonal fibres and reindex before any absolute-value bound."

scaleEntry : G21ObligationEntry
scaleEntry =
  g21ObligationEntry primePairScaleDecision arithmeticInterfaceOpen
    "Compare the trivial surviving pair scale with the zero-side determinant floor and kill the lane immediately if the ratio diverges."

canonicalG21Obligations : List G21ObligationEntry
canonicalG21Obligations =
  commonPoleEntry ∷ poleQuotientIdentityEntry ∷ zeroRankEntry
  ∷ explicitFormulaEntry ∷ diagonalZeroEntry ∷ nonseparableEntry
  ∷ swapEntry ∷ scaleEntry ∷ []

threeMinusOneLeavesTwo :
  Exterior.residualDimension Exterior.canonicalExteriorQuotientDimensionReceipt ≡ 2
threeMinusOneLeavesTwo =
  Exterior.residualDimensionIsTwo Exterior.canonicalExteriorQuotientDimensionReceipt

naiveTwoByTwoRankOnePoleGateRejected :
  Mixed2.det2Code Mixed2.responseLeft Mixed2.responseRight
  ≡ Mixed2.det2Code Mixed2.commonPole Mixed2.commonPole → ⊥
naiveTwoByTwoRankOnePoleGateRejected =
  Mixed2.rankOnePoleDoesNotKillMixedTwoByTwoDeterminant

finiteThreeByThreePoleQuotientMechanism :
  Det3.SameSignedDeterminant
    (Det3.det3 Det3.response₁ Det3.response₂ Det3.poleProfile)
    (Det3.det3 Det3.residual₁ Det3.residual₂ Det3.poleProfile)
finiteThreeByThreePoleQuotientMechanism =
  Det3.augmentedPoleQuotientPreservesSignedDeterminant

primePairRelationalAdmissionCriterionIsNonVacuous : Pair.PrimePairRelationalAdmission
primePairRelationalAdmissionCriterionIsNonVacuous = Pair.canonicalToyPrimePairRelationalAdmission

pairSwapIsInvolutive :
  {A : Set} → (p : Pair.Pair A) → Pair.swapPair (Pair.swapPair p) ≡ p
pairSwapIsInvolutive = Pair.swapPairInvolutive

record G21CurrentBoundary : Set where
  constructor g21CurrentBoundary
  field
    newObserverUsesPoleQuotientExteriorCoordinate : Bool
    newObserverUsesPoleQuotientExteriorCoordinateIsTrue :
      newObserverUsesPoleQuotientExteriorCoordinate ≡ true
    twoByTwoMixedTermObstructionDerived : Bool
    twoByTwoMixedTermObstructionDerivedIsTrue :
      twoByTwoMixedTermObstructionDerived ≡ true
    finiteThreeByThreePoleQuotientMechanismDerived : Bool
    finiteThreeByThreePoleQuotientMechanismDerivedIsTrue :
      finiteThreeByThreePoleQuotientMechanismDerived ≡ true
    literalAugmentedDeterminantIdentityDerived : Bool
    literalAugmentedDeterminantIdentityDerivedIsFalse :
      literalAugmentedDeterminantIdentityDerived ≡ false
    offLineZeroRankTwoDerived : Bool
    offLineZeroRankTwoDerivedIsFalse : offLineZeroRankTwoDerived ≡ false
    literalPrimePairKernelDerived : Bool
    literalPrimePairKernelDerivedIsFalse : literalPrimePairKernelDerived ≡ false
    favorableScaleGateDerived : Bool
    favorableScaleGateDerivedIsFalse : favorableScaleGateDerived ≡ false
    riemannHypothesisDerived : Bool
    riemannHypothesisDerivedIsFalse : riemannHypothesisDerived ≡ false

canonicalG21CurrentBoundary : G21CurrentBoundary
canonicalG21CurrentBoundary =
  g21CurrentBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
