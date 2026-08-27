module DASHI.Analysis.RiemannG21PoleQuotientedExteriorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannHermitianTopDownAssemblyExact as G1G4
import DASHI.Analysis.PoleQuotientedExteriorDeskTestExact as Exterior
import DASHI.Analysis.RiemannG21PrimePairKernelExact as Pair
import DASHI.Analysis.RiemannG21TwoByTwoMixedObstructionExact as Mixed2

------------------------------------------------------------------------
-- G21: pole-quotiented two-channel exterior explicit-formula programme.
--
-- This is intentionally stacked on the existing Hermitian RH branch.  It is
-- a new post-G20 architecture, not a claim that the G1--G4 programme or RH is
-- complete.  The key change of observer is:
--
--   one transported Weil channel
--      -> three samples of two channels
--      -> quotient by the known one-dimensional pole profile
--      -> exterior orientation of the two residual channels.
--
-- The first literal analytic target is the 3x3 augmented determinant
--
--   det [ S1(x1) S1(x2) S1(x3)
--         S2(x1) S2(x2) S2(x3)
--          m(x1)  m(x2)  m(x3) ]
--
-- and the crucial identity is that after S_i = c_i m + E_i the determinant
-- equals det[E1;E2;m] exactly, with no surviving MxE term.
------------------------------------------------------------------------

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
  g21ObligationEntry
    commonPoleProfileFactorization
    analyticInterfaceOpen
    "Choose literal Weil test channels whose deterministic pole responses factor through one common profile m(x). This must be established from the literal explicit formula, not postulated from the finite desk-test carrier."

poleQuotientIdentityEntry : G21ObligationEntry
poleQuotientIdentityEntry =
  g21ObligationEntry
    augmentedDeterminantPoleQuotientIdentity
    analyticInterfaceOpen
    "After literal common-pole factorization, prove the 3x3 augmented determinant equals the residual determinant det[E1;E2;m], thereby annihilating pure-pole and mixed pole/error contributions before estimation."

zeroRankEntry : G21ObligationEntry
zeroRankEntry =
  g21ObligationEntry
    offLineZeroRankTwoInPoleQuotient
    analyticInterfaceOpen
    "For an off-critical-line zero, prove the two residual zero channels remain rank two after quotienting by the pole profile, preferably with an explicit determinant floor depending on the off-line displacement."

explicitFormulaEntry : G21ObligationEntry
explicitFormulaEntry =
  g21ObligationEntry
    literalTwoChannelExplicitFormulaExpansion
    arithmeticInterfaceOpen
    "Substitute both literal explicit formulas before majorization and derive the surviving double von-Mangoldt pair expression exactly."

diagonalZeroEntry : G21ObligationEntry
diagonalZeroEntry =
  g21ObligationEntry
    literalPrimePairDiagonalZero
    arithmeticInterfaceOpen
    "For a derivative/contrastive second channel, derive the expected log(n/m)-type factor and prove K(n,n)=0 on the literal prime-pair kernel."

nonseparableEntry : G21ObligationEntry
nonseparableEntry =
  g21ObligationEntry
    literalPrimePairRelationalNonseparability
    arithmeticInterfaceOpen
    "Prove a rectangle violation and preferably a nonzero 2x2 minor for the literal prime-pair kernel; pair-valued syntax alone is not sufficient."

swapEntry : G21ObligationEntry
swapEntry =
  g21ObligationEntry
    exactSwapReindexBeforeMajorization
    arithmeticInterfaceOpen
    "Partition the exact finite pair carrier into diagonal and swapped off-diagonal fibres and perform the permutation/reindex cancellation or doubling before any absolute-value bound."

scaleEntry : G21ObligationEntry
scaleEntry =
  g21ObligationEntry
    primePairScaleDecision
    arithmeticInterfaceOpen
    "Only after the exact algebraic cancellations are exposed, compare the trivial surviving prime-pair scale with the zero-side determinant floor and kill the lane immediately if the ratio diverges."

canonicalG21Obligations : List G21ObligationEntry
canonicalG21Obligations =
  commonPoleEntry
  ∷ poleQuotientIdentityEntry
  ∷ zeroRankEntry
  ∷ explicitFormulaEntry
  ∷ diagonalZeroEntry
  ∷ nonseparableEntry
  ∷ swapEntry
  ∷ scaleEntry
  ∷ []

------------------------------------------------------------------------
-- Exact structural results already obtained in this tranche.
------------------------------------------------------------------------

threeMinusOneLeavesTwo :
  Exterior.residualDimension
    Exterior.canonicalExteriorQuotientDimensionReceipt
  ≡ 2
threeMinusOneLeavesTwo =
  Exterior.residualDimensionIsTwo
    Exterior.canonicalExteriorQuotientDimensionReceipt

naiveTwoByTwoRankOnePoleGateRejected :
  Mixed2.det2Code Mixed2.responseLeft Mixed2.responseRight
  ≡ Mixed2.det2Code Mixed2.commonPole Mixed2.commonPole
  → ⊥
naiveTwoByTwoRankOnePoleGateRejected =
  Mixed2.rankOnePoleDoesNotKillMixedTwoByTwoDeterminant

primePairRelationalAdmissionCriterionIsNonVacuous :
  Pair.PrimePairRelationalAdmission
primePairRelationalAdmissionCriterionIsNonVacuous =
  Pair.canonicalToyPrimePairRelationalAdmission

pairSwapIsInvolutive :
  {A : Set} →
  (p : Pair.Pair A) →
  Pair.swapPair (Pair.swapPair p) ≡ p
pairSwapIsInvolutive = Pair.swapPairInvolutive

------------------------------------------------------------------------
-- Current proof boundary.
------------------------------------------------------------------------

record G21CurrentBoundary : Set where
  constructor g21CurrentBoundary
  field
    newObserverUsesPoleQuotientExteriorCoordinate : Bool
    newObserverUsesPoleQuotientExteriorCoordinateIsTrue :
      newObserverUsesPoleQuotientExteriorCoordinate ≡ true

    twoByTwoMixedTermObstructionDerived : Bool
    twoByTwoMixedTermObstructionDerivedIsTrue :
      twoByTwoMixedTermObstructionDerived ≡ true

    literalAugmentedDeterminantIdentityDerived : Bool
    literalAugmentedDeterminantIdentityDerivedIsFalse :
      literalAugmentedDeterminantIdentityDerived ≡ false

    offLineZeroRankTwoDerived : Bool
    offLineZeroRankTwoDerivedIsFalse :
      offLineZeroRankTwoDerived ≡ false

    literalPrimePairKernelDerived : Bool
    literalPrimePairKernelDerivedIsFalse :
      literalPrimePairKernelDerived ≡ false

    favorableScaleGateDerived : Bool
    favorableScaleGateDerivedIsFalse :
      favorableScaleGateDerived ≡ false

    riemannHypothesisDerived : Bool
    riemannHypothesisDerivedIsFalse :
      riemannHypothesisDerived ≡ false

canonicalG21CurrentBoundary : G21CurrentBoundary
canonicalG21CurrentBoundary =
  g21CurrentBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
