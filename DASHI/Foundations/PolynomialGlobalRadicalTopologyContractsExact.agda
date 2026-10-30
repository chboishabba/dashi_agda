module DASHI.Foundations.PolynomialGlobalRadicalTopologyContractsExact where

------------------------------------------------------------------------
-- UNDISCHARGED GLOBAL THEOREM INTERFACES, NOT POSTULATES / AXIOMS.
--
-- Classical roots: Viete (1591), Riemann (1851), Abel (1824),
-- Galois (1830--32), Jordan (1870), Hamilton (1843).
-- A finite S3 braid IMAGE is not continuous monodromy. A concrete
-- A,B in S5 is not the generic quintic's full Galois representation.
--
-- Each record states the missing exact evidence contract. None is
-- instantiated here. All conclusions are conditional on supplied proofs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.TernaryEndomorphismConjugacyExact as S3

-- Finite root multisets have to be connected to a complex field,
-- a discriminant complement, and a genuine coefficient map.
record PolynomialRootCovering : Set₁ where
  field
    Coefficient : Set
    OrderedRoots : Set
    RegularCoefficient : Coefficient → Set
    coefficientOf : OrderedRoots → Coefficient
    RootLoop : Coefficient → Set
    monodromy : (c : Coefficient) → RootLoop c →
      OrderedRoots → OrderedRoots
    coefficientPreserved :
      (c : Coefficient) (loop : RootLoop c) (roots : OrderedRoots) →
      coefficientOf roots ≡ c →
      coefficientOf (monodromy c loop roots) ≡ c
    discriminantNonzero : (c : Coefficient) → Set
    discriminantCharacterisesRegular :
      (c : Coefficient) →
      RegularCoefficient c → discriminantNonzero c

-- For actual square root topology a nontrivial deck involution
-- has to arise as a lift of a CONTINUOUS coefficient loop.
record SquareRootAnalyticMonodromy : Set₁ where
  field
    Complex : Set
    Root : Set
    Path : Set
    loopAtNonzeroBasepoint : Path
    continuousSquareMap : Root → Complex
    pathLiftsSquareMap : Set
    generatorExchangesSheets : Set
    noGlobalContinuousSection : Set
    windingNumberSoundness : Set

-- These are actual group-theoretic and field-theoretic obligations,
-- not one boolean for "the quintic was proved".
record RadicalSolvabilityAuthority : Set₁ where
  field
    Field : Set
    Polynomial : Set
    RadicalExtension : Set
    SplittingField : Polynomial → Set
    GaloisGroup : Polynomial → Set
    GroupSolvable : Set → Set
    SolvableByRadicals : Polynomial → Set
    radicalTowerGivesSolvableGaloisGroup :
      (p : Polynomial) →
      SolvableByRadicals p →
      GroupSolvable (GaloisGroup p)
    solvableGaloisGroupGivesRadicals :
      (p : Polynomial) →
      GroupSolvable (GaloisGroup p) →
      SolvableByRadicals p

-- A5 perfection + generic S5 group identification are missing
-- independently. The only legal bridge to the general theorem is a
-- conditional implication with both inputs paid.
record GeneralQuinticCriterion : Set₁ where
  field
    GenericQuinticS5 : Set
    S5NonSolvable : Set
    GenericQuinticHasRadicalFormula : Set
    RadicalFormulaImpliesSolvability : Set
    S5ContradictsSolvability :
      GenericQuinticS5 →
      S5NonSolvable →
      RadicalFormulaImpliesSolvability → ⊥
    candidateFormulaProvidesSolvability :
      GenericQuinticHasRadicalFormula →
      RadicalFormulaImpliesSolvability

open GeneralQuinticCriterion public

conditionalGeneralQuinticImpossibility :
  (c : GeneralQuinticCriterion) →
  GenericQuinticS5 c →
  S5NonSolvable c →
  GenericQuinticHasRadicalFormula c → ⊥
conditionalGeneralQuinticImpossibility c s5 nonsolvable formula =
  S5ContradictsSolvability c
    s5 nonsolvable (candidateFormulaProvidesSolvability c formula)

-- A smooth spin double cover requires paths/homotopies and an explicit
-- representation into SO(3). The quaternion q^3=-1 proof does not supply
-- these topological objects.
record SmoothSpinDoubleCoverAuthority : Set₁ where
  field
    SU2 : Set
    SO3 : Set
    SpinPath : Set
    RotationPath : Set
    project : SU2 → SO3
    lift : RotationPath → SpinPath
    kernelIsPlusMinusOne : Set
    liftOf360DegreeLoopEndsAtMinusOne : Set
    liftOf720DegreeLoopEndsAtPlusOne : Set
    nontrivialFundamentalGroupSO3 : Set

-- Ordinary S3 has orientation-reversing permutation matrices for odd
-- permutations on positively oriented (i,j,k). A *proper* SO3 action
-- needs an additional sign correction; the raw positive-axis action is
-- genuinely only C3. This is a representation-compatibility debt.
record S3QuaternionRepresentationExtension : Set₁ where
  field
    signedAxisAction : S3.TriPermutation → Set
    orientationCorrection : (p : S3.TriPermutation) → Set
    actionPreservesQuaternionProduct : Set
    restrictsToExistingC3Conjugation : Set

-- No global theory is inhabited in this source file; consequently none of
-- these high-level bridge records may be treated as discharge receipts.
