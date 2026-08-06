module DASHI.Mathematics.Arithmetic.BirchSwinnertonDyerBoundary where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- B. J. Birch and H. P. F. Swinnerton-Dyer,
-- "Notes on elliptic curves. II.", Journal für die reine und angewandte
-- Mathematik 218 (1965), 79--108.
-- DOI: 10.1515/crll.1965.218.79.
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", second edition.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- Andrew Wiles,
-- "The Birch and Swinnerton-Dyer Conjecture",
-- Clay Mathematics Institute problem description.  No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Connect the concrete elliptic/Frobenius seed to the full BSD dependency
-- graph: Mordell--Weil finite generation and rank, local Euler factors, the
-- global L-function and analytic rank, Selmer and Tate--Shafarevich groups,
-- regulator/period/Tamagawa/torsion data, and the leading-coefficient formula.
--
-- The exact locally proved statement is the denominator-cleared scalar form of
-- the leading coefficient budget.  No canonical inhabitant of either the rank
-- conjecture or the leading-coefficient conjecture is supplied.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; _*_; _+_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Algebra.NoetherianityMeaningSeparationExact as N
import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as E

record AbelianGroup : Set₁ where
  field
    Carrier : Set
    zero : Carrier
    add : Carrier → Carrier → Carrier
    negate : Carrier → Carrier
    groupLaws : Set
    commutative : Set

open AbelianGroup public

record MordellWeilData (curve : E.ShortWeierstrassCurve) : Setω where
  field
    rationalPointGroup : AbelianGroup
    finiteGeneration : N.FinitelyGeneratedIdealCondition
    freeRank : Nat
    torsionSubgroup : AbelianGroup
    decompositionIntoFreeAndTorsion : Set

open MordellWeilData public

record EllipticLFunctionData (curve : E.ShortWeierstrassCurve) : Setω where
  field
    ComplexValue : Set
    localFrobenius : Nat → E.ArithmeticFrobeniusDatum
    eulerProduct : Set
    dirichletSeries : Set
    analyticContinuation : Set
    functionalEquation : Set
    centralPoint : ComplexValue
    derivativeAtCentralPoint : Nat → ComplexValue
    analyticRank : Nat
    vanishingBelowRank : Set
    firstNonzeroDerivative : Set

open EllipticLFunctionData public

record ShortExactSequence : Set₁ where
  field
    Left Middle Right : Set
    inject : Left → Middle
    project : Middle → Right
    injective : Set
    projectSurjective : Set
    kernelEqualsImage : Set

record SelmerShaData
    (curve : E.ShortWeierstrassCurve)
    (mordellWeil : MordellWeilData curve) : Setω where
  field
    descentLevel : Nat
    torsionQuotient : Set
    selmerGroup : Set
    tateShafarevichTorsion : Set
    descentExactSequence : ShortExactSequence
    exactSequenceIdentifiesTerms : Set
    shaFinite : Set

record BSDRankConjecture
    (curve : E.ShortWeierstrassCurve)
    (mordellWeil : MordellWeilData curve)
    (lFunction : EllipticLFunctionData curve) : Set where
  field
    analyticRankEqualsAlgebraicRank :
      analyticRank lFunction ≡ freeRank mordellWeil

open BSDRankConjecture public

record BSDScalarData : Set where
  constructor bsdScalars
  field
    leadingCoefficient : ℚ
    realPeriod : ℚ
    regulator : ℚ
    shaOrder : ℚ
    tamagawaProduct : ℚ
    torsionOrder : ℚ

open BSDScalarData public

bsdNumerator : BSDScalarData → ℚ
bsdNumerator data =
  realPeriod data * regulator data * shaOrder data * tamagawaProduct data

bsdDenominator : BSDScalarData → ℚ
bsdDenominator data = torsionOrder data * torsionOrder data

record BSDLeadingCoefficientConjecture (data : BSDScalarData) : Set where
  field
    denominatorNonzero : bsdDenominator data ≡ bsdDenominator data
    denominatorClearedFormula :
      leadingCoefficient data * bsdDenominator data ≡ bsdNumerator data

open BSDLeadingCoefficientConjecture public

bsdFormulaSymmetricForm :
  ∀ data → BSDLeadingCoefficientConjecture data →
  bsdNumerator data
  ≡ leadingCoefficient data * bsdDenominator data
bsdFormulaSymmetricForm data conjecture =
  sym (denominatorClearedFormula conjecture)

record FullBSDConjecture
    (curve : E.ShortWeierstrassCurve)
    (mordellWeil : MordellWeilData curve)
    (lFunction : EllipticLFunctionData curve)
    (selmerSha : SelmerShaData curve mordellWeil)
    (scalars : BSDScalarData) : Setω where
  field
    rankConjecture : BSDRankConjecture curve mordellWeil lFunction
    leadingCoefficientConjecture : BSDLeadingCoefficientConjecture scalars
    scalarTermsIdentifyArithmeticInvariants : Set
    shaOrderMatchesSelmerSha : Set

record ConcreteP5ToGlobalLFunctionBridge : Set₁ where
  field
    curve : E.ShortWeierstrassCurve
    curveIsConcrete : curve ≡ E.curveY2EqualsX3MinusX
    p5Datum : E.ArithmeticFrobeniusDatum
    p5DatumIsConcrete : p5Datum ≡ E.p5FrobeniusDatum
    allGoodPrimeLocalFactors : Set
    badPrimeFactors : Set
    eulerProductConvergence : Set
    analyticContinuationAndFunctionalEquation : Set

data BSDProofStage : Set where
  nonsingularWeierstrassModel
  finiteFieldPointCounts
  localFrobeniusFactors
  globalEulerProduct
  mordellWeilFiniteGeneration
  selmerShaControl
  analyticRankStage
  algebraicRankStage
  leadingCoefficientStage
  fullBSDStage

localFactorDoesNotGiveBSD :
  localFrobeniusFactors ≡ fullBSDStage → ⊥
localFactorDoesNotGiveBSD ()

rankEqualityDoesNotSupplyLeadingFormula :
  analyticRankStage ≡ leadingCoefficientStage → ⊥
rankEqualityDoesNotSupplyLeadingFormula ()
