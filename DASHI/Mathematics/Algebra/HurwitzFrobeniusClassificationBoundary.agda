module DASHI.Mathematics.Algebra.HurwitzFrobeniusClassificationBoundary where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Adolf Hurwitz,
-- "Über die Komposition der quadratischen Formen",
-- Mathematische Annalen 88 (1923), 1--25.
-- DOI: 10.1007/BF01448439.
--
-- Matej Bresar and Victor S. Shulman,
-- "On, around, and beyond Frobenius' theorem on division algebras",
-- Linear and Multilinear Algebra 70 (2022), 1369--1381.
-- DOI: 10.1080/03081087.2020.1761281.
--
-- Aleksandra Galecka,
-- "A Proof of the Hurwitz Theorem About Composition Algebras".
-- DOI: 10.24917/20809751.13.4.
--
-- DASHI CONTRIBUTION
--
-- State the proof-obligation boundaries of the two classical classification
-- theorems without importing either theorem as a receipt.
--
-- Frobenius requires a finite-dimensional associative real division algebra
-- and concludes dimension 1, 2 or 4 together with classification up to real-
-- algebra isomorphism by R, C or H.
--
-- Hurwitz requires a finite-dimensional real algebra with a positive-definite
-- multiplicative quadratic norm and division, and concludes dimension
-- 1, 2, 4 or 8 together with classification by R, C, H or O.
--
-- The records below make every hypothesis and every conclusion explicit.  No
-- inhabitant of the theorem records is supplied here.  The exact rational
-- quaternion/octonion polynomial modules discharge concrete algebraic laws but
-- do not manufacture real scalar structure, finite-dimensionality, positivity,
-- division or classification isomorphisms.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Mathematics.Algebra.HurwitzFrobeniusLawProfileExact
  using (FrobeniusDimension; HurwitzDimension)

record FrobeniusHypotheses : Set₁ where
  field
    fCarrier : Set
    fRealVectorSpaceStructure : Set
    fDimension : Nat
    fFiniteDimensional : Set
    fMultiplication : fCarrier → fCarrier → fCarrier
    fUnitElement : fCarrier
    fAssociativeMultiplication : Set
    fDistributiveRealAlgebraLaws : Set
    fNonzeroElementsInvertible : Set

open FrobeniusHypotheses public

record FrobeniusConclusion
    (hypotheses : FrobeniusHypotheses) : Set₁ where
  field
    fAllowedDimension :
      FrobeniusDimension (fDimension hypotheses)
    fClassifiedAsRealComplexOrQuaternion : Set
    fClassificationIsRealAlgebraIsomorphism : Set

record HurwitzHypotheses : Set₁ where
  field
    hCarrier : Set
    hRealVectorSpaceStructure : Set
    hDimension : Nat
    hFiniteDimensional : Set
    hMultiplication : hCarrier → hCarrier → hCarrier
    hUnitElement : hCarrier
    hDistributiveRealAlgebraLaws : Set
    hQuadraticNorm : hCarrier → Set
    hNormIsRealValued : Set
    hNormPositiveDefinite : Set
    hNormMultiplicative : Set
    hNonzeroElementsInvertible : Set

open HurwitzHypotheses public

record HurwitzConclusion
    (hypotheses : HurwitzHypotheses) : Set₁ where
  field
    hAllowedDimension :
      HurwitzDimension (hDimension hypotheses)
    hClassifiedAsRealComplexQuaternionOrOctonion : Set
    hClassificationPreservesAlgebraAndNorm : Set

record FrobeniusClassificationTheorem : Set₂ where
  field
    classifyFrobenius :
      (hypotheses : FrobeniusHypotheses) →
      FrobeniusConclusion hypotheses

record HurwitzClassificationTheorem : Set₂ where
  field
    classifyHurwitz :
      (hypotheses : HurwitzHypotheses) →
      HurwitzConclusion hypotheses

record ClassificationTheoremBoundary : Set₂ where
  field
    frobeniusTheorem : FrobeniusClassificationTheorem
    hurwitzTheorem : HurwitzClassificationTheorem

record ConcreteRationalAlgebraEvidence : Set₁ where
  field
    rationalCarrier : Set
    multiplicationAndConjugationLaws : Set
    multiplicativeQuadraticNormIdentity : Set

record MissingRealAnalyticClassificationEvidence : Set₁ where
  field
    realScalarExtension : Set
    finiteDimensionProof : Set
    positiveDefiniteRealNorm : Set
    divisionProof : Set
    exhaustiveClassificationProof : Set

record ConcreteToClassificationBridge : Set₁ where
  field
    concreteEvidence : ConcreteRationalAlgebraEvidence
    missingEvidence : MissingRealAnalyticClassificationEvidence

-- ConcreteToClassificationBridge deliberately requires the missing evidence;
-- there is no function from ConcreteRationalAlgebraEvidence alone to either
-- classical classification theorem conclusion.
