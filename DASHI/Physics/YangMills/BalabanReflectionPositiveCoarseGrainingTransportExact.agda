module DASHI.Physics.YangMills.BalabanReflectionPositiveCoarseGrainingTransportExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Konrad Osterwalder and Erhard Seiler,
-- "Gauge Field Theories on a Lattice", Annals of Physics 110 (1978),
-- 440--471. DOI: 10.1016/0003-4916(78)90039-8.
--
-- P. Menotti and A. Pelissetto,
-- "General Proof of Osterwalder-Schrader Positivity for the Wilson Action",
-- Communications in Mathematical Physics 113 (1987), 369--373.
-- DOI: 10.1007/BF01221251.
--
-- DASHI CONTRIBUTION
--
-- Positive transition weights are NOT enough for reflection positivity (the
-- companion no-go module gives an exact 2-state counterexample).  There is,
-- however, a genuine compression available: reflection positivity transports
-- through a coarse-graining pullback if the block map
--
--   * sends coarse positive-time observables to fine positive-time observables;
--   * commutes with reflection;
--   * preserves the product used in the reflected quadratic form; and
--   * defines the coarse expectation by pullback of the fine expectation.
--
-- Thus, once Wilson lattice RP is supplied by Osterwalder--Seiler / Menotti--
-- Pelissetto on the SAME carrier, one does not have to re-prove RP separately
-- after every Bałaban blocking step.  The new physical producer is the exact
-- reflection/half-space compatibility of the literal block map.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record ReflectionPositiveFunctional (Observable : Set) : Set₁ where
  field
    positiveTime : Observable → Set
    reflect : Observable → Observable
    multiply : Observable → Observable → Observable
    expectation : Observable → ℚ
    reflectionPositive : ∀ observable →
      positiveTime observable →
      0ℚ ≤ expectation (multiply (reflect observable) observable)
open ReflectionPositiveFunctional public

record ReflectionCompatibleCoarseGraining
    (Fine Coarse : Set)
    (fine : ReflectionPositiveFunctional Fine) : Set₁ where
  field
    pullback : Coarse → Fine
    coarsePositiveTime : Coarse → Set
    coarseReflect : Coarse → Coarse
    coarseMultiply : Coarse → Coarse → Coarse
    pullbackPositiveTime : ∀ observable →
      coarsePositiveTime observable →
      positiveTime fine (pullback observable)
    pullbackReflectExact : ∀ observable →
      pullback (coarseReflect observable)
      ≡ reflect fine (pullback observable)
    pullbackMultiplyExact : ∀ left right →
      pullback (coarseMultiply left right)
      ≡ multiply fine (pullback left) (pullback right)
open ReflectionCompatibleCoarseGraining public

coarseExpectation :
  ∀ {Fine Coarse}
    {fine : ReflectionPositiveFunctional Fine} →
  ReflectionCompatibleCoarseGraining Fine Coarse fine →
  Coarse → ℚ
coarseExpectation {fine = fine} coarse observable =
  expectation fine (pullback coarse observable)

coarseReflectedQuadraticPullsBackExact :
  ∀ {Fine Coarse}
    {fine : ReflectionPositiveFunctional Fine}
    (coarse : ReflectionCompatibleCoarseGraining Fine Coarse fine)
    observable →
  coarseExpectation coarse
    (coarseMultiply coarse (coarseReflect coarse observable) observable)
  ≡ expectation fine
      (multiply fine (reflect fine (pullback coarse observable))
        (pullback coarse observable))
coarseReflectedQuadraticPullsBackExact {fine = fine} coarse observable =
  trans
    (cong (expectation fine)
      (pullbackMultiplyExact coarse
        (coarseReflect coarse observable) observable))
    (cong
      (λ reflected → expectation fine
        (multiply fine reflected (pullback coarse observable)))
      (pullbackReflectExact coarse observable))

coarseReflectionPositive :
  ∀ {Fine Coarse}
    {fine : ReflectionPositiveFunctional Fine}
    (coarse : ReflectionCompatibleCoarseGraining Fine Coarse fine)
    observable →
  coarsePositiveTime coarse observable →
  0ℚ ≤ coarseExpectation coarse
    (coarseMultiply coarse (coarseReflect coarse observable) observable)
coarseReflectionPositive {fine = fine} coarse observable positive =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (coarseReflectedQuadraticPullsBackExact coarse observable))
    (reflectionPositive fine
      (pullback coarse observable)
      (pullbackPositiveTime coarse observable positive))

reflectionCompatibleCoarseGrainingPreservesRPLevel : ProofLevel
reflectionCompatibleCoarseGrainingPreservesRPLevel = machineChecked

literalBalabanBlockReflectionCompatibilityLevel : ProofLevel
literalBalabanBlockReflectionCompatibilityLevel = conditional
