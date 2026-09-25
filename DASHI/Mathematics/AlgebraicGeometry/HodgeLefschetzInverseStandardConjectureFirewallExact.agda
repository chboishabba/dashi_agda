module DASHI.Mathematics.AlgebraicGeometry.HodgeLefschetzInverseStandardConjectureFirewallExact where

------------------------------------------------------------------------
-- HODGE FIREWALL: COHOMOLOGICAL LEFSCHETZ INVERSE != ALGEBRAIC INVERSE
--
-- Hard Lefschetz supplies an inverse on cohomology.  That does NOT by itself
-- supply an algebraic correspondence realizing the inverse.
--
-- A proposed primitive-class proof can silently cross this boundary by using
-- an "inverse Lefschetz operator" on cycle representatives.  This owner makes
-- the distinction type-level on the frozen rational Hodge / literal algebraic
-- cycle carriers.
--
-- The cohomological inverse below returns only a rational Hodge class.
-- The algebraic inverse below must return a literal rational algebraic cycle
-- and prove the exact rational singular cycle-class equation.
--
-- The latter is therefore already a cycle-producing theorem, not background
-- linear algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.HodgeRationalClassIntersectionExact as Exact
import DASHI.Mathematics.AlgebraicGeometry.HodgeAlgebraicCycleClayCoreExact as Clay

------------------------------------------------------------------------
-- Purely cohomological Lefschetz data.
------------------------------------------------------------------------

record CohomologicalLefschetzStep
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (codimension : Nat) : Set₁ where
  field
    raiseClass :
      Exact.RationalHodgeClassExact hodge codimension →
      Exact.RationalHodgeClassExact hodge (suc codimension)

    lowerClass :
      Exact.RationalHodgeClassExact hodge (suc codimension) →
      Exact.RationalHodgeClassExact hodge codimension

    lowerAfterRaise :
      (alpha :
        Exact.RationalHodgeClassExact hodge codimension) →
      lowerClass (raiseClass alpha) ≡ alpha

open CohomologicalLefschetzStep public

------------------------------------------------------------------------
-- Cycle-level inverse realization.
--
-- This is the dangerous extra assumption: it consumes a literal cycle
-- representing the raised class and manufactures a literal cycle representing
-- the original class.
------------------------------------------------------------------------

record AlgebraicLefschetzInverseRealization
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge)
    (codimension : Nat)
    (cohomological :
      CohomologicalLefschetzStep codimension) : Set₁ where
  field
    lowerCycle :
      (alpha :
        Exact.RationalHodgeClassExact hodge codimension) →
      Hodge.RationalAlgebraicCycle
        variety
        (suc codimension) →
      Hodge.RationalAlgebraicCycle
        variety
        codimension

    lowerCycleClassExact :
      (alpha :
        Exact.RationalHodgeClassExact hodge codimension) →
      (raisedCycle :
        Hodge.RationalAlgebraicCycle
          variety
          (suc codimension)) →
      Clay.singularCycleClass
          cycleBackground
          (suc codimension)
          raisedCycle
      ≡
      Exact.singularClass
        (raiseClass cohomological alpha) →
      Clay.singularCycleClass
          cycleBackground
          codimension
          (lowerCycle alpha raisedCycle)
      ≡
      Exact.singularClass alpha

open AlgebraicLefschetzInverseRealization public

------------------------------------------------------------------------
-- The algebraic inverse is already a literal cycle producer.
------------------------------------------------------------------------

algebraicInverseProducesOriginalCycle :
  ∀ {variety comparison hodge}
    {cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge}
    {codimension : Nat}
    {cohomological :
      CohomologicalLefschetzStep codimension} →
  (algebraicInverse :
    AlgebraicLefschetzInverseRealization
      cycleBackground
      codimension
      cohomological) →
  (alpha :
    Exact.RationalHodgeClassExact hodge codimension) →
  Σ
    (Hodge.RationalAlgebraicCycle
      variety
      (suc codimension))
    (λ raisedCycle →
      Clay.singularCycleClass
          cycleBackground
          (suc codimension)
          raisedCycle
      ≡
      Exact.singularClass
        (raiseClass cohomological alpha)) →
  Σ
    (Hodge.RationalAlgebraicCycle
      variety
      codimension)
    (λ cycle →
      Clay.singularCycleClass
          cycleBackground
          codimension
          cycle
      ≡
      Exact.singularClass alpha)
algebraicInverseProducesOriginalCycle
    algebraicInverse
    alpha
    raisedProducer =
  lowerCycle algebraicInverse
      alpha
      (proj₁ raisedProducer)
  ,
  lowerCycleClassExact
    algebraicInverse
    alpha
    (proj₁ raisedProducer)
    (proj₂ raisedProducer)

------------------------------------------------------------------------
-- If raised classes already have algebraic representatives, an algebraic
-- Lefschetz inverse closes the lower-codimension Clay core immediately.
--
-- This theorem is the firewall: any mechanism that cites such an algebraic
-- inverse has already imported exactly the kind of cycle-producing statement
-- the Hodge lane is searching for.
------------------------------------------------------------------------

RaisedClassAlgebraicProducer :
  ∀ {variety comparison hodge}
    (cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge)
    {codimension : Nat} →
  CohomologicalLefschetzStep codimension →
  Set₁
RaisedClassAlgebraicProducer
    {variety = variety}
    cycleBackground
    {codimension}
    cohomological =
  (alpha :
    Exact.RationalHodgeClassExact hodge codimension) →
  Σ
    (Hodge.RationalAlgebraicCycle
      variety
      (suc codimension))
    (λ raisedCycle →
      Clay.singularCycleClass
          cycleBackground
          (suc codimension)
          raisedCycle
      ≡
      Exact.singularClass
        (raiseClass cohomological alpha))

algebraicInversePlusRaisedProducerGivesClayCore :
  ∀ {variety comparison hodge}
    {cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge}
    {codimension : Nat}
    {cohomological :
      CohomologicalLefschetzStep codimension} →
  AlgebraicLefschetzInverseRealization
    cycleBackground
    codimension
    cohomological →
  RaisedClassAlgebraicProducer
    cycleBackground
    cohomological →
  Clay.HodgeClayCoreAtCodimensionAlgebraicExact
    cycleBackground
    codimension
algebraicInversePlusRaisedProducerGivesClayCore
    algebraicInverse
    raisedProducer =
  record
    { Clay.algebraicRepresentative =
        λ alpha →
          proj₁
            (algebraicInverseProducesOriginalCycle
              algebraicInverse
              alpha
              (raisedProducer alpha))
    ; Clay.algebraicRepresentativeHasExactRationalClass =
        λ alpha →
          proj₂
            (algebraicInverseProducesOriginalCycle
              algebraicInverse
              alpha
              (raisedProducer alpha))
    }

------------------------------------------------------------------------
-- HODGE MECHANISM AUDIT CONSEQUENCE
--
-- Safe established background:
--
--   cohomological raise/lower + inverse law.
--
-- NOT safe to import as "Hard Lefschetz background":
--
--   a cycle-level lowerCycle with exact cycle-class compatibility.
--
-- The latter directly manufactures literal algebraic representatives and can
-- close the frozen Clay core once the raised class is represented.  It must
-- therefore be counted as a conjectural/cycle-producing mechanism unless
-- independently established by a theorem stronger than ordinary Hard
-- Lefschetz.
------------------------------------------------------------------------
