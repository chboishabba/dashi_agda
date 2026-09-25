module DASHI.Mathematics.AlgebraicGeometry.HodgePrimitiveLefschetzClayReductionExact where

------------------------------------------------------------------------
-- HODGE MAX-CUT: REDUCE THE CLAY CORE TO PRIMITIVE ALGEBRAIC LIFT
--
-- The frozen Clay owner already asks for a literal rational algebraic cycle
-- representing every exact rational Hodge class.
--
-- This owner pays the standard Lefschetz assembly layer explicitly:
--
--   alpha = sum_r L^r alpha_r^prim
--
-- and proves that algebraic lifts of the primitive summands assemble to an
-- algebraic lift of alpha.
--
-- The novel theorem is therefore isolated as:
--
--   every exact rational primitive (q,q) class has a literal rational
--   algebraic cycle with the same rational singular cohomology class.
--
-- Hard Lefschetz / primitive decomposition itself and the fact that powers of
-- the hyperplane class act algebraically are ESTABLISHED-BACKGROUND inputs.
-- No primitive algebraic lift is manufactured here.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.HodgeRationalClassIntersectionExact as Exact
import DASHI.Mathematics.AlgebraicGeometry.HodgeAlgebraicCycleClayCoreExact as Clay

------------------------------------------------------------------------
-- Primitive exact rational Hodge classes.
------------------------------------------------------------------------

record PrimitiveRationalHodgeClassExact
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    (hodge : Hodge.HodgeDecomposition variety comparison)
    (codimension : Nat) : Set₁ where
  constructor primitive-rational-hodge-class-exact
  field
    exactClass :
      Exact.RationalHodgeClassExact hodge codimension

    -- Kernel-of-lowering / primitive condition.  Its established geometric
    -- realization is intentionally kept separate from the novel algebraicity
    -- theorem.
    primitiveWitness : Set

open PrimitiveRationalHodgeClassExact public

------------------------------------------------------------------------
-- One Lefschetz summand L^power alpha^prim of total codimension p.
------------------------------------------------------------------------

record PrimitiveLefschetzTerm
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    (hodge : Hodge.HodgeDecomposition variety comparison)
    (totalCodimension : Nat) : Set₁ where
  constructor primitive-lefschetz-term
  field
    primitiveCodimension : Nat
    power : Nat
    codimensionAccounting :
      primitiveCodimension + power ≡ totalCodimension
    primitiveClass :
      PrimitiveRationalHodgeClassExact
        hodge
        primitiveCodimension

open PrimitiveLefschetzTerm public

------------------------------------------------------------------------
-- Fold a list of already-Lefschetz-raised singular classes.
------------------------------------------------------------------------

foldSingular :
  ∀ {variety comparison}
    (degree : Nat) →
  List
    (Hodge.Carrier
      (Hodge.singularCohomology comparison degree)) →
  Hodge.Carrier
    (Hodge.singularCohomology comparison degree)
foldSingular {comparison = comparison} degree [] =
  Hodge.zero
    (Hodge.singularCohomology comparison degree)
foldSingular {comparison = comparison} degree (x ∷ xs) =
  Hodge.add
    (Hodge.singularCohomology comparison degree)
    x
    (foldSingular degree xs)

------------------------------------------------------------------------
-- Map a supplied Lefschetz action over the finite primitive decomposition.
------------------------------------------------------------------------

mapLefschetzClasses :
  ∀ {variety comparison hodge p} →
  (PrimitiveLefschetzTerm hodge p →
    Hodge.Carrier
      (Hodge.singularCohomology comparison (p + p))) →
  List (PrimitiveLefschetzTerm hodge p) →
  List
    (Hodge.Carrier
      (Hodge.singularCohomology comparison (p + p)))
mapLefschetzClasses action [] =
  []
mapLefschetzClasses action (term ∷ rest) =
  action term ∷ mapLefschetzClasses action rest

------------------------------------------------------------------------
-- Established Lefschetz / hyperplane background, on the SAME Clay carrier.
------------------------------------------------------------------------

record LefschetzAlgebraicAssemblyBackground
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge)
    (totalCodimension : Nat) : Setω where
  field
    -- Standard primitive decomposition data.
    decompose :
      Exact.RationalHodgeClassExact hodge totalCodimension →
      List (PrimitiveLefschetzTerm hodge totalCodimension)

    lefschetzSingularClass :
      PrimitiveLefschetzTerm hodge totalCodimension →
      Hodge.Carrier
        (Hodge.singularCohomology comparison
          (totalCodimension + totalCodimension))

    decompositionExact :
      (alpha :
        Exact.RationalHodgeClassExact hodge totalCodimension) →
      foldSingular
        (totalCodimension + totalCodimension)
        (mapLefschetzClasses
          lefschetzSingularClass
          (decompose alpha))
      ≡ Exact.singularClass alpha

    -- Algebraic action of the required hyperplane power.
    raiseCycle :
      (term : PrimitiveLefschetzTerm hodge totalCodimension) →
      Hodge.RationalAlgebraicCycle
        variety
        (primitiveCodimension term) →
      Hodge.RationalAlgebraicCycle
        variety
        totalCodimension

    raiseCycleClass :
      (term : PrimitiveLefschetzTerm hodge totalCodimension) →
      (cycle :
        Hodge.RationalAlgebraicCycle
          variety
          (primitiveCodimension term)) →
      Clay.singularCycleClass
          cycleBackground
          (primitiveCodimension term)
          cycle
      ≡
      Exact.singularClass
        (exactClass (primitiveClass term)) →
      Clay.singularCycleClass
          cycleBackground
          totalCodimension
          (raiseCycle term cycle)
      ≡
      lefschetzSingularClass term

    -- Rational cycle addition on the literal algebraic-cycle carrier.
    zeroCycle :
      Hodge.RationalAlgebraicCycle variety totalCodimension

    addCycle :
      Hodge.RationalAlgebraicCycle variety totalCodimension →
      Hodge.RationalAlgebraicCycle variety totalCodimension →
      Hodge.RationalAlgebraicCycle variety totalCodimension

    zeroCycleClass :
      Clay.singularCycleClass
          cycleBackground
          totalCodimension
          zeroCycle
      ≡
      Hodge.zero
        (Hodge.singularCohomology comparison
          (totalCodimension + totalCodimension))

    addCycleClass :
      (left right :
        Hodge.RationalAlgebraicCycle variety totalCodimension) →
      Clay.singularCycleClass
          cycleBackground
          totalCodimension
          (addCycle left right)
      ≡
      Hodge.add
        (Hodge.singularCohomology comparison
          (totalCodimension + totalCodimension))
        (Clay.singularCycleClass
          cycleBackground totalCodimension left)
        (Clay.singularCycleClass
          cycleBackground totalCodimension right)


open LefschetzAlgebraicAssemblyBackground public

------------------------------------------------------------------------
-- The ONLY novel producer exposed by this reduction.
------------------------------------------------------------------------

PrimitiveAlgebraicLift :
  ∀ {variety comparison hodge}
    (cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge) →
  Set₁
PrimitiveAlgebraicLift
    {variety = variety}
    {hodge = hodge}
    cycleBackground =
  (codimension : Nat) →
  (primitive :
    PrimitiveRationalHodgeClassExact hodge codimension) →
  Σ
    (Hodge.RationalAlgebraicCycle variety codimension)
    (λ cycle →
      Clay.singularCycleClass
          cycleBackground
          codimension
          cycle
      ≡
      Exact.singularClass
        (exactClass primitive))

------------------------------------------------------------------------
-- Assemble primitive lifts into one codimension-p cycle.
------------------------------------------------------------------------

assemblePrimitiveCycles :
  ∀ {variety comparison hodge}
    {cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge}
    {p : Nat} →
  (background :
    LefschetzAlgebraicAssemblyBackground
      cycleBackground p) →
  PrimitiveAlgebraicLift cycleBackground →
  List (PrimitiveLefschetzTerm hodge p) →
  Hodge.RationalAlgebraicCycle variety p
assemblePrimitiveCycles background lift [] =
  zeroCycle background
assemblePrimitiveCycles background lift (term ∷ rest) =
  addCycle background
    (raiseCycle background term
      (proj₁
        (lift
          (primitiveCodimension term)
          (primitiveClass term))))
    (assemblePrimitiveCycles background lift rest)

------------------------------------------------------------------------
-- The previous proof needs the head rewrite explicitly.
------------------------------------------------------------------------

assemblePrimitiveCyclesClassStep :
  ∀ {variety comparison hodge}
    {cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge}
    {p : Nat}
    (background :
      LefschetzAlgebraicAssemblyBackground
        cycleBackground p)
    (lift : PrimitiveAlgebraicLift cycleBackground)
    (term : PrimitiveLefschetzTerm hodge p)
    (rest : List (PrimitiveLefschetzTerm hodge p)) →
  Clay.singularCycleClass
      cycleBackground p
      (assemblePrimitiveCycles background lift (term ∷ rest))
  ≡
  Hodge.add
    (Hodge.singularCohomology comparison (p + p))
    (lefschetzSingularClass background term)
    (Clay.singularCycleClass
      cycleBackground p
      (assemblePrimitiveCycles background lift rest))
assemblePrimitiveCyclesClassStep background lift term rest =
  trans
    (addCycleClass background _ _)
    (cong
      (λ head →
        Hodge.add
          (Hodge.singularCohomology _ (_ + _))
          head
          (Clay.singularCycleClass
            _ _ (assemblePrimitiveCycles background lift rest)))
      (raiseCycleClass background
        term
        (proj₁
          (lift
            (primitiveCodimension term)
            (primitiveClass term)))
        (proj₂
          (lift
            (primitiveCodimension term)
            (primitiveClass term)))))

------------------------------------------------------------------------
-- Correct structural induction with the explicit head step.
------------------------------------------------------------------------

assemblePrimitiveCyclesClassExact :
  ∀ {variety comparison hodge}
    {cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge}
    {p : Nat}
    (background :
      LefschetzAlgebraicAssemblyBackground
        cycleBackground p)
    (lift : PrimitiveAlgebraicLift cycleBackground)
    (terms : List (PrimitiveLefschetzTerm hodge p)) →
  Clay.singularCycleClass
      cycleBackground p
      (assemblePrimitiveCycles background lift terms)
  ≡
  foldSingular
    (p + p)
    (mapLefschetzClasses
      (lefschetzSingularClass background)
      terms)
assemblePrimitiveCyclesClassExact background lift [] =
  zeroCycleClass background
assemblePrimitiveCyclesClassExact background lift (term ∷ rest) =
  trans
    (assemblePrimitiveCyclesClassStep
      background lift term rest)
    (cong
      (Hodge.add
        (Hodge.singularCohomology _ (_ + _))
        (lefschetzSingularClass background term))
      (assemblePrimitiveCyclesClassExact
        background lift rest))

------------------------------------------------------------------------
-- MAIN REDUCTION: primitive algebraicity -> frozen Clay core.
------------------------------------------------------------------------

primitiveLiftGivesHodgeClayCoreAt :
  ∀ {variety comparison hodge}
    {cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge}
    {p : Nat} →
  LefschetzAlgebraicAssemblyBackground
    cycleBackground p →
  PrimitiveAlgebraicLift cycleBackground →
  Clay.HodgeClayCoreAtCodimensionAlgebraicExact
    cycleBackground p
primitiveLiftGivesHodgeClayCoreAt background lift =
  record
    { Clay.algebraicRepresentative =
        λ alpha →
          assemblePrimitiveCycles
            background
            lift
            (decompose background alpha)
    ; Clay.algebraicRepresentativeHasExactRationalClass =
        λ alpha →
          trans
            (assemblePrimitiveCyclesClassExact
              background lift
              (decompose background alpha))
            (decompositionExact background alpha)
    }

------------------------------------------------------------------------
-- CLAY CUT
--
-- Once the classical Lefschetz decomposition and algebraic hyperplane action
-- are instantiated on the frozen same-object background, the entire Hodge Clay
-- core follows from ONE producer:
--
--   PrimitiveAlgebraicLift.
--
-- No projective-space special case or abstract cycle carrier is used.
------------------------------------------------------------------------
