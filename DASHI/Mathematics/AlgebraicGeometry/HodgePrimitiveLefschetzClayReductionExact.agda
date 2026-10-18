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
-- Hard Lefschetz / primitive decomposition itself and algebraicity of the
-- hyperplane action are established-background inputs.  No primitive
-- algebraic lift is manufactured here.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.HodgeRationalClassIntersectionExact as Exact
import DASHI.Mathematics.AlgebraicGeometry.HodgeAlgebraicCycleClayCoreExact as Clay

------------------------------------------------------------------------
-- A genuine primitive predicate on the exact same rational Hodge carrier.
------------------------------------------------------------------------

PrimitivePredicate :
  ∀ {variety comparison}
    (hodge : Hodge.HodgeDecomposition variety comparison) →
  Set₁
PrimitivePredicate hodge =
  (codimension : Nat) →
  Exact.RationalHodgeClassExact hodge codimension →
  Set

record PrimitiveRationalHodgeClassExact
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (isPrimitive : PrimitivePredicate hodge)
    (codimension : Nat) : Set₁ where
  constructor primitive-rational-hodge-class-exact
  field
    exactClass :
      Exact.RationalHodgeClassExact hodge codimension

    primitiveWitness :
      isPrimitive codimension exactClass

open PrimitiveRationalHodgeClassExact public

------------------------------------------------------------------------
-- One Lefschetz summand L^power alpha^prim of total codimension p.
------------------------------------------------------------------------

record PrimitiveLefschetzTerm
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (isPrimitive : PrimitivePredicate hodge)
    (totalCodimension : Nat) : Set₁ where
  constructor primitive-lefschetz-term
  field
    primitiveCodimension : Nat
    power : Nat
    codimensionAccounting :
      primitiveCodimension + power ≡ totalCodimension
    primitiveClass :
      PrimitiveRationalHodgeClassExact
        isPrimitive
        primitiveCodimension

open PrimitiveLefschetzTerm public

------------------------------------------------------------------------
-- Finite singular-class assembly.
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

mapLefschetzClasses :
  ∀ {variety comparison hodge p}
    {isPrimitive : PrimitivePredicate hodge} →
  (PrimitiveLefschetzTerm isPrimitive p →
    Hodge.Carrier
      (Hodge.singularCohomology comparison (p + p))) →
  List (PrimitiveLefschetzTerm isPrimitive p) →
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
    isPrimitive :
      PrimitivePredicate hodge

    -- Standard rational primitive decomposition.
    decompose :
      Exact.RationalHodgeClassExact hodge totalCodimension →
      List
        (PrimitiveLefschetzTerm
          isPrimitive
          totalCodimension)

    lefschetzSingularClass :
      PrimitiveLefschetzTerm
        isPrimitive
        totalCodimension →
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

    -- Algebraic action of the corresponding hyperplane power.
    raiseCycle :
      (term :
        PrimitiveLefschetzTerm
          isPrimitive
          totalCodimension) →
      Hodge.RationalAlgebraicCycle
        variety
        (primitiveCodimension term) →
      Hodge.RationalAlgebraicCycle
        variety
        totalCodimension

    raiseCycleClass :
      (term :
        PrimitiveLefschetzTerm
          isPrimitive
          totalCodimension) →
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
      Hodge.RationalAlgebraicCycle
        variety totalCodimension

    addCycle :
      Hodge.RationalAlgebraicCycle
        variety totalCodimension →
      Hodge.RationalAlgebraicCycle
        variety totalCodimension →
      Hodge.RationalAlgebraicCycle
        variety totalCodimension

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
        Hodge.RationalAlgebraicCycle
          variety totalCodimension) →
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
-- The ONLY conjectural producer exposed by this reduction.
------------------------------------------------------------------------

PrimitiveAlgebraicLift :
  ∀ {variety comparison hodge}
    (cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge)
    (isPrimitive : PrimitivePredicate hodge) →
  Set₁
PrimitiveAlgebraicLift
    {variety = variety}
    {hodge = hodge}
    cycleBackground
    isPrimitive =
  (codimension : Nat) →
  (primitive :
    PrimitiveRationalHodgeClassExact
      isPrimitive
      codimension) →
  Σ
    (Hodge.RationalAlgebraicCycle
      variety codimension)
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
    {p : Nat}
    (background :
      LefschetzAlgebraicAssemblyBackground
        cycleBackground p) →
  PrimitiveAlgebraicLift
    cycleBackground
    (isPrimitive background) →
  List
    (PrimitiveLefschetzTerm
      (isPrimitive background)
      p) →
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

assemblePrimitiveCyclesClassStep :
  ∀ {variety comparison hodge}
    {cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge}
    {p : Nat}
    (background :
      LefschetzAlgebraicAssemblyBackground
        cycleBackground p)
    (lift :
      PrimitiveAlgebraicLift
        cycleBackground
        (isPrimitive background))
    (term :
      PrimitiveLefschetzTerm
        (isPrimitive background)
        p)
    (rest :
      List
        (PrimitiveLefschetzTerm
          (isPrimitive background)
          p)) →
  Clay.singularCycleClass
      cycleBackground p
      (assemblePrimitiveCycles
        background lift (term ∷ rest))
  ≡
  Hodge.add
    (Hodge.singularCohomology comparison (p + p))
    (lefschetzSingularClass background term)
    (Clay.singularCycleClass
      cycleBackground p
      (assemblePrimitiveCycles background lift rest))
assemblePrimitiveCyclesClassStep
    {comparison = comparison}
    {cycleBackground = cycleBackground}
    {p = p}
    background lift term rest =
  trans
    (addCycleClass background
      (raiseCycle background term
        (proj₁
          (lift
            (primitiveCodimension term)
            (primitiveClass term))))
      (assemblePrimitiveCycles background lift rest))
    (cong
      (λ head →
        Hodge.add
          (Hodge.singularCohomology comparison (p + p))
          head
          (Clay.singularCycleClass
            cycleBackground p
            (assemblePrimitiveCycles background lift rest)))
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

assemblePrimitiveCyclesClassExact :
  ∀ {variety comparison hodge}
    {cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge}
    {p : Nat}
    (background :
      LefschetzAlgebraicAssemblyBackground
        cycleBackground p)
    (lift :
      PrimitiveAlgebraicLift
        cycleBackground
        (isPrimitive background))
    (terms :
      List
        (PrimitiveLefschetzTerm
          (isPrimitive background)
          p)) →
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
assemblePrimitiveCyclesClassExact
    {comparison = comparison}
    {p = p}
    background lift (term ∷ rest) =
  trans
    (assemblePrimitiveCyclesClassStep
      background lift term rest)
    (cong
      (Hodge.add
        (Hodge.singularCohomology comparison (p + p))
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
    {p : Nat}
    (background :
      LefschetzAlgebraicAssemblyBackground
        cycleBackground p) →
  PrimitiveAlgebraicLift
    cycleBackground
    (isPrimitive background) →
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
-- Once standard Hard Lefschetz/primitive decomposition and algebraic
-- hyperplane action are instantiated on the frozen same-object background,
-- the entire Hodge Clay core follows from ONE conjectural producer:
--
--   PrimitiveAlgebraicLift.
--
-- The primitive predicate itself is proof-relevant and shared by the
-- decomposition and lift theorem, so "primitive" is no longer a label-only
-- field.
------------------------------------------------------------------------
