module DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Claire Voisin,
-- "Hodge Theory and Complex Algebraic Geometry I".
-- DOI: 10.1017/CBO9780511615344.
-- Chapter 11, "Hodge Classes": DOI 10.1017/CBO9780511615344.012.
--
-- Pierre Deligne,
-- "The Hodge Conjecture", Clay Mathematics Institute problem description.
-- No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Add the missing native Hodge-theory carrier: smooth projective varieties,
-- singular/de Rham comparison, bidegree pieces, Hodge decomposition, rational
-- algebraic cycles and cycle-class maps.  The exact local theorem states that
-- the supplied cycle-class map lands in the (p,p) piece and preserves rational
-- linear combinations.
--
-- Existence of the analytic Hodge decomposition, de Rham comparison,
-- algebraicity of every rational Hodge class and all scheme/coherent-sheaf
-- foundations remain explicit fields.  No Hodge-conjecture solution is
-- manufactured from the type definitions.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Rational.Base using (ℚ)

record RationalVectorSpace : Set₁ where
  field
    Carrier : Set
    zero : Carrier
    add : Carrier → Carrier → Carrier
    scale : ℚ → Carrier → Carrier
    additiveAssociative : Set
    additiveCommutative : Set
    additiveIdentity : Set
    additiveInverse : Set
    scalarLaws : Set

open RationalVectorSpace public

record SmoothProjectiveComplexVariety : Set₁ where
  field
    Point : Set
    complexDimension : Nat
    smoothAtlas : Set
    complexStructure : Set
    projectiveEmbedding : Set
    compactKahlerStructure : Set
    algebraicStructureSheaf : Set
    noetherianStructure : Set

open SmoothProjectiveComplexVariety public

record SingularDeRhamComparison
    (variety : SmoothProjectiveComplexVariety) : Setω where
  field
    singularCohomology : Nat → RationalVectorSpace
    deRhamCohomology : Nat → RationalVectorSpace
    singularToDeRham : ∀ degree →
      Carrier (singularCohomology degree) →
      Carrier (deRhamCohomology degree)
    deRhamToSingular : ∀ degree →
      Carrier (deRhamCohomology degree) →
      Carrier (singularCohomology degree)
    comparisonLeftInverse : ∀ degree class →
      deRhamToSingular degree (singularToDeRham degree class) ≡ class
    comparisonRightInverse : ∀ degree formClass →
      singularToDeRham degree (deRhamToSingular degree formClass) ≡ formClass
    comparisonLinear : Set

open SingularDeRhamComparison public

record HodgeDecomposition
    (variety : SmoothProjectiveComplexVariety)
    (comparison : SingularDeRhamComparison variety) : Setω where
  field
    HodgePiece : Nat → Nat → RationalVectorSpace
    injectPiece : ∀ p q →
      Carrier (HodgePiece p q) →
      Carrier (deRhamCohomology comparison (p + q))
    decompose : ∀ degree →
      Carrier (deRhamCohomology comparison degree) → Set
    directSumDecomposition : Set
    complexConjugation : ∀ p q →
      Carrier (HodgePiece p q) → Carrier (HodgePiece q p)
    conjugationInvolutive : Set
    differentialTypeCompatibility : Set
    kahlerHarmonicRepresentative : Set

open HodgeDecomposition public

record RationalAlgebraicCycle
    (variety : SmoothProjectiveComplexVariety)
    (codimension : Nat) : Set₁ where
  field
    CycleGenerator : Set
    coefficient : CycleGenerator → ℚ
    finiteSupport : Set
    algebraicSubvarietyWitness : CycleGenerator → Set

record CycleClassMap
    (variety : SmoothProjectiveComplexVariety)
    (comparison : SingularDeRhamComparison variety)
    (hodge : HodgeDecomposition variety comparison) : Setω where
  field
    Cycle : Nat → Set
    zeroCycle : ∀ codimension → Cycle codimension
    addCycle : ∀ codimension →
      Cycle codimension → Cycle codimension → Cycle codimension
    scaleCycle : ∀ codimension →
      ℚ → Cycle codimension → Cycle codimension

    cycleClass : ∀ codimension →
      Cycle codimension →
      Carrier (HodgePiece hodge codimension codimension)

    cycleClassZero : ∀ codimension →
      cycleClass codimension (zeroCycle codimension)
      ≡ zero (HodgePiece hodge codimension codimension)
    cycleClassAdditive : ∀ codimension left right →
      cycleClass codimension (addCycle codimension left right)
      ≡ add (HodgePiece hodge codimension codimension)
          (cycleClass codimension left)
          (cycleClass codimension right)
    cycleClassHomogeneous : ∀ codimension scalar cycle →
      cycleClass codimension (scaleCycle codimension scalar cycle)
      ≡ scale (HodgePiece hodge codimension codimension)
          scalar (cycleClass codimension cycle)
    geometricCycleConstruction : ∀ codimension → Set

open CycleClassMap public

record RationalHodgeClass
    {variety : SmoothProjectiveComplexVariety}
    {comparison : SingularDeRhamComparison variety}
    (hodge : HodgeDecomposition variety comparison)
    (codimension : Nat) : Set where
  constructor rationalHodgeClass
  field
    hodgeClassValue : Carrier (HodgePiece hodge codimension codimension)

open RationalHodgeClass public

cycleClassProducesRationalHodgeClass :
  ∀ {variety comparison hodge}
    (cycleMap : CycleClassMap variety comparison hodge)
    codimension cycle →
  RationalHodgeClass hodge codimension
cycleClassProducesRationalHodgeClass cycleMap codimension cycle =
  rationalHodgeClass (cycleClass cycleMap codimension cycle)

cycleClassOfSumIsHodgeSum :
  ∀ {variety comparison hodge}
    (cycleMap : CycleClassMap variety comparison hodge)
    codimension left right →
  hodgeClassValue
    (cycleClassProducesRationalHodgeClass cycleMap codimension
      (addCycle cycleMap codimension left right))
  ≡ add (HodgePiece hodge codimension codimension)
      (hodgeClassValue
        (cycleClassProducesRationalHodgeClass cycleMap codimension left))
      (hodgeClassValue
        (cycleClassProducesRationalHodgeClass cycleMap codimension right))
cycleClassOfSumIsHodgeSum cycleMap codimension left right =
  cycleClassAdditive cycleMap codimension left right

cycleClassOfScalarMultipleIsHodgeScalarMultiple :
  ∀ {variety comparison hodge}
    (cycleMap : CycleClassMap variety comparison hodge)
    codimension scalar cycle →
  hodgeClassValue
    (cycleClassProducesRationalHodgeClass cycleMap codimension
      (scaleCycle cycleMap codimension scalar cycle))
  ≡ scale (HodgePiece hodge codimension codimension) scalar
      (hodgeClassValue
        (cycleClassProducesRationalHodgeClass cycleMap codimension cycle))
cycleClassOfScalarMultipleIsHodgeScalarMultiple
    cycleMap codimension scalar cycle =
  cycleClassHomogeneous cycleMap codimension scalar cycle

record HodgeConjectureAtCodimension
    {variety : SmoothProjectiveComplexVariety}
    {comparison : SingularDeRhamComparison variety}
    {hodge : HodgeDecomposition variety comparison}
    (cycleMap : CycleClassMap variety comparison hodge)
    (codimension : Nat) : Set₁ where
  field
    everyRationalHodgeClassHasCycle :
      RationalHodgeClass hodge codimension →
      Cycle cycleMap codimension
    cycleRepresentsClass : ∀ hodgeClass →
      cycleClass cycleMap codimension
        (everyRationalHodgeClassHasCycle hodgeClass)
      ≡ hodgeClassValue hodgeClass

open HodgeConjectureAtCodimension public

hodgeConjectureGivesCycleRepresentative :
  ∀ {variety : SmoothProjectiveComplexVariety}
    {comparison : SingularDeRhamComparison variety}
    {hodge : HodgeDecomposition variety comparison}
    {cycleMap : CycleClassMap variety comparison hodge}
    {codimension : Nat} →
  (conjecture : HodgeConjectureAtCodimension
    {variety = variety}
    {comparison = comparison}
    {hodge = hodge}
    cycleMap codimension) →
  (hodgeClass : RationalHodgeClass hodge codimension) →
  cycleClass cycleMap codimension
    (everyRationalHodgeClassHasCycle conjecture hodgeClass)
  ≡ hodgeClassValue hodgeClass
hodgeConjectureGivesCycleRepresentative conjecture hodgeClass =
  cycleRepresentsClass conjecture hodgeClass
