module DASHI.Mathematics.AlgebraicGeometry.HodgeLiteralCycleWitnessStrengthAuditExact where

------------------------------------------------------------------------
-- HODGE: GEOMETRIC-WITNESS STRENGTH AUDIT
--
-- The current RationalAlgebraicCycle carrier has:
--
--   finiteSupport : Set
--   algebraicSubvarietyWitness : CycleGenerator -> Set
--
-- These are TYPES of potential witnesses, not inhabitants. Therefore merely
-- returning RationalAlgebraicCycle does not establish finite support or even
-- the existence of any algebraic generator witness. The record admits a
-- syntactically nonempty cycle with all witness propositions uninhabited.
--
-- This owner gives that counterexample and makes the necessary extra
-- geometric evidence first-class. It does NOT change the frozen Clay core or
-- assert a universal Hodge cycle producer.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; trans)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 1ℚ)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Sum.Base using (inj₁; inj₂)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.HodgeLiteralCycleClassMapBridgeExact as Literal
import DASHI.Mathematics.AlgebraicGeometry.HodgeRationalClassIntersectionExact as Exact
import DASHI.Mathematics.AlgebraicGeometry.HodgeAlgebraicCycleClayCoreExact as Clay

------------------------------------------------------------------------
-- Real witness-carrying refinement of the existing literal cycle carrier.
------------------------------------------------------------------------

record WitnessedRationalAlgebraicCycle
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {codimension : Nat}
    (cycle : Hodge.RationalAlgebraicCycle variety codimension) : Set₁ where
  field
    finiteSupportCertificate :
      Hodge.finiteSupport cycle

    generatorAlgebraicCertificate :
      (generator : Hodge.CycleGenerator cycle) →
      Hodge.algebraicSubvarietyWitness cycle generator

open WitnessedRationalAlgebraicCycle public

------------------------------------------------------------------------
-- Actual cycle constructors preserve both witness obligations by computation.
------------------------------------------------------------------------

witnessedZeroCycle :
  ∀ {variety : Hodge.SmoothProjectiveComplexVariety}
    {codimension : Nat} →
  WitnessedRationalAlgebraicCycle
    (Literal.zeroRationalAlgebraicCycle
      {variety = variety} {codimension = codimension})
witnessedZeroCycle =
  record
    { finiteSupportCertificate = tt
    ; generatorAlgebraicCertificate = λ ()
    }

witnessedAddCycle :
  ∀ {variety : Hodge.SmoothProjectiveComplexVariety}
    {codimension : Nat}
    {left right : Hodge.RationalAlgebraicCycle variety codimension} →
  WitnessedRationalAlgebraicCycle left →
  WitnessedRationalAlgebraicCycle right →
  WitnessedRationalAlgebraicCycle
    (Literal.addRationalAlgebraicCycle left right)
witnessedAddCycle leftWitness rightWitness =
  record
    { finiteSupportCertificate =
        finiteSupportCertificate leftWitness ,
        finiteSupportCertificate rightWitness
    ; generatorAlgebraicCertificate = λ where
        (inj₁ generator) →
          generatorAlgebraicCertificate leftWitness generator
        (inj₂ generator) →
          generatorAlgebraicCertificate rightWitness generator
    }

witnessedScaleCycle :
  ∀ {variety : Hodge.SmoothProjectiveComplexVariety}
    {codimension : Nat}
    {cycle : Hodge.RationalAlgebraicCycle variety codimension} →
  (scalar : ℚ) →
  WitnessedRationalAlgebraicCycle cycle →
  WitnessedRationalAlgebraicCycle
    (Literal.scaleRationalAlgebraicCycle scalar cycle)
witnessedScaleCycle scalar witnessed =
  record
    { finiteSupportCertificate =
        finiteSupportCertificate witnessed
    ; generatorAlgebraicCertificate =
        generatorAlgebraicCertificate witnessed
    }

------------------------------------------------------------------------
-- Conversely, an INHABITED Set-valued witness does not establish geometric
-- meaning either: it can be selected as the one-element type by construction.
-- This audit prevents treating proof-relevant "witnessed" syntax as a Chow
-- variety or an actual algebraic subvariety without a geometry-backed map.
------------------------------------------------------------------------

syntacticallyWitnessedCycle :
  ∀ {variety : Hodge.SmoothProjectiveComplexVariety}
    {codimension : Nat} →
  Hodge.RationalAlgebraicCycle variety codimension
syntacticallyWitnessedCycle =
  record
    { Hodge.CycleGenerator = ⊤
    ; Hodge.coefficient = λ _ → 1ℚ
    ; Hodge.finiteSupport = ⊤
    ; Hodge.algebraicSubvarietyWitness = λ _ → ⊤
    }

syntacticallyWitnessedCycleHasCertificates :
  ∀ {variety : Hodge.SmoothProjectiveComplexVariety}
    {codimension : Nat} →
  WitnessedRationalAlgebraicCycle
    (syntacticallyWitnessedCycle
      {variety = variety}
      {codimension = codimension})
syntacticallyWitnessedCycleHasCertificates =
  record
    { finiteSupportCertificate = tt
    ; generatorAlgebraicCertificate = λ _ → tt
    }

------------------------------------------------------------------------
-- Universal SYNTAX production is trivial: ignore the rational Hodge class,
-- return the same one-generator cycle with unit-typed certificates.
-- It carries NO equality between its cycle class and the input alpha.
--
-- Thus a theorem of type
--   RationalHodgeClassExact -> Σ Cycle WitnessedCycle
-- is not a Hodge-algebraicity theorem without same-object singular-class
-- correctness and genuine geometry of the chosen generator.
------------------------------------------------------------------------

syntacticUniversalHodgeCycleProducer :
  ∀ {variety comparison hodge codimension} →
  (alpha :
    Exact.RationalHodgeClassExact
      hodge codimension) →
  Σ
    (Hodge.RationalAlgebraicCycle variety codimension)
    (λ cycle → WitnessedRationalAlgebraicCycle cycle)
syntacticUniversalHodgeCycleProducer alpha =
  syntacticallyWitnessedCycle ,
  syntacticallyWitnessedCycleHasCertificates

------------------------------------------------------------------------
-- Nontriviality check on the ACTUAL Clay singular-class target.
--
-- Because the universal syntactic producer ignores its alpha argument, a
-- FIXED cycle-class map assigns both outputs the same singular class.
-- Therefore it cannot represent two different rational Hodge classes.
--
-- This is an exact obstruction to promoting the synthetic total producer
-- into the universal Hodge theorem merely by inhabiting its support fields.
------------------------------------------------------------------------

syntacticProducerCannotRepresentDistinctSingularClasses :
  ∀ {variety comparison hodge codimension}
    (background : Clay.RationalAlgebraicCycleClassBackground hodge)
    (left right : Exact.RationalHodgeClassExact hodge codimension) →
  Exact.singularClass left ≢ Exact.singularClass right →
  Clay.singularCycleClass background codimension
    (Data.Product.proj₁
      (syntacticUniversalHodgeCycleProducer left))
    ≡ Exact.singularClass left →
  Clay.singularCycleClass background codimension
    (Data.Product.proj₁
      (syntacticUniversalHodgeCycleProducer right))
    ≡ Exact.singularClass right →
  ⊥
syntacticProducerCannotRepresentDistinctSingularClasses
    background left right distinct leftRep rightRep =
  distinct (trans (sym leftRep) rightRep)

------------------------------------------------------------------------
-- Counterexample: nonempty rational generator with no valid witnesses.
------------------------------------------------------------------------

phantomRationalCycle :
  ∀ {variety : Hodge.SmoothProjectiveComplexVariety}
    {codimension : Nat} →
  Hodge.RationalAlgebraicCycle variety codimension
phantomRationalCycle =
  record
    { Hodge.CycleGenerator = ⊤
    ; Hodge.coefficient = λ _ → 1ℚ
    ; Hodge.finiteSupport = ⊥
    ; Hodge.algebraicSubvarietyWitness = λ _ → ⊥
    }

phantomFiniteSupportImpossible :
  ∀ {variety : Hodge.SmoothProjectiveComplexVariety}
    {codimension : Nat} →
  Hodge.finiteSupport
    (phantomRationalCycle {variety = variety}
      {codimension = codimension})
  → ⊥
phantomFiniteSupportImpossible ()

phantomGeneratorAlgebraicityImpossible :
  ∀ {variety : Hodge.SmoothProjectiveComplexVariety}
    {codimension : Nat} →
  Hodge.algebraicSubvarietyWitness
    (phantomRationalCycle {variety = variety}
      {codimension = codimension})
    tt
  → ⊥
phantomGeneratorAlgebraicityImpossible ()

phantomCycleCannotBeWitnessed :
  ∀ {variety : Hodge.SmoothProjectiveComplexVariety}
    {codimension : Nat} →
  WitnessedRationalAlgebraicCycle
    (phantomRationalCycle {variety = variety}
      {codimension = codimension}) →
  ⊥
phantomCycleCannotBeWitnessed witnessed =
  phantomFiniteSupportImpossible
    (finiteSupportCertificate witnessed)

------------------------------------------------------------------------
-- So the actual geometric upgrade debt is not merely a projector:
--   1. generators must be mapped to genuine geometric subvarieties,
--   2. finite support must have an inhabitant,
--   3. cycle class must agree with the actual singular class,
--   4. ONLY THEN can an algebraic projector be called a Clay cycle producer.
--
-- A witnessed carrier here is still not sufficient by itself, because the
-- geometric interpretation of each Set-valued witness must also be anchored.
-- syntacticallyWitnessedCycleHasCertificates demonstrates that limitation
-- with a concrete inhabited but unconstrained witness presentation.
------------------------------------------------------------------------
