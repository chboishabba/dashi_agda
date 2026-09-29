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
open import Data.Empty using (⊥)
open import Data.Rational.Base using (1ℚ)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge

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
------------------------------------------------------------------------
