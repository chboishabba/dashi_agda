module DASHI.Mathematics.Complexity.PNotEqualsNPLiteralSelfCodeGrowthNoGoExact where

------------------------------------------------------------------------
-- STRICT CODE GROWTH KILLS LITERAL DATA SELF-FIXED POINTS
--
-- A tempting notation in the resource-bounded diagonal programme is:
--
--   input = code(F input).
--
-- Classical recursion/fixed-point theorems do NOT generally promise literal
-- equality of source data with the code of the generated object.  They promise
-- an appropriate behavioural/semantic fixed point.
--
-- Now that Cook.BooleanFormula has an exact binary code, this owner records the
-- elementary but decisive size obstruction:
--
--   if |input| < |code(F input)|,
--   then input != code(F input).
--
-- This theorem is generic.  It does not claim every useful self-constructor is
-- strictly growing.  It prevents us from silently demanding an impossible raw
-- string fixed point once a concrete constructor's strict growth is proved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_<_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

------------------------------------------------------------------------
-- Ordinary list length.
------------------------------------------------------------------------

listLength :
  ∀ {A : Set} →
  List A →
  Nat
listLength [] =
  zero
listLength (_ ∷ rest) =
  suc (listLength rest)

------------------------------------------------------------------------
-- Literal raw-code fixed point.
------------------------------------------------------------------------

LiteralSelfCodeFixedPoint :
  (constructor : List Bool → Cook.BooleanFormula) →
  List Bool →
  Set
LiteralSelfCodeFixedPoint constructor input =
  input
  ≡
  Binary.encodeFormulaBits
    (constructor input)

literalSelfCodeFixedPointForcesEqualLength :
  (constructor : List Bool → Cook.BooleanFormula) →
  (input : List Bool) →
  LiteralSelfCodeFixedPoint constructor input →
  listLength input
  ≡
  Binary.formulaBitCodeLength
    (constructor input)
literalSelfCodeFixedPointForcesEqualLength
    constructor
    input
    fixed =
  cong listLength fixed

------------------------------------------------------------------------
-- Main strict-growth no-go.
------------------------------------------------------------------------

strictCodeGrowthKillsLiteralFixedPoint :
  (constructor : List Bool → Cook.BooleanFormula) →
  (input : List Bool) →
  listLength input
    <
  Binary.formulaBitCodeLength
    (constructor input) →
  LiteralSelfCodeFixedPoint constructor input →
  ⊥
strictCodeGrowthKillsLiteralFixedPoint
    constructor
    input
    grows
    fixed =
  NatP.<-irrefl
    (listLength input)
    (substRight
      (literalSelfCodeFixedPointForcesEqualLength
        constructor
        input
        fixed)
      grows)
  where
    substRight :
      ∀ {left right : Nat} →
      left ≡ right →
      left < right →
      left < left
    substRight equality proof
        rewrite equality =
      proof

------------------------------------------------------------------------
-- Equivalent convenient formulation.
------------------------------------------------------------------------

record StrictlyGrowingSelfFormulaConstructor : Set₁ where
  constructor strictly-growing-self-formula-constructor
  field
    build :
      List Bool →
      Cook.BooleanFormula

    codeStrictlyGrows :
      (input : List Bool) →
      listLength input
      <
      Binary.formulaBitCodeLength
        (build input)

open StrictlyGrowingSelfFormulaConstructor public

strictlyGrowingConstructorHasNoLiteralSelfCode :
  (constructor : StrictlyGrowingSelfFormulaConstructor) →
  (input : List Bool) →
  LiteralSelfCodeFixedPoint
    (build constructor)
    input →
  ⊥
strictlyGrowingConstructorHasNoLiteralSelfCode
    constructor
    input =
  strictCodeGrowthKillsLiteralFixedPoint
    (build constructor)
    input
    (codeStrictlyGrows constructor input)

------------------------------------------------------------------------
-- Research consequence.
--
-- The next self-reference theorem must distinguish:
--
--   RAW DATA FIXED POINT:
--     input == binary code of generated formula
--
-- from
--
--   BEHAVIOURAL / SEMANTIC FIXED POINT:
--     generated object has the required self-referential semantics.
--
-- If the concrete SAT self-constructor is proved strictly code-growing, only
-- the second route can survive.  This is exactly where Kleene/Godel ancestry
-- is relevant, but their unbounded fixed-point theorems still do not pay the
-- polynomial resource closure.
------------------------------------------------------------------------
