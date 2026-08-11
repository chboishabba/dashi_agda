module DASHI.Computation.JacquardOperationalSemanticsExact where

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)

------------------------------------------------------------------------
-- Jacquard control is formalized as an executable semantics:
--
--   finite pattern program
--     -> lift-mask schedule
--     -> crossing rows
--     -> per-warp crossing word.
--
-- The compilation theorem proves that direct program execution and execution
-- of the compiled lift schedule agree exactly.
------------------------------------------------------------------------

data Crossing : Set where
  warpOver : Crossing
  weftOver : Crossing

crossingOf : Bool → Crossing
crossingOf true = warpOver
crossingOf false = weftOver

LiftMask : Nat → Set
LiftMask n = Fin n → Bool

data JacquardInstruction (n : Nat) : Set where
  liftMask : LiftMask n → JacquardInstruction n

JacquardProgram : Nat → Set
JacquardProgram n = List (JacquardInstruction n)

LiftSchedule : Nat → Set
LiftSchedule n = List (LiftMask n)

CrossingRow : Nat → Set
CrossingRow n = Fin n → Crossing

WovenRows : Nat → Set
WovenRows n = List (CrossingRow n)

compile :
  {n : Nat} →
  JacquardProgram n →
  LiftSchedule n
compile [] = []
compile (liftMask mask ∷ program) = mask ∷ compile program

weaveRow :
  {n : Nat} →
  LiftMask n →
  CrossingRow n
weaveRow mask warp = crossingOf (mask warp)

executeSchedule :
  {n : Nat} →
  LiftSchedule n →
  WovenRows n
executeSchedule [] = []
executeSchedule (mask ∷ schedule) =
  weaveRow mask ∷ executeSchedule schedule

executeProgram :
  {n : Nat} →
  JacquardProgram n →
  WovenRows n
executeProgram [] = []
executeProgram (liftMask mask ∷ program) =
  weaveRow mask ∷ executeProgram program

compilePreservesExecution :
  {n : Nat} →
  (program : JacquardProgram n) →
  executeSchedule (compile program) ≡ executeProgram program
compilePreservesExecution [] = refl
compilePreservesExecution (liftMask mask ∷ program) =
  cong (λ rows → weaveRow mask ∷ rows)
    (compilePreservesExecution program)

crossingWordAt :
  {n : Nat} →
  Fin n →
  WovenRows n →
  List Crossing
crossingWordAt warp [] = []
crossingWordAt warp (row ∷ rows) =
  row warp ∷ crossingWordAt warp rows

compiledCrossingWordAgrees :
  {n : Nat} →
  (warp : Fin n) →
  (program : JacquardProgram n) →
  crossingWordAt warp (executeSchedule (compile program))
  ≡ crossingWordAt warp (executeProgram program)
compiledCrossingWordAgrees warp program =
  cong (crossingWordAt warp) (compilePreservesExecution program)

ObservationallyEquivalent :
  {n : Nat} →
  JacquardProgram n →
  JacquardProgram n →
  Set
ObservationallyEquivalent first second =
  executeProgram first ≡ executeProgram second

observationalReflexive :
  {n : Nat} →
  (program : JacquardProgram n) →
  ObservationallyEquivalent program program
observationalReflexive program = refl

observationalSymmetric :
  {n : Nat} →
  {first second : JacquardProgram n} →
  ObservationallyEquivalent first second →
  ObservationallyEquivalent second first
observationalSymmetric = sym

observationalTransitive :
  {n : Nat} →
  {first second third : JacquardProgram n} →
  ObservationallyEquivalent first second →
  ObservationallyEquivalent second third →
  ObservationallyEquivalent first third
observationalTransitive = trans

------------------------------------------------------------------------
-- Distinct source programs may still compile to the same observations only
-- when their executed crossing rows are propositionally equal.  The quotient
-- is semantic rather than textual.
------------------------------------------------------------------------

record JacquardSemantics (n : Nat) : Set₁ where
  constructor jacquardSemantics
  field
    Program : Set
    Schedule : Set
    FabricObservation : Set
    compileProgram : Program → Schedule
    executeCompiled : Schedule → FabricObservation
    executeDirect : Program → FabricObservation
    compilerCorrect :
      (program : Program) →
      executeCompiled (compileProgram program) ≡ executeDirect program

open JacquardSemantics public

canonicalJacquardSemantics :
  (n : Nat) → JacquardSemantics n
canonicalJacquardSemantics n =
  jacquardSemantics
    (JacquardProgram n)
    (LiftSchedule n)
    (WovenRows n)
    compile
    executeSchedule
    executeProgram
    compilePreservesExecution
