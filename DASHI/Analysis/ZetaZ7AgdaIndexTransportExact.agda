module DASHI.Analysis.ZetaZ7AgdaIndexTransportExact where

------------------------------------------------------------------------
-- EXACT Z7 INDEX TRANSPORT INTO THE EXISTING DASHI Fin 15 ODD WINDOW.
--
-- External source: Shawn Krisman, telaviv/zeta-irrationality,
-- ZetaIrr.Z7.oneOfZeta7To21 (Zudilin/Ball-Rivoal lineage).
-- This file does NOT import its Lean proof into Agda.
--
-- DASHI: every 7,9,...,21 source index maps to its exact original
-- oddArgument (5+2*k). Witnesses transport ONLY when an actual
-- ValueContext carries the two value equalities.
--
-- No claim of an individually selected irrational zeta value,
-- native Agda analytic-substrate closure or RH.
-- Source-written, pinned Agda kernel check pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)
open import Data.Fin using (Fin; zero; suc)

import DASHI.Analysis.ZetaOddValueWitnessTransportExact as Odd

data Z7Index : Set where
  at7 at9 at11 at13 at15 at17 at19 at21 : Z7Index

intoFifteen : Z7Index → Fin 15
intoFifteen at7 = suc zero
intoFifteen at9 = suc suc zero
intoFifteen at11 = suc suc suc zero
intoFifteen at13 = suc suc suc suc zero
intoFifteen at15 = suc suc suc suc suc zero
intoFifteen at17 = suc suc suc suc suc suc zero
intoFifteen at19 = suc suc suc suc suc suc suc zero
intoFifteen at21 = suc suc suc suc suc suc suc suc zero

------------------------------------------------------------------------
-- Literal index equalities, checked by Agda's Nat normalizer.
------------------------------------------------------------------------

z7Argument7 : Odd.oddArgument (intoFifteen at7) ≡ 7
z7Argument7 = refl

z7Argument9 : Odd.oddArgument (intoFifteen at9) ≡ 9
z7Argument9 = refl

z7Argument11 : Odd.oddArgument (intoFifteen at11) ≡ 11
z7Argument11 = refl

z7Argument13 : Odd.oddArgument (intoFifteen at13) ≡ 13
z7Argument13 = refl

z7Argument15 : Odd.oddArgument (intoFifteen at15) ≡ 15
z7Argument15 = refl

z7Argument17 : Odd.oddArgument (intoFifteen at17) ≡ 17
z7Argument17 = refl

z7Argument19 : Odd.oddArgument (intoFifteen at19) ≡ 19
z7Argument19 = refl

z7Argument21 : Odd.oddArgument (intoFifteen at21) ≡ 21
z7Argument21 = refl

------------------------------------------------------------------------
-- The external mathematical witness is an INPUT, not a manufactured
-- inhabitant of this type.
------------------------------------------------------------------------

Z7IrrationalWitness : (context : Odd.ValueContext) → Set
Z7IrrationalWitness context =
  Σ Z7Index (λ i →
    Odd.IrrationalAt context
      (Odd.leanValue context) (intoFifteen i))

z7WitnessIntoFifteen :
  (context : Odd.ValueContext) →
  Z7IrrationalWitness context →
  Odd.OddIrrationalWitness context (Odd.leanValue context)
z7WitnessIntoFifteen context (i , irrational) =
  intoFifteen i , irrational

z7WitnessIntoDashi :
  (context : Odd.ValueContext) →
  Z7IrrationalWitness context →
  Odd.OddIrrationalWitness context (Odd.dashiValue context)
z7WitnessIntoDashi context witness =
  Odd.leanToDashiIrrationalWitnessDirect context
    (z7WitnessIntoFifteen context witness)

z7WitnessIndexPreserved :
  (context : Odd.ValueContext) →
  (witness : Z7IrrationalWitness context) →
  fst (z7WitnessIntoDashi context witness) ≡
  intoFifteen (fst witness)
z7WitnessIndexPreserved context (i , irrational) = refl
