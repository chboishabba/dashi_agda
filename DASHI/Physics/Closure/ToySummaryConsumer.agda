module DASHI.Physics.Closure.ToySummaryConsumer where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.Canonical.LocalProgramBundle as LPB
open import DASHI.Physics.Toy.UnifiedToySummaryBundle as UTSB

record ToySummaryConsumer : Setω where
  field
    localProgram : LPB.LocalProgramBundle
    toySummary   : UTSB.UnifiedToySummaryBundle

toySummaryConsumer : ToySummaryConsumer
toySummaryConsumer =
  record
    { localProgram = LPB.localProgramBundle
    ; toySummary = UTSB.unifiedToySummaryBundle
    }

record ToyIterateConsumer (n : Nat) : Setω where
  field
    localProgram : LPB.LocalProgramBundle
    toyIterates  : UTSB.UnifiedToyIterateBundle n

toyIterateConsumer : (n : Nat) → ToyIterateConsumer n
toyIterateConsumer n =
  record
    { localProgram = LPB.localProgramBundle
    ; toyIterates = UTSB.unifiedToyIterateBundle n
    }
