module DASHI.Physics.Moonshine.MoonshineOrbitTraceSummary where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Moonshine.MoonshineTraceFamilySummary as MTFS
open import DASHI.Physics.Moonshine.MoonshinePrototypeComparisonBundle as MPCB

record MoonshineOrbitTraceSummary : Set where
  field
    traceFamily : MTFS.MoonshineTraceFamilySummary
    prototypeBundle : MPCB.MoonshinePrototypeComparisonBundle
    orbitTraceCount : Nat

canonicalMoonshineOrbitTraceSummary : MoonshineOrbitTraceSummary
canonicalMoonshineOrbitTraceSummary =
  record
    { traceFamily = MTFS.canonicalMoonshineTraceFamilySummary
    ; prototypeBundle = MPCB.canonicalMoonshinePrototypeComparisonBundle
    ; orbitTraceCount =
        MTFS.MoonshineTraceFamilySummary.explicitVerdictCount
          MTFS.canonicalMoonshineTraceFamilySummary
    }
