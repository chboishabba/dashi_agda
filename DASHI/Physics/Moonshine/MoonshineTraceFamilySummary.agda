module DASHI.Physics.Moonshine.MoonshineTraceFamilySummary where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.List.Base using (length)

open import DASHI.Physics.Moonshine.FiniteTwinedTraceDetailedReport as FTDR
open import DASHI.Physics.Moonshine.MoonshinePrototypeComparisonBundle as MPCB

record MoonshineTraceFamilySummary : Set where
  field
    bundle : MPCB.MoonshinePrototypeComparisonBundle
    explicitVerdictCount : Nat
    extraVerdictCount : Nat

canonicalMoonshineTraceFamilySummary : MoonshineTraceFamilySummary
canonicalMoonshineTraceFamilySummary =
  record
    { bundle = MPCB.canonicalMoonshinePrototypeComparisonBundle
    ; explicitVerdictCount =
        suc
          (suc
            (suc
              (length
                (FTDR.FiniteTwinedTraceDetailedReport.extraVerdicts
                  FTDR.finiteTwinedTraceDetailedReport))))
    ; extraVerdictCount =
        length
          (FTDR.FiniteTwinedTraceDetailedReport.extraVerdicts
            FTDR.finiteTwinedTraceDetailedReport)
    }
