module DASHI.Physics.Closure.Canonical.LocalProgramBundle where

-- Canonical local-program bundle. This freezes the current local theorem
-- ladder into one grouped surface so later widening can target broader-than-
-- local packages instead of adding more local rungs.

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalStageCStatus as CSS
open import DASHI.Physics.Closure.CanonicalStageCTheoremBundle as CSTB
open import DASHI.Physics.Closure.CanonicalStageCSummaryBundle as CSSB
open import DASHI.Physics.Closure.Algebra.WaveRegime as AWR
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
open import DASHI.Physics.Closure.Consumers.WaveRegime as CWR

record LocalProgramBundle : Setω where
  field
    closureStatus : CSS.ClosureSurfaceStatus
    theoremBundle : CSTB.CanonicalStageCTheoremBundle
    summaryBundle : CSSB.CanonicalStageCSummaryBundle

localProgramBundle : LocalProgramBundle
localProgramBundle =
  record
    { closureStatus = CSS.canonicalProved
    ; theoremBundle = CSTB.canonicalStageCTheoremBundle
    ; summaryBundle = CSSB.canonicalStageCSummaryBundle
    }
