module DASHI.Physics.Moonshine.FiniteTwinedTraceComparison where

open import Data.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.Moonshine.FiniteTwinedShellTrace as FTST

natEq : Nat → Nat → Bool
natEq zero zero = true
natEq zero (suc _) = false
natEq (suc _) zero = false
natEq (suc m) (suc n) = natEq m n

and : Bool → Bool → Bool
and true true = true
and _ _ = false

record FiniteTwinedTraceComparison : Set where
  field
    orientationMatches : Bool
    grade1Matches : Bool
    grade2Matches : Bool

compareTwinedTrace :
  FTST.FiniteTwinedShellTrace →
  FTST.FiniteTwinedShellTrace →
  FiniteTwinedTraceComparison
compareTwinedTrace left right =
  record
    { orientationMatches =
        natEq
          (FTST.FiniteTwinedShellTrace.orientationCoeff left)
          (FTST.FiniteTwinedShellTrace.orientationCoeff right)
    ; grade1Matches =
        natEq
          (FTST.FiniteTwinedShellTrace.grade1FixedCount left)
          (FTST.FiniteTwinedShellTrace.grade1FixedCount right)
    ; grade2Matches =
        natEq
          (FTST.FiniteTwinedShellTrace.grade2FixedCount left)
          (FTST.FiniteTwinedShellTrace.grade2FixedCount right)
    }

data FiniteTwinedTraceVerdict : Set where
  exactTwinedMatch : FiniteTwinedTraceVerdict
  gradedTwinedMatch : FiniteTwinedTraceVerdict
  twinedMismatch : FiniteTwinedTraceVerdict

classifyTwined :
  FiniteTwinedTraceComparison →
  FiniteTwinedTraceVerdict
classifyTwined cmp with and
  (FiniteTwinedTraceComparison.grade1Matches cmp)
  (FiniteTwinedTraceComparison.grade2Matches cmp)
... | false = twinedMismatch
... | true with FiniteTwinedTraceComparison.orientationMatches cmp
... | true = exactTwinedMatch
... | false = gradedTwinedMatch
