module DASHI.Physics.Closure.Validation.Chi2BoundaryShiftTheorem where

open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.Validation.Chi2BoundaryShiftLibrary as LIB

record Chi2BoundaryShiftTheorem : Set where
  field
    caseCount : Nat
    primary : LIB.Chi2BoundaryCase
    secondary : LIB.Chi2BoundaryCase
    tertiary : LIB.Chi2BoundaryCase

canonicalChi2BoundaryShiftTheorem : Chi2BoundaryShiftTheorem
canonicalChi2BoundaryShiftTheorem =
  record
    { caseCount = LIB.caseCount
    ; primary = LIB.caseA
    ; secondary = LIB.caseB
    ; tertiary = LIB.caseC
    }
