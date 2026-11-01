module DASHI.Physics.Closure.Validation.Chi2BoundaryBoolInversionWitness where

open import Agda.Builtin.Equality using (_≡_)
open import UFTC_Lattice using (special; severity)

open import DASHI.Physics.Closure.Validation.Chi2BoundaryShiftLibrary as LIB
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TernaryRealInstance as TRI
open import DASHI.Physics.SeverityMapping as SM
open import DASHI.Physics.SeverityGuard.Core as SG
open import DASHI.Physics.SeverityGuard.Shift.Concrete as SGSC
open Chi2BoundaryCase

-- Bool-inversion-specific witness selection on the shared 4D closure carrier.
witnessState : RTC.Carrier TRI.n
witnessState = state LIB.caseB

witnessCode :
  SM.codeᵣ {TRI.m} {TRI.k} witnessState ≡ special 4
witnessCode = code-special4 LIB.caseB

witnessSeverity :
  severity (SG.SeverityPolicy.code (SGSC.policyᵣ {TRI.m} {TRI.k}) witnessState) ≡ 4
witnessSeverity = severity4 LIB.caseB

witnessSnap :
  SG.Snap (SGSC.policyᵣ {TRI.m} {TRI.k}) witnessState
witnessSnap = snapWitness LIB.caseB

witnessBroken :
  SG.Broken (SGSC.policyᵣ {TRI.m} {TRI.k}) witnessState
witnessBroken = brokenWitness LIB.caseB
