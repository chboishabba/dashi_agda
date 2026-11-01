module DASHI.Physics.Closure.Deg23Candidate14302Receipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.Deg23FromFullTraceFormulaReceipt as Trace

deg23CandidateStatement : String
deg23CandidateStatement =
  "The diagnostic denominator 1-alpha1/2-alpha1^2/4 gives a 14.301-class effective degree near the 14.302 target, but it is not derived."

record Deg23Candidate14302Receipt : Setω where
  field
    traceReceipt :
      Trace.Deg23FromFullTraceFormulaReceipt

    traceRouteStillOpen :
      Trace.deg23ResidualExplained traceReceipt ≡ false

    baseDegreeMilliUnits :
      Nat

    baseDegreeMilliUnitsIsFourteen :
      baseDegreeMilliUnits ≡ 14000

    oneLoopDegreeMilliUnits :
      Nat

    oneLoopDegreeMilliUnitsIsFourteenPointTwoNineThree :
      oneLoopDegreeMilliUnits ≡ 14293

    twoLoopCandidateDegreeMilliUnits :
      Nat

    twoLoopCandidateDegreeMilliUnitsIsFourteenPointThreeZeroOne :
      twoLoopCandidateDegreeMilliUnits ≡ 14301

    targetDegreeMilliUnits :
      Nat

    targetDegreeMilliUnitsIsFourteenPointThreeZeroTwo :
      targetDegreeMilliUnits ≡ 14302

    twoLoopCandidateErrorPPM :
      Nat

    twoLoopCandidateErrorPPMIsAboutSeventy :
      twoLoopCandidateErrorPPM ≡ 70

    deg23FormulaDerived :
      Bool

    deg23FormulaDerivedIsFalse :
      deg23FormulaDerived ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ deg23CandidateStatement

open Deg23Candidate14302Receipt public

canonicalDeg23Candidate14302Receipt :
  Deg23Candidate14302Receipt
canonicalDeg23Candidate14302Receipt =
  record
    { traceReceipt =
        Trace.canonicalDeg23FromFullTraceFormulaReceipt
    ; traceRouteStillOpen =
        refl
    ; baseDegreeMilliUnits =
        14000
    ; baseDegreeMilliUnitsIsFourteen =
        refl
    ; oneLoopDegreeMilliUnits =
        14293
    ; oneLoopDegreeMilliUnitsIsFourteenPointTwoNineThree =
        refl
    ; twoLoopCandidateDegreeMilliUnits =
        14301
    ; twoLoopCandidateDegreeMilliUnitsIsFourteenPointThreeZeroOne =
        refl
    ; targetDegreeMilliUnits =
        14302
    ; targetDegreeMilliUnitsIsFourteenPointThreeZeroTwo =
        refl
    ; twoLoopCandidateErrorPPM =
        70
    ; twoLoopCandidateErrorPPMIsAboutSeventy =
        refl
    ; deg23FormulaDerived =
        false
    ; deg23FormulaDerivedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; statement =
        deg23CandidateStatement
    ; statementIsCanonical =
        refl
    }
