module DASHI.Cognition.Teleodynamics.ExceptionalE6Mod3FiniteGeometryRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.Teleodynamics.ExceptionalE6Mod3FiniteGeometryExact as E6

partition243Paid : E6.stateCount ≡ E6.zeroCount + E6.nullNonzeroCount + E6.class90Count + E6.class72Count
partition243Paid = E6.statePartition

projective121Paid : E6.projectiveTotal ≡ E6.nullLineCount + E6.rootLineCount + E6.otherLineCount
projective121Paid = E6.projectivePartition

pythonReceiptIsExternal :
  E6.FiniteQuadraticComputationReceipt.grade E6.canonicalFiniteQuadraticComputationReceipt
  ≡ E6.localFiniteComputation
pythonReceiptIsExternal = refl

e6RecognitionNotAutoPromoted :
  E6.ExceptionalE6Mod3FiniteGeometryBoundary.e6RootSameObjectRecognitionInhabitedHere
    E6.canonicalExceptionalE6Mod3FiniteGeometryBoundary
  ≡ false
e6RecognitionNotAutoPromoted = refl

e8DualIncidenceNotAutoPromoted :
  E6.ExceptionalE6Mod3FiniteGeometryBoundary.e6E8DualIncidenceRecognitionInhabitedHere
    E6.canonicalExceptionalE6Mod3FiniteGeometryBoundary
  ≡ false
e8DualIncidenceNotAutoPromoted = refl

t4LinearIdentificationNotClaimed :
  E6.ExceptionalE6Mod3FiniteGeometryBoundary.t4LinearIdentificationClaimed
    E6.canonicalExceptionalE6Mod3FiniteGeometryBoundary
  ≡ false
t4LinearIdentificationNotClaimed = refl
