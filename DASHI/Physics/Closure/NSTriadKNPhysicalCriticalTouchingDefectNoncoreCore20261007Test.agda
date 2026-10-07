module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectNoncoreCore20261007Test where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectNoncoreCore20261007Exact as X

noncoreCoreBipartiteClosed :
  X.b4DefectNoncoreCoreBipartiteClosed ≡ true
noncoreCoreBipartiteClosed = X.b4DefectNoncoreCoreBipartiteClosedIsTrue

noncoreCoreFourAggregateClosed :
  X.b4DefectNoncoreCoreFourAggregateClosed ≡ true
noncoreCoreFourAggregateClosed = X.b4DefectNoncoreCoreFourAggregateClosedIsTrue

noncoreCoreVectorClosed :
  X.b4DefectNoncoreCoreVectorClosed ≡ true
noncoreCoreVectorClosed = X.b4DefectNoncoreCoreVectorClosedIsTrue

noncoreCoreSharpYoungClosed :
  X.b4DefectNoncoreCoreSharpYoungClosed ≡ true
noncoreCoreSharpYoungClosed = X.b4DefectNoncoreCoreSharpYoungClosedIsTrue

physicalBudgetStillOpen :
  X.b4DefectNoncoreCorePhysicalBudgetClosed ≡ false
physicalBudgetStillOpen = X.b4DefectNoncoreCorePhysicalBudgetClosedIsFalse
