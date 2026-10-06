module DASHI.Reasoning.T5QuadraticOrbitAuditRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Reasoning.T5QuadraticOrbitAuditExact as Q

qZeroCountPinned : Q.qZeroCount ≡ 81
qZeroCountPinned = Q.qZeroCountIs81

qOneCountPinned : Q.qOneCount ≡ 90
qOneCountPinned = Q.qOneCountIs90

qTwoCountPinned : Q.qTwoCount ≡ 72
qTwoCountPinned = Q.qTwoCountIs72

fullPartitionPinned : Q.fullT5Count ≡ 1 + 80 + 90 + 72
fullPartitionPinned = Q.fullPartitionOneEightyNinetySeventyTwo

relativePartitionPinned : Q.relativeCount ≡ 80 + 90 + 70
relativePartitionPinned = Q.relativePartitionEightyNinetySeventy

relativeNotQTwoPinned :
  Q.T5QuadraticOrbitBoundary.relative240IsQTwoShell Q.canonicalT5QuadraticOrbitBoundary ≡ false
relativeNotQTwoPinned = Q.reflRelativeNotQTwo

leanKernelStatusPinned :
  Q.CrossLanguageQuadraticReceipt.leanKernelVerified Q.canonicalCrossLanguageQuadraticReceipt ≡ false
leanKernelStatusPinned = Q.reflLeanKernelUnverified
