module DASHI.Reasoning.E8E6A2TernaryBranchingCandidateRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (_+_)

import DASHI.Reasoning.E8E6A2TernaryBranchingCandidateExact as B

fullBranchingPinned : B.fullCarrierCount ≡ 72 + 81 + 81 + 6 + 3
fullBranchingPinned = B.fullBranchingCount

relativeBranchingPinned : B.relativeCarrierCount ≡ 72 + 81 + 81 + 6
relativeBranchingPinned = B.relativeBranchingCount

planeCountPinned : B.selectedAffinePlaneCount ≡ 9
planeCountPinned = B.selectedAffinePlaneCountIs9

lineCountPinned : B.selectedAffineLineCount ≡ 3
lineCountPinned = B.selectedAffineLineCountIs3

recognitionBoundaryPinned :
  B.BranchingCandidateBoundary.branchingCountsCreateE8Recognition B.canonicalBranchingCandidateBoundary ≡ false
recognitionBoundaryPinned = B.reflNoE8Recognition

leanVerificationPinned :
  B.CrossLanguageBranchingReceipt.leanKernelVerified B.canonicalCrossLanguageBranchingReceipt ≡ false
leanVerificationPinned = B.reflLeanUnverified
