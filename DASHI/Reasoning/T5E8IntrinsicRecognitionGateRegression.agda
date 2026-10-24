module DASHI.Reasoning.T5E8IntrinsicRecognitionGateRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Reasoning.T5E8IntrinsicRecognitionGateExact as G

preexistencePinned :
  G.IntrinsicRecognitionBoundary.targetGeometryMustPreexistRecognition G.canonicalIntrinsicRecognitionBoundary ≡ true
preexistencePinned = G.reflTargetPreexists

transportBoundaryPinned :
  G.IntrinsicRecognitionBoundary.transportedGeometryCountsAsIndependentEvidence G.canonicalIntrinsicRecognitionBoundary ≡ false
transportBoundaryPinned = G.reflTransportNotEvidence

naiveCandidatePinned :
  G.IntrinsicRecognitionBoundary.naiveOrthogonalityCandidateRejectedByLeanSource G.canonicalIntrinsicRecognitionBoundary ≡ true
naiveCandidatePinned = G.reflNaiveRejected

leanKernelPinned :
  G.IntrinsicRecognitionBoundary.leanKernelVerified G.canonicalIntrinsicRecognitionBoundary ≡ false
leanKernelPinned = G.reflLeanKernelUnverified
