module DASHI.Cognition.Teleodynamics.TeleodynamicGeometricCandidateRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.Teleodynamics.TeleodynamicGeometricCandidateBridgeExact as Bridge
import DASHI.Reasoning.GeometricReasoningCandidateSelectionExact as Reasoning

noPriorMapsToBaseline :
  Bridge.reasoningCandidate Bridge.noPriorArm ≡ Reasoning.unstructuredBaseline
noPriorMapsToBaseline = refl

e8MapsToLilaE8Candidate :
  Bridge.reasoningCandidate Bridge.e8RootArm ≡ Reasoning.lilaE8RootPrior
e8MapsToLilaE8Candidate = refl

f4RemainsGenericExceptionalCandidate :
  Bridge.reasoningCandidate Bridge.f4RootArm ≡ Reasoning.genericFiniteActionGeometry
f4RemainsGenericExceptionalCandidate = refl

bestFitDoesNotSelectMechanism :
  Bridge.bestCandidateCreatesMechanism Bridge.canonicalCandidateBridgeBoundary ≡ false
bestFitDoesNotSelectMechanism = refl

cosineOnlyIsInsufficient :
  Bridge.cosineSimilarityAloneClosesCandidateSelection Bridge.canonicalCandidateBridgeBoundary ≡ false
cosineOnlyIsInsufficient = refl
