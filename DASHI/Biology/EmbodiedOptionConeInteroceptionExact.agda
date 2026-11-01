module DASHI.Biology.EmbodiedOptionConeInteroceptionExact where

open import DASHI.Core.Prelude

import DASHI.Governance.OptionConeCoercionExact as Cone

------------------------------------------------------------------------
-- EMBODIED OPTION-CONE / INTEROCEPTION FEEDBACK
--
-- Exact finite bridge:
--   reachable-option geometry
--   -> appraisal/body regime
--   -> interoceptive afference
--   -> prior-indexed felt state
--   -> next accessible-option geometry.
--
-- This is a structural countermodel/calibration surface.  It does not claim
-- that a real person's option appraisal deterministically sets cortisol,
-- norepinephrine, emotion, diagnosis, or behaviour.
------------------------------------------------------------------------

data Activation : Set where low medium high : Activation

record BodyState : Set where
  constructor bodyState
  field
    norepinephrine : Activation
    cortisol : Activation
    sympathetic : Activation
    parasympathetic : Activation

open BodyState public

regulatedBody : BodyState
regulatedBody = bodyState medium medium low high

mobilisedBody : BodyState
mobilisedBody = bodyState high medium high low

prolongedLoadBody : BodyState
prolongedLoadBody = bodyState high high high low

sameCortisolDifferentBody :
  cortisol regulatedBody ≡ cortisol mobilisedBody
sameCortisolDifferentBody = refl

cortisolDoesNotDetermineBodyState : regulatedBody ≡ mobilisedBody → ⊥
cortisolDoesNotDetermineBodyState ()

------------------------------------------------------------------------
-- 1. Objective/reachable option cone.
------------------------------------------------------------------------

data Situation : Set where broadCone contractedCone reopenedCone : Situation

data Option : Set where flexiblePlanning seekSupport defensiveWithdrawal : Option

data Available : Situation → Option → Set where
  broadPlan : Available broadCone flexiblePlanning
  broadSupport : Available broadCone seekSupport
  broadWithdraw : Available broadCone defensiveWithdrawal
  contractedWithdraw : Available contractedCone defensiveWithdrawal
  reopenedPlan : Available reopenedCone flexiblePlanning
  reopenedSupport : Available reopenedCone seekSupport
  reopenedWithdraw : Available reopenedCone defensiveWithdrawal

reachability : Cone.SafeReachabilitySystem Situation Option
reachability = Cone.safeReachabilitySystem Available

contractedIncludedInBroad :
  (option : Option) →
  Available contractedCone option →
  Available broadCone option
contractedIncludedInBroad defensiveWithdrawal contractedWithdraw = broadWithdraw

canonicalOptionConeContraction :
  Cone.StrictSafeReachabilityContraction reachability broadCone contractedCone
canonicalOptionConeContraction =
  Cone.strictSafeReachabilityContraction
    contractedIncludedInBroad
    flexiblePlanning
    broadPlan
    (λ ())

reopenedRestoresLostPlan : Available reopenedCone flexiblePlanning
reopenedRestoresLostPlan = reopenedPlan

------------------------------------------------------------------------
-- 2. Appraisal -> multidimensional body state.
------------------------------------------------------------------------

data Appraisal : Set where manageableAppraisal constrainedThreatAppraisal : Appraisal

appraise : Situation → Appraisal
appraise broadCone = manageableAppraisal
appraise contractedCone = constrainedThreatAppraisal
appraise reopenedCone = manageableAppraisal

bodyResponse : Appraisal → BodyState
bodyResponse manageableAppraisal = regulatedBody
bodyResponse constrainedThreatAppraisal = mobilisedBody

contractedConeRecruitsDifferentBodyRegime :
  bodyResponse (appraise contractedCone) ≡ bodyResponse (appraise broadCone) → ⊥
contractedConeRecruitsDifferentBodyRegime ()

------------------------------------------------------------------------
-- 3. Body -> interoceptive afference -> prior-indexed felt state.
--
-- `afference` is intentionally a toy projection of the multidimensional body
-- state through the sympathetic coordinate.  It is not claimed to be a full
-- anatomical interoceptive encoder.
------------------------------------------------------------------------

data InteroceptiveAfference : Set where quietAfference arousalAfference : InteroceptiveAfference

sympatheticAfference : Activation → InteroceptiveAfference
sympatheticAfference low = quietAfference
sympatheticAfference medium = arousalAfference
sympatheticAfference high = arousalAfference

afference : BodyState → InteroceptiveAfference
afference body = sympatheticAfference (sympathetic body)

data InteroceptivePrior : Set where safetyPrior threatPrior : InteroceptivePrior

data FeltState : Set where settledFeeling activatedFeeling alarmedFeeling : FeltState

inferFeltState : InteroceptivePrior → InteroceptiveAfference → FeltState
inferFeltState safetyPrior quietAfference = settledFeeling
inferFeltState threatPrior quietAfference = activatedFeeling
inferFeltState safetyPrior arousalAfference = activatedFeeling
inferFeltState threatPrior arousalAfference = alarmedFeeling

sameAfferenceDifferentPriorCanChangeFeeling :
  inferFeltState safetyPrior arousalAfference
  ≡ inferFeltState threatPrior arousalAfference → ⊥
sameAfferenceDifferentPriorCanChangeFeeling ()

feltStateIsNotRawBodyReadout :
  inferFeltState safetyPrior (afference mobilisedBody)
  ≡ inferFeltState threatPrior (afference mobilisedBody) → ⊥
feltStateIsNotRawBodyReadout ()

------------------------------------------------------------------------
-- 4. Felt/body state feeds the next accessible cone.
------------------------------------------------------------------------

nextAccessibleSituation : FeltState → Situation
nextAccessibleSituation settledFeeling = broadCone
nextAccessibleSituation activatedFeeling = reopenedCone
nextAccessibleSituation alarmedFeeling = contractedCone

closedLoop : InteroceptivePrior → Situation → Situation
closedLoop prior situation =
  nextAccessibleSituation
    (inferFeltState prior (afference (bodyResponse (appraise situation))))

threatPriorContractedConeIsSelfMaintainingWitness :
  closedLoop threatPrior contractedCone ≡ contractedCone
threatPriorContractedConeIsSelfMaintainingWitness = refl

safetyPriorContractedConeCanReopenWitness :
  closedLoop safetyPrior contractedCone ≡ reopenedCone
safetyPriorContractedConeCanReopenWitness = refl

record EmbodiedOptionConeBoundary : Set where
  constructor embodiedOptionConeBoundary
  field
    cortisolAloneDeterminesBodyState : Bool
    bodilyAfferenceAloneDeterminesFeltState : Bool
    contractedConeAlwaysMeansPathology : Bool
    threatPriorAlwaysClinicallyTraumatic : Bool
    bodyStateCanParticipateInNextAccessGeometry : Bool

canonicalEmbodiedOptionConeBoundary : EmbodiedOptionConeBoundary
canonicalEmbodiedOptionConeBoundary =
  embodiedOptionConeBoundary false false false false true
