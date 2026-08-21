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

-- Same cortisol coordinate does not determine the complete body regime.
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
------------------------------------------------------------------------

data InteroceptiveAfference : Set where quietAfference arousalAfference : InteroceptiveAfference

afference : BodyState → InteroceptiveAfference
afference (bodyState medium medium low high) = quietAfference
afference (bodyState high medium high low) = arousalAfference
afference (bodyState high high high low) = arousalAfference
-- Total fallback clauses keep this finite vocabulary total without claiming a
-- physiological partition theorem.
afference (bodyState low low low low) = quietAfference
afference (bodyState low low low medium) = quietAfference
afference (bodyState low low low high) = quietAfference
afference (bodyState low low medium low) = arousalAfference
afference (bodyState low low medium medium) = arousalAfference
afference (bodyState low low medium high) = arousalAfference
afference (bodyState low low high low) = arousalAfference
afference (bodyState low low high medium) = arousalAfference
afference (bodyState low low high high) = arousalAfference
afference (bodyState low medium low low) = quietAfference
afference (bodyState low medium low medium) = quietAfference
afference (bodyState low medium low high) = quietAfference
afference (bodyState low medium medium low) = arousalAfference
afference (bodyState low medium medium medium) = arousalAfference
afference (bodyState low medium medium high) = arousalAfference
afference (bodyState low medium high low) = arousalAfference
afference (bodyState low medium high medium) = arousalAfference
afference (bodyState low medium high high) = arousalAfference
afference (bodyState low high low low) = quietAfference
afference (bodyState low high low medium) = quietAfference
afference (bodyState low high low high) = quietAfference
afference (bodyState low high medium low) = arousalAfference
afference (bodyState low high medium medium) = arousalAfference
afference (bodyState low high medium high) = arousalAfference
afference (bodyState low high high low) = arousalAfference
afference (bodyState low high high medium) = arousalAfference
afference (bodyState low high high high) = arousalAfference
afference (bodyState medium low low low) = quietAfference
afference (bodyState medium low low medium) = quietAfference
afference (bodyState medium low low high) = quietAfference
afference (bodyState medium low medium low) = arousalAfference
afference (bodyState medium low medium medium) = arousalAfference
afference (bodyState medium low medium high) = arousalAfference
afference (bodyState medium low high low) = arousalAfference
afference (bodyState medium low high medium) = arousalAfference
afference (bodyState medium low high high) = arousalAfference
afference (bodyState medium medium low low) = quietAfference
afference (bodyState medium medium low medium) = quietAfference
afference (bodyState medium medium medium low) = arousalAfference
afference (bodyState medium medium medium medium) = arousalAfference
afference (bodyState medium medium medium high) = arousalAfference
afference (bodyState medium medium high low) = arousalAfference
afference (bodyState medium medium high medium) = arousalAfference
afference (bodyState medium medium high high) = arousalAfference
afference (bodyState medium high low low) = quietAfference
afference (bodyState medium high low medium) = quietAfference
afference (bodyState medium high low high) = quietAfference
afference (bodyState medium high medium low) = arousalAfference
afference (bodyState medium high medium medium) = arousalAfference
afference (bodyState medium high medium high) = arousalAfference
afference (bodyState medium high high low) = arousalAfference
afference (bodyState medium high high medium) = arousalAfference
afference (bodyState medium high high high) = arousalAfference
afference (bodyState high low low low) = quietAfference
afference (bodyState high low low medium) = quietAfference
afference (bodyState high low low high) = quietAfference
afference (bodyState high low medium low) = arousalAfference
afference (bodyState high low medium medium) = arousalAfference
afference (bodyState high low medium high) = arousalAfference
afference (bodyState high low high low) = arousalAfference
afference (bodyState high low high medium) = arousalAfference
afference (bodyState high low high high) = arousalAfference
afference (bodyState high medium low low) = quietAfference
afference (bodyState high medium low medium) = quietAfference
afference (bodyState high medium low high) = quietAfference
afference (bodyState high medium medium low) = arousalAfference
afference (bodyState high medium medium medium) = arousalAfference
afference (bodyState high medium medium high) = arousalAfference
afference (bodyState high medium high medium) = arousalAfference
afference (bodyState high medium high high) = arousalAfference
afference (bodyState high high low low) = quietAfference
afference (bodyState high high low medium) = quietAfference
afference (bodyState high high low high) = quietAfference
afference (bodyState high high medium low) = arousalAfference
afference (bodyState high high medium medium) = arousalAfference
afference (bodyState high high medium high) = arousalAfference
afference (bodyState high high high medium) = arousalAfference
afference (bodyState high high high high) = arousalAfference

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
