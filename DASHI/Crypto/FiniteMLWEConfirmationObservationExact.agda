module DASHI.Crypto.FiniteMLWEConfirmationObservationExact where

------------------------------------------------------------------------
-- FINITE MLWE LAB + CONFIRMATION OBSERVATION + NET RECOVERY COST
--
-- This composes the existing non-scalar Z/5Z MLWE regression with the generic
-- key-confirmation observation model.  The public collision remains ambiguous
-- until an externally visible confirmation result is supplied; that result
-- splits the two surviving candidates.  The observation is useful only when
-- acquisition cost plus post-observation recovery is below pre-observation
-- recovery cost.
--
-- This is a finite defensive regression, not a claim that ML-KEM confirmation
-- exposes such an oracle in a conforming deployment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Crypto.FiniteMLWEVectorLabExact as Lab
import DASHI.Crypto.FiniteMLWEPriorScoreSearchRegressionExact as LabSearch
import DASHI.Crypto.KeyConfirmationObservationRefinementExact as Confirm
import DASHI.Crypto.ObservationAcquisitionCostExact as Acquisition
import DASHI.Crypto.BlueTeamAdversaryObservationExact as Observation

labConfirmationOutcome : Lab.HiddenState → Bool → Bool
labConfirmationOutcome hidden presented =
  Confirm.boolEq (Lab.s0 (Lab.secret hidden)) presented

labConfirmationSystem : Confirm.ConfirmationObservationSystem
labConfirmationSystem =
  Confirm.confirmationObservationSystem
    Lab.HiddenState
    Lab.Public2
    Bool
    Lab.projectHidden
    labConfirmationOutcome

labConfirmationSplit : Confirm.ConfirmationSplitWitness labConfirmationSystem
labConfirmationSplit =
  Confirm.confirmationSplitWitness
    Lab.hidden01
    Lab.hidden10
    refl
    false
    different
  where
  different : true ≡ false → ⊥
  different ()

labConfirmationIsHiddenDependent :
  Observation.HiddenDependentSplit
    (Confirm.asAdversarySystem labConfirmationSystem)
labConfirmationIsHiddenDependent =
  Confirm.confirmationSplitGivesHiddenDependentObservation labConfirmationSplit

------------------------------------------------------------------------
-- Cost-aware value of the observation.
------------------------------------------------------------------------

labConfirmationCost2 : Acquisition.ObservationAcquisitionComparison
labConfirmationCost2 =
  Acquisition.observationAcquisitionComparison
    LabSearch.labBeforeObservation
    LabSearch.labAfterObservation
    2

labConfirmationCost2Total :
  Acquisition.afterWithObservationCost labConfirmationCost2 ≡ 10
labConfirmationCost2Total = refl

labConfirmationCost2NetGain :
  Acquisition.NetBeneficialObservation labConfirmationCost2
labConfirmationCost2NetGain = Acquisition.netBeneficialObservation 3 refl

labConfirmationCost6 : Acquisition.ObservationAcquisitionComparison
labConfirmationCost6 =
  Acquisition.observationAcquisitionComparison
    LabSearch.labBeforeObservation
    LabSearch.labAfterObservation
    6

labConfirmationCost6IsHarmful :
  Acquisition.NetHarmfulObservation labConfirmationCost6
labConfirmationCost6IsHarmful = Acquisition.netHarmfulObservation 1 refl

------------------------------------------------------------------------
-- The same hidden-dependent partition can therefore have opposite algorithmic
-- value under different acquisition costs.  Observation bandwidth/cardinality
-- alone is not the blue-team objective; net protected-label recovery cost is.
------------------------------------------------------------------------
