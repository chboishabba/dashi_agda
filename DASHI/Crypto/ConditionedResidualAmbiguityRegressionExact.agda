module DASHI.Crypto.ConditionedResidualAmbiguityRegressionExact where

------------------------------------------------------------------------
-- CONDITIONING DOES NOT AUTOMATICALLY HALVE SEARCH
--
-- After the FIPS BaseCase algebra removes a known conditioned contribution, the
-- remaining equation is still noisy.  This finite Z/5Z regression shows the
-- precise obstruction: one conditioned scalar equation can admit two distinct
-- remaining secret bits because different small residuals explain the same
-- public value.
--
-- This is a regression model, not an ML-KEM parameter-set attack.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Crypto.FiniteMLWEVectorLabExact as Lab

conditionedPublic : Lab.Z5
conditionedPublic = Lab.z1

remainingResidual : Bool → Lab.Z5
remainingResidual candidate =
  Lab.sub5 conditionedPublic (Lab.embedBit candidate)

candidateFalseResidual : remainingResidual false ≡ Lab.z1
candidateFalseResidual = refl

candidateTrueResidual : remainingResidual true ≡ Lab.z0
candidateTrueResidual = refl

candidateFalseStillSmall : Lab.small (remainingResidual false) ≡ true
candidateFalseStillSmall = refl

candidateTrueStillSmall : Lab.small (remainingResidual true) ≡ true
candidateTrueStillSmall = refl

remainingCandidatesDistinct : false ≡ true → ⊥
remainingCandidatesDistinct ()

conditionedEquationLeavesTwoPlausibleSecrets :
  Lab.small (remainingResidual false) ≡ true
  × Lab.small (remainingResidual true) ≡ true
conditionedEquationLeavesTwoPlausibleSecrets = refl , refl

------------------------------------------------------------------------
-- Blue-team boundary: conditioning is a real algebraic simplification, but its
-- cryptanalytic value is determined by the conditional posterior/candidate
-- geometry after noise, not by the number of symbols eliminated syntactically.
------------------------------------------------------------------------

data ConditioningOutcome : Set where
  noisyConditioningCanRemainAmbiguous : ConditioningOutcome

conditioningOutcome : ConditioningOutcome
conditioningOutcome = noisyConditioningCanRemainAmbiguous
