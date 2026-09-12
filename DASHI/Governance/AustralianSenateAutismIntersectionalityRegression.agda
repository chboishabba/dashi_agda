module DASHI.Governance.AustralianSenateAutismIntersectionalityRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Governance.AustralianSenateAutismIntersectionalityExact as AutismI

------------------------------------------------------------------------
-- Regression surface: the autism inquiry intersectionality weld must reuse
-- existing situated/longitudinal/representation machinery without promoting
-- a finite cohort list into an exhaustive account of autistic people.
------------------------------------------------------------------------

cohortListNotExhaustive : AutismI.committeeCohortListExhaustive ≡ false
cohortListNotExhaustive = refl

singleAxisNotAdequate : AutismI.singleAxisAutomaticallyAdequate ≡ false
singleAxisNotAdequate = refl

strategyTextNotImplementation : AutismI.strategyIntersectionalityTextPaysImplementation ≡ false
strategyTextNotImplementation = refl

affectedPeopleRetainArticulation : AutismI.affectedConstituencyMayArticulateFurtherAxes ≡ true
affectedPeopleRetainArticulation = refl

recognitionNotDistribution : AutismI.recognitionAlonePaysDistribution ≡ false
recognitionNotDistribution = refl

representationNotDistribution : AutismI.representationAlonePaysDistribution ≡ false
representationNotDistribution = refl

longitudinalCarrierPresent : AutismI.autismIntersectionalLongitudinalCarrierExists ≡ true
longitudinalCarrierPresent = refl
