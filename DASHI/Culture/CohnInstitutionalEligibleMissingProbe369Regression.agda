module DASHI.Culture.CohnInstitutionalEligibleMissingProbe369Regression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalEligibleMissingProbe369Exact as Probe

realisedCarrierDoesNotDetermineProbe :
  Probe.realisedCarrierDeterminesMissingnessProbe
    Probe.canonicalEligibleMissingProbeBoundary ≡ false
realisedCarrierDoesNotDetermineProbe = refl

proofSearchReused :
  Probe.canonicalDialecticalProofSearchReused
    Probe.canonicalEligibleMissingProbeBoundary ≡ true
proofSearchReused = refl

schedulerReused :
  Probe.canonical369SchedulerBoundaryReused
    Probe.canonicalEligibleMissingProbeBoundary ≡ true
schedulerReused = refl

consumerRevisionDoesNotRewriteCarrier :
  Probe.consumerRevisionRewritesRealisedCarrier
    Probe.canonicalEligibleMissingProbeBoundary ≡ false
consumerRevisionDoesNotRewriteCarrier = refl

sourceDoesNotSelectMechanism :
  Probe.sourceCitationSelectsObservedMissingnessMechanism
    Probe.canonicalEligibleMissingProbeBoundary ≡ false
sourceDoesNotSelectMechanism = refl
