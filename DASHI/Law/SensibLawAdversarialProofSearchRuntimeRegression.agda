module DASHI.Law.SensibLawAdversarialProofSearchRuntimeRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.SensibLawAdversarialProofSearchRuntimeExact as Adversarial

boundary : Adversarial.AdversarialProofSearchRuntimeBoundary
boundary =
  Adversarial.canonicalAdversarialProofSearchRuntimeBoundary

paired :
  Adversarial.supportAndDefeaterSearchRemainPaired boundary ≡ true
paired =
  Adversarial.supportAndDefeaterSearchRemainPairedIsTrue boundary

defeatMayClose :
  Adversarial.reviewedDefeaterMayCloseCandidateRoute boundary ≡ true
defeatMayClose =
  Adversarial.reviewedDefeaterMayCloseCandidateRouteIsTrue boundary

counterDefeatSearch :
  Adversarial.closedRouteMaySearchCounterDefeater boundary ≡ true
counterDefeatSearch =
  Adversarial.closedRouteMaySearchCounterDefeaterIsTrue boundary

reopenedFacesDefeatAgain :
  Adversarial.reopenedRouteFacesDefeaterSearchAgain boundary ≡ true
reopenedFacesDefeatAgain =
  Adversarial.reopenedRouteFacesDefeaterSearchAgainIsTrue boundary

analogyDoesNotPayRule :
  Adversarial.structuralAnalogyAutomaticallyPaysSubstantiveRule boundary ≡ false
analogyDoesNotPayRule =
  Adversarial.structuralAnalogyAutomaticallyPaysSubstantiveRuleIsFalse boundary

noFinalJudgment :
  Adversarial.adversarialSearchCreatesFinalJudgment boundary ≡ false
noFinalJudgment =
  Adversarial.adversarialSearchCreatesFinalJudgmentIsFalse boundary
