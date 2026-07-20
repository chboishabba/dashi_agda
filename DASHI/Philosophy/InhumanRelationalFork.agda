module DASHI.Philosophy.InhumanRelationalFork where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Two different consequences can follow from decentring the sovereign human.
--
-- 1. machinic dissolution: impersonal process is allowed to outrun human
--    measure;
-- 2. more-than-human reciprocity: ethical consideration is widened beyond
--    human supremacy.
--
-- Shared anti-sovereign premises do not make these ethical branches equal.

data DecentringBranch : Set where
  machinicDissolution :
    DecentringBranch

  moreThanHumanReciprocity :
    DecentringBranch

data RelationalConstraint : Set where
  dependency :
    RelationalConstraint

  vulnerability :
    RelationalConstraint

  consent :
    RelationalConstraint

  repair :
    RelationalConstraint

  ecologicalContinuity :
    RelationalConstraint

  nonDomination :
    RelationalConstraint

canonicalRelationalConstraints :
  List RelationalConstraint
canonicalRelationalConstraints =
  dependency
  ∷ vulnerability
  ∷ consent
  ∷ repair
  ∷ ecologicalContinuity
  ∷ nonDomination
  ∷ []

record DecentringForkBoundary : Set where
  constructor mkDecentringForkBoundary
  field
    bothRejectSovereignLiberalIndividual :
      Bool

    machinicProcessesExceedIndividualIntentions :
      Bool

    moreThanHumanBranchExpandsEthicalConsideration :
      Bool

    machinicBranchAutomaticallyEthicallyAdmissible :
      Bool

    resistanceCanCarryMeaning :
      Bool

    impersonalSystemsReceiveMoralSovereignty :
      Bool

open DecentringForkBoundary public

canonicalDecentringForkBoundary :
  DecentringForkBoundary
canonicalDecentringForkBoundary =
  mkDecentringForkBoundary
    true
    true
    true
    false
    true
    false

canonicalNoMoralSovereigntyForSystems :
  impersonalSystemsReceiveMoralSovereignty canonicalDecentringForkBoundary
  ≡
  false
canonicalNoMoralSovereigntyForSystems =
  refl
