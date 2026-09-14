module DASHI.Core.InstitutionalStatusSignalAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- INSTITUTIONAL STATUS SIGNAL / SUBSTANTIVE ADEQUACY
--
-- Institutional familiarity, credential/status and social respectability are
-- observation coordinates, not truth or consumer-specific adequacy primitives.
-- This finite witness is intentionally generic: it names no profession,
-- religion, institution, diagnosis, class or historical group.
------------------------------------------------------------------------

data StatusWorld : Set where
  highStatusAdequateWorld : StatusWorld
  highStatusInadequateWorld : StatusWorld

data StatusSurface : Set where
  sameHighInstitutionalStatus : StatusSurface

data StatusQuery : Set where
  statusIdentityQuery : StatusQuery
  substantiveAdequacyQuery : StatusQuery

data StatusAnswer : Set where
  sameStatusAnswer : StatusAnswer
  adequateForDeclaredConsumer : StatusAnswer
  inadequateForDeclaredConsumer : StatusAnswer

statusSurface : StatusWorld → StatusSurface
statusSurface world = sameHighInstitutionalStatus

statusAnswer : StatusQuery → StatusWorld → StatusAnswer
statusAnswer statusIdentityQuery world = sameStatusAnswer
statusAnswer substantiveAdequacyQuery highStatusAdequateWorld =
  adequateForDeclaredConsumer
statusAnswer substantiveAdequacyQuery highStatusInadequateWorld =
  inadequateForDeclaredConsumer

statusSemantics : Query.QuerySemantics StatusWorld StatusQuery StatusAnswer
statusSemantics = Query.querySemantics statusAnswer

statusIdentityAdequate :
  Query.AdequateFor statusSurface statusSemantics statusIdentityQuery
statusIdentityAdequate =
  Query.factorsForQuery (λ surface → sameStatusAnswer) (λ world → refl)

SubstantiveAdequacyQueryDefect : Set₁
SubstantiveAdequacyQueryDefect =
  Query.QueryAdequacyDefect
    statusSurface
    statusSemantics
    substantiveAdequacyQuery

substantiveAdequacyQueryDefect : SubstantiveAdequacyQueryDefect
substantiveAdequacyQueryDefect =
  Query.queryAdequacyDefect
    highStatusAdequateWorld
    highStatusInadequateWorld
    refl
    (λ ())

SubstantiveAdequacyThroughStatus : Set₁
SubstantiveAdequacyThroughStatus =
  Query.AdequateFor
    statusSurface
    statusSemantics
    substantiveAdequacyQuery

substantiveAdequacyDoesNotFactorThroughStatus :
  SubstantiveAdequacyThroughStatus → ⊥
substantiveAdequacyDoesNotFactorThroughStatus =
  Query.queryAdequacyDefectBlocksFactorisation substantiveAdequacyQueryDefect

record InstitutionalStatusSignalBoundary : Set where
  constructor institutionalStatusSignalBoundary
  field
    statusSignalAutomaticallySubstantiveAdequacy : Bool
    institutionalFamiliarityAutomaticallyTruth : Bool
    credentialAutomaticallyConsumerSpecificFit : Bool
    respectabilityAutomaticallyMoralConduct : Bool
    repeatedInstitutionalAccessAutomaticallyEpistemicSuperiority : Bool
    lowInstitutionalFamiliarityAutomaticallyLowReliability : Bool
    statusAndSubstantiveCoordinatesRemainSeparate : Bool

open InstitutionalStatusSignalBoundary public

canonicalInstitutionalStatusSignalBoundary : InstitutionalStatusSignalBoundary
canonicalInstitutionalStatusSignalBoundary =
  institutionalStatusSignalBoundary
    false
    false
    false
    false
    false
    false
    true
