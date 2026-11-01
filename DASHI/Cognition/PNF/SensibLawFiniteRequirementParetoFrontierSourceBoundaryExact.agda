module DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierSourceBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- SOURCE / ATTRIBUTION BOUNDARY
--
-- The finite Pareto frontier, live-fibre salience relation, cost/gain comparison,
-- and scheduler policy are DASHI formal synthesis. They are not attributed to a
-- court, legislature, scholar, or historical source.
--
-- Application-level legal/historical propositions must preserve their explicit
-- source owners and stable identifiers (case citation, statutory identifier,
-- author/title/DOI, or another stable identifier where DOI is unavailable).
------------------------------------------------------------------------

record RequirementParetoSourceBoundary : Set where
  constructor requirement-pareto-source-boundary
  field
    frontierCompilerIsDASHISynthesis : Bool
    frontierCompilerIsDASHISynthesisIsTrue : frontierCompilerIsDASHISynthesis ≡ true
    compilerCreatesExternalSourceAuthority : Bool
    compilerCreatesExternalSourceAuthorityIsFalse : compilerCreatesExternalSourceAuthority ≡ false
    applicationSourcesRemainExplicit : Bool
    applicationSourcesRemainExplicitIsTrue : applicationSourcesRemainExplicit ≡ true
    stableIdentifierRequiredWhenExternalSourceUsed : Bool
    stableIdentifierRequiredWhenExternalSourceUsedIsTrue : stableIdentifierRequiredWhenExternalSourceUsed ≡ true

canonicalRequirementParetoSourceBoundary : RequirementParetoSourceBoundary
canonicalRequirementParetoSourceBoundary =
  requirement-pareto-source-boundary true refl false refl true refl true refl

data SchedulerSynthesisIsExternalLegalAuthority : Set where

data MissingStableIdentifierMayBeSilentlyFilled : Set where

schedulerSynthesisDoesNotBecomeAuthority : SchedulerSynthesisIsExternalLegalAuthority → ⊥
schedulerSynthesisDoesNotBecomeAuthority ()

missingIdentifierCannotBeSilentlyInvented : MissingStableIdentifierMayBeSilentlyFilled → ⊥
missingIdentifierCannotBeSilentlyInvented ()
