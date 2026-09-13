module DASHI.Core.SnowballHistoricalProgrammeNameCollisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- HISTORICAL "SNOWBALL" PROGRAMME NAME COLLISIONS
--
-- The generic DASHI snowball method is not historically derived from, and does
-- not inherit semantics from, any military/intelligence programme merely because
-- they share the word "Snowball".  This owner records several independently
-- sourced historical uses so name equality cannot collapse programme identity.
------------------------------------------------------------------------

data ProgrammeClass : Set where
  conventionalBlastEffectsTrial : ProgrammeClass
  nuclearFieldExercise : ProgrammeClass
  armsTransferLogisticsProgramme : ProgrammeClass
  militaryConstructionReview : ProgrammeClass
  dashiEvidenceSnowballMethod : ProgrammeClass

record NamedSnowballProgramme : Set where
  constructor named-snowball-programme
  field
    canonicalName : String
    yearOrPeriod : String
    jurisdictionOrSponsor : String
    programmeClass : ProgrammeClass
    sourceLocator : String
    sourceRole : String
    narrowDescription : String

open NamedSnowballProgramme public

suffield1964 : NamedSnowballProgramme
suffield1964 = named-snowball-programme
  "Operation SNOWBALL"
  "1964"
  "Canada Defence Research Board / Suffield; United States and United Kingdom participation"
  conventionalBlastEffectsTrial
  "https://www.canada.ca/en/department-national-defence/campaigns/defence-research-through-the-decades.html"
  "official Canadian defence history; corroborated by U.S. Defense Nuclear Agency history and technical reports"
  "500-ton TNT conventional explosive trial used to study blast/ground-shock phenomena relevant to nuclear-weapons effects"

totskoye1954 : NamedSnowballProgramme
totskoye1954 = named-snowball-programme
  "Snowball / Snezok code name for Totskoye nuclear exercise"
  "1954"
  "Soviet Army"
  nuclearFieldExercise
  "historical-source lineage; exact archival primary carrier still to be pinned"
  "historical programme identity only"
  "Soviet field exercise involving a live nuclear detonation; kept distinct from the 1964 Canadian allied conventional-blast trial"

iranContra1986 : NamedSnowballProgramme
iranContra1986 = named-snowball-programme
  "Operation Snowball"
  "1986-1987"
  "United States Department of Defense / Army / CIA transfer context"
  armsTransferLogisticsProgramme
  "U.S. House Committee on Armed Services, Report on the Department of Defense Role in the Sale of Military Equipment to the Islamic Republic of Iran: Operation Snowball and Operation Crocus (1987)"
  "U.S. congressional report identity; National Security Archive / Library of Congress lineage"
  "TOW missile procurement/transfer logistics in the Iran-Contra arms-transfer context"

airForce1952 : NamedSnowballProgramme
airForce1952 = named-snowball-programme
  "Operation Snowball I"
  "1952"
  "United States Air Force"
  militaryConstructionReview
  "U.S. Air Force historical study, Establishing Independence"
  "official institutional history"
  "line-by-line military construction programme review supporting expanded Air Force force structure"

dashiSnowball : NamedSnowballProgramme
dashiSnowball = named-snowball-programme
  "DASHI snowball"
  "2026"
  "DASHI"
  dashiEvidenceSnowballMethod
  "DASHI.Core snowball invariant owners"
  "internal formal-method provenance"
  "consumer-relative evidence/provenance accumulation with non-promoting acquisition and receipt-gated payment"

record SnowballNameCollisionBoundary : Set where
  constructor snowball-name-collision-boundary
  field
    sameNameImpliesSameProgramme : Bool
    historicalMilitaryProgrammeDefinesDashiMethod : Bool
    dashiMethodInheritsMilitaryPurposeByName : Bool
    historicalProgrammeMayBeRetainedAsSourceAtom : Bool
    eachProgrammeNeedsIndependentSourceIdentity : Bool
    unresolvedPrimaryCarrierMayBeGuessed : Bool

canonicalSnowballNameCollisionBoundary : SnowballNameCollisionBoundary
canonicalSnowballNameCollisionBoundary =
  snowball-name-collision-boundary false false false true true false
