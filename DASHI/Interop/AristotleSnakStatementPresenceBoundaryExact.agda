module DASHI.Interop.AristotleSnakStatementPresenceBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ZelphBoundedGraphCoverageExact as Zelph

------------------------------------------------------------------------
-- Source contracts rechecked against RequestProject.Snaks in the attached
-- Aristotle archive.
--
-- Native snak semantics are not property-presence semantics:
--   value / somevalue / novalue are statements in a snak base;
--   seeing no statement row for Q/P is a coverage-qualified observation about
--   the selected surface, not a native novalue assertion.
------------------------------------------------------------------------

data NativeSnakType : Set where
  valueSnak someValueSnak noValueSnak : NativeSnakType

data PropertyStatementPresence : Set where
  statementPresent noStatementObserved statementPresenceUnresolved : PropertyStatementPresence

record AristotleSnakContract : Set where
  constructor aristotle-snak-contract
  field
    sourceModule : String
    declaration : String
    contractReference : String
open AristotleSnakContract public

novalueEntailmentContract : AristotleSnakContract
novalueEntailmentContract =
  aristotle-snak-contract
    "RequestProject.Snaks"
    "Wikidata.SnakBase.entails_noValue_iff"
    "in a satisfiable snak base, novalue is entailed exactly when a novalue snak is asserted"

somevalueEntailmentContract : AristotleSnakContract
somevalueEntailmentContract =
  aristotle-snak-contract
    "RequestProject.Snaks"
    "Wikidata.SnakBase.entails_someValue_iff"
    "in a satisfiable snak base, somevalue is entailed exactly from an asserted somevalue or asserted concrete value"

clashContract : AristotleSnakContract
clashContract =
  aristotle-snak-contract
    "RequestProject.Snaks"
    "Wikidata.SnakBase.satisfiable_iff_clashFree"
    "novalue cannot coexist consistently with value or somevalue for the same subject-property pair"

presenceFromCoverageAndStatementRows :
  Zelph.QueryCoverageStatus → Bool → PropertyStatementPresence
presenceFromCoverageAndStatementRows Zelph.queryCoverageComplete true = statementPresent
presenceFromCoverageAndStatementRows Zelph.queryCoverageComplete false = noStatementObserved
presenceFromCoverageAndStatementRows Zelph.queryCoverageIncomplete _ = statementPresenceUnresolved
presenceFromCoverageAndStatementRows Zelph.queryCoverageUninspected _ = statementPresenceUnresolved
presenceFromCoverageAndStatementRows Zelph.queryCoverageInvalid _ = statementPresenceUnresolved

coveredNoRowsMeansNoStatementObserved :
  presenceFromCoverageAndStatementRows Zelph.queryCoverageComplete false ≡ noStatementObserved
coveredNoRowsMeansNoStatementObserved = refl

uninspectedNoRowsRemainUnresolved :
  presenceFromCoverageAndStatementRows Zelph.queryCoverageUninspected false ≡ statementPresenceUnresolved
uninspectedNoRowsRemainUnresolved = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data NoStatementObservedImpliesNativeNoValue : Set where
data NativeNoValueImpliesNoStatementRow : Set where
data PartialNonObservationImpliesNativeNoValue : Set where
\data NativeSnakCreatesMigrationAuthority : Set where

noStatementObservedDoesNotCreateNativeNoValue :
  NoStatementObservedImpliesNativeNoValue → ⊥
noStatementObservedDoesNotCreateNativeNoValue ()

nativeNoValueIsStillAStatement :
  NativeNoValueImpliesNoStatementRow → ⊥
nativeNoValueIsStillAStatement ()

partialNonObservationDoesNotCreateNativeNoValue :
  PartialNonObservationImpliesNativeNoValue → ⊥
partialNonObservationDoesNotCreateNativeNoValue ()

nativeSnakDoesNotCreateMigrationAuthority :
  NativeSnakCreatesMigrationAuthority → ⊥
nativeSnakDoesNotCreateMigrationAuthority ()

record SnakPresenceBoundary : Set where
  constructor snak-presence-boundary
  field
    nativeSnakAndStatementPresenceDistinct : Bool
    coveredNoRowsMayMeanNoStatementObserved : Bool
    coveredNoRowsMeanNativeNoValue : Bool
    nativeNoValueIsAStatement : Bool
    partialNonObservationMeansNativeNoValue : Bool
    nativeSnakCreatesMigrationAuthority : Bool

canonicalSnakPresenceBoundary : SnakPresenceBoundary
canonicalSnakPresenceBoundary =
  snak-presence-boundary true true false true false false

snakPresenceStatement : String
snakPresenceStatement =
  "Native Wikibase snak semantics and property-family statement presence are distinct. Under complete policy-relative Q/P coverage, no returned statement may be recorded as noStatementObserved, but it is not an asserted novalue snak. Incomplete or uninspected coverage remains unresolved, and no native snak creates migration authority."
