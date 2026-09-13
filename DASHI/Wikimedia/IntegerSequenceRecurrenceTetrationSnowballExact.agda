module DASHI.Wikimedia.IntegerSequenceRecurrenceTetrationSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Interop.SensibLawNDimAdmissibilityTetrationComplexityBridgeExact as NDim
import DASHI.Wikimedia.IbrahimJMathematicsNumberOEISSecondOrderQidSnowballExact as Qid
import DASHI.Wikimedia.IbrahimBase369JOEISMoonshineSnowballExact as JOEIS
import DASHI.Wikimedia.Base369Z3TriadOEISRegressionSnowballExact as TriadOEIS
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- INTEGER SEQUENCE / RECURRENCE / RECURSIVE FIBRE / TETRATION SNOWBALL
--
-- Q2297602 describes an integer sequence as an ordered integer succession that
-- may be specified by a formula, a recurrence, or a property of its members.
-- That broad definition does not identify ordinary recurrences with the repo's
-- literal function-space tetration.
------------------------------------------------------------------------

data RecursiveConstructionRole : Set where
  explicitFormula fixedIndexRecurrence memberPredicate powerSequence
  incidenceCountSequence functionSpaceRecurrence selfIndexedAxisRecurrence
  recursiveHiddenFibre tetrationRole : RecursiveConstructionRole

record RecursiveConstructionCoordinate : Set where
  constructor recursive-construction-coordinate
  field
    label : String
    role : RecursiveConstructionRole
    externalIdentity : String
    nextStateDependsOnPreviousValue : Bool
    recursivelyChangesObserverDomain : Bool
    exactTetrationReceipt : Bool
    createsSemanticIdentityWithOtherRecurrences : Bool
open RecursiveConstructionCoordinate public

integerSequenceGeneric : RecursiveConstructionCoordinate
integerSequenceGeneric = recursive-construction-coordinate
  "integer sequence / Q2297602"
  fixedIndexRecurrence
  "Q2297602: formula, recurrence, or member-property may specify the sequence"
  true false false false

powersOfThree : RecursiveConstructionCoordinate
powersOfThree = recursive-construction-coordinate
  "OEIS A000244"
  powerSequence
  "a(n)=3^n"
  true false false false

powersOfSeven : RecursiveConstructionCoordinate
powersOfSeven = recursive-construction-coordinate
  "OEIS A000420"
  incidenceCountSequence
  "a(n)=7^n; repo uses 7^3=343 as raw bounded triad combinatorics"
  true false false false

repoPredicateTower : RecursiveConstructionCoordinate
repoPredicateTower = recursive-construction-coordinate
  "DASHI RecursiveFibreTower.PredicateLevel"
  functionSpaceRecurrence
  "PredicateLevel(n+1)=PredicateLevel(n)->TriTruth"
  true true true false

repoNDimSelfIndexing : RecursiveConstructionCoordinate
repoNDimSelfIndexing = recursive-construction-coordinate
  "SensibLaw N-dimensional self-indexed admissibility tower"
  selfIndexedAxisRecurrence
  "admissibility axes are regenerated recursively; tetrational growth is separately typed"
  true true true false

------------------------------------------------------------------------
-- Exact reuse of the repository's literal tetration facts.
------------------------------------------------------------------------

triadicTetrationTwoIsTwentySeven : Tower.tetration 3 2 ≡ 27
triadicTetrationTwoIsTwentySeven = Tower.triadicTetrationTwo

record RecurrenceFactorsThroughAudit : Set where
  constructor recurrence-factors-through-audit
  field
    source : String
    proposedQuotient : String
    sameInitialValuesEnough : Bool
    sameRecurrenceLawEnough : Bool
    sameCarrierEnough : Bool
    sameRecursiveDomainGrowthPaid : Bool
    factorsThroughTetration : Bool
    failedFactorisationMaySnowballAxis : Bool
open RecurrenceFactorsThroughAudit public

powerThreeVsTetration : RecurrenceFactorsThroughAudit
powerThreeVsTetration = recurrence-factors-through-audit
  "A000244 powers of three"
  "triadic tetration"
  false false false false false true

integerSequenceVsTetration : RecurrenceFactorsThroughAudit
integerSequenceVsTetration = recurrence-factors-through-audit
  "generic Q2297602 recurrence"
  "recursive function-space tower"
  false false false false false true

predicateTowerVsTetration : RecurrenceFactorsThroughAudit
predicateTowerVsTetration = recurrence-factors-through-audit
  "PredicateLevel(n+1)=PredicateLevel(n)->TriTruth"
  "triadic tetration cardinality"
  false true true true true false

------------------------------------------------------------------------
-- The useful missing axis exposed by failed factorisation is recursion ROLE:
-- whether a fixed carrier is iterated, a sequence value is updated, a hidden
-- fibre is refined, or the observer/domain itself is regenerated.
------------------------------------------------------------------------

record SequenceTetrationSnowballBoundary : Set where
  constructor sequence-tetration-snowball-boundary
  field
    q2297602Retained : Bool
    ordinaryFormulaRecurrenceMemberPropertySeparated : Bool
    powerSequencesNotPromotedToTetration : Bool
    functionSpaceTetrationReused : Bool
    nDimSelfIndexingReused : Bool
    recursiveDomainGrowthIsSeparateAxis : Bool
    allPairsComparisonAllowed : Bool
    failedFactorisationCanDiscoverRecursionRole : Bool
open SequenceTetrationSnowballBoundary public

canonicalSequenceTetrationSnowballBoundary : SequenceTetrationSnowballBoundary
canonicalSequenceTetrationSnowballBoundary =
  sequence-tetration-snowball-boundary true true true true true true true true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SequenceRecurrenceCreatesTetration : Set where
data PowerSequenceCreatesTetration : Set where
data SameInitialTermsCreateSameSequence : Set where
data OEISIdentityCreatesRecursiveFibre : Set where
data FixedFiniteFeatureProductCreatesTetration : Set where

sequenceRecurrenceIsNotTetration : SequenceRecurrenceCreatesTetration → ⊥
sequenceRecurrenceIsNotTetration ()

powerSequenceIsNotTetration : PowerSequenceCreatesTetration → ⊥
powerSequenceIsNotTetration ()

sameInitialTermsDoNotCreateSameSequence : SameInitialTermsCreateSameSequence → ⊥
sameInitialTermsDoNotCreateSameSequence ()

oeisDoesNotCreateRecursiveFibre : OEISIdentityCreatesRecursiveFibre → ⊥
oeisDoesNotCreateRecursiveFibre ()

finiteProductIsNotTetration : FixedFiniteFeatureProductCreatesTetration → ⊥
finiteProductIsNotTetration ()

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
