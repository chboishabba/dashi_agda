module DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact where

------------------------------------------------------------------------
-- FINITE EXECUTABLE SEARCH OVER THE PROOF-RELEVANT LEGAL ALGEBRA
--
-- This module adds terminating search procedures without collapsing a Boolean
-- search result into an Algebra.Derivation / MinimalCut / precedent receipt.
-- Promotion back into proof-relevant law remains an explicit second step.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String; primStringEquality)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawPrecedentApplicabilityDistinguishingExact as Precedent

------------------------------------------------------------------------
-- Small Boolean/list kernel.
------------------------------------------------------------------------

infixr 6 _&&ᵇ_
_&&ᵇ_ : Bool → Bool → Bool
true &&ᵇ b = b
false &&ᵇ b = false

infixr 5 _||ᵇ_
_||ᵇ_ : Bool → Bool → Bool
true ||ᵇ b = true
false ||ᵇ b = b

notᵇ : Bool → Bool
notᵇ true = false
notᵇ false = true

ifᵇ_then_else_ : ∀ {A : Set} → Bool → A → A → A
ifᵇ true then x else y = x
ifᵇ false then x else y = y

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

------------------------------------------------------------------------
-- Stable executable identity is proposition/rule id, not statement text.
------------------------------------------------------------------------

stableValue : Ontology.StableId → String
stableValue = Ontology.StableId.value

propositionKey : Algebra.LegalProposition → String
propositionKey p = stableValue (Algebra.propositionId p)

ruleKey : Algebra.LegalRule → String
ruleKey r = stableValue (Algebra.ruleId r)

sameProposition : Algebra.LegalProposition → Algebra.LegalProposition → Bool
sameProposition p q = primStringEquality (propositionKey p) (propositionKey q)

sameRuleId : String → Algebra.LegalRule → Bool
sameRuleId key r = primStringEquality key (ruleKey r)

memberString : String → List String → Bool
memberString x [] = false
memberString x (y ∷ ys) = primStringEquality x y ||ᵇ memberString x ys

memberProposition : Algebra.LegalProposition → List Algebra.LegalProposition → Bool
memberProposition p [] = false
memberProposition p (q ∷ qs) = sameProposition p q ||ᵇ memberProposition p qs

removeString : String → List String → List String
removeString x [] = []
removeString x (y ∷ ys) =
  ifᵇ primStringEquality x y
  then removeString x ys
  else y ∷ removeString x ys

------------------------------------------------------------------------
-- Bounded executable derivability.
------------------------------------------------------------------------

mutual
  reachableWithin :
    Nat → Algebra.LegalGraph → Algebra.FactSet → List String →
    Algebra.LegalProposition → Bool
  reachableWithin zero graph factSet disabled goal =
    memberProposition goal (Algebra.facts factSet)
  reachableWithin (suc depth) graph factSet disabled goal =
    memberProposition goal (Algebra.facts factSet)
    ||ᵇ someRuleReachesWithin
          depth graph factSet disabled goal (Algebra.rules graph)

  allReachableWithin :
    Nat → Algebra.LegalGraph → Algebra.FactSet → List String →
    List Algebra.LegalProposition → Bool
  allReachableWithin depth graph factSet disabled [] = true
  allReachableWithin depth graph factSet disabled (p ∷ ps) =
    reachableWithin depth graph factSet disabled p
    &&ᵇ allReachableWithin depth graph factSet disabled ps

  noneReachableWithin :
    Nat → Algebra.LegalGraph → Algebra.FactSet → List String →
    List Algebra.LegalProposition → Bool
  noneReachableWithin depth graph factSet disabled [] = true
  noneReachableWithin depth graph factSet disabled (p ∷ ps) =
    notᵇ (reachableWithin depth graph factSet disabled p)
    &&ᵇ noneReachableWithin depth graph factSet disabled ps

  someRuleReachesWithin :
    Nat → Algebra.LegalGraph → Algebra.FactSet → List String →
    Algebra.LegalProposition → List Algebra.LegalRule → Bool
  someRuleReachesWithin depth graph factSet disabled goal [] = false
  someRuleReachesWithin depth graph factSet disabled goal (r ∷ rs) =
    let enabled = notᵇ (memberString (ruleKey r) disabled)
        concludesGoal = sameProposition (Algebra.conclusion r) goal
        premisesPaid =
          allReachableWithin depth graph factSet disabled (Algebra.premises r)
        exceptionsAbsent =
          noneReachableWithin depth graph factSet disabled (Algebra.exceptions r)
        defeatersAbsent =
          noneReachableWithin depth graph factSet disabled (Algebra.defeaters r)
        fires = enabled &&ᵇ concludesGoal &&ᵇ premisesPaid
                &&ᵇ exceptionsAbsent &&ᵇ defeatersAbsent
    in fires ||ᵇ someRuleReachesWithin depth graph factSet disabled goal rs

reachable :
  Nat → Algebra.LegalGraph → Algebra.FactSet → Algebra.LegalProposition → Bool
reachable depth graph factSet goal = reachableWithin depth graph factSet [] goal

------------------------------------------------------------------------
-- Executable issue projection.
--
-- The proof-level IssueProjection uses a Set-valued activeRule predicate and is
-- intentionally not assumed decidable. The executable companion carries a
-- finite list of active rule ids. Unknown ids are detectable; inactive rules are
-- disabled before bounded search. Promotion still requires the proof-level
-- IssueProjection and IssueReachable witnesses.
------------------------------------------------------------------------

allActiveIdsKnownIn : List String → List Algebra.LegalRule → Bool
allActiveIdsKnownIn [] rules = true
allActiveIdsKnownIn (key ∷ keys) rules =
  ruleIdPresent key rules &&ᵇ allActiveIdsKnownIn keys rules
  where
    ruleIdPresent : String → List Algebra.LegalRule → Bool
    ruleIdPresent wanted [] = false
    ruleIdPresent wanted (r ∷ rs) =
      sameRuleId wanted r ||ᵇ ruleIdPresent wanted rs

inactiveRuleIds : List Algebra.LegalRule → List String → List String
inactiveRuleIds [] active = []
inactiveRuleIds (r ∷ rs) active =
  ifᵇ memberString (ruleKey r) active
  then inactiveRuleIds rs active
  else ruleKey r ∷ inactiveRuleIds rs active

record ExecutableIssueProjection
    (graph : Algebra.LegalGraph)
    (issue : Algebra.LegalIssue) : Set where
  constructor executable-issue-projection
  field
    activeRuleIds : List String
    activeRuleIdsKnown :
      allActiveIdsKnownIn activeRuleIds (Algebra.rules graph) ≡ true

open ExecutableIssueProjection public

issueReachable :
  Nat →
  (graph : Algebra.LegalGraph) →
  Algebra.FactSet →
  (issue : Algebra.LegalIssue) →
  ExecutableIssueProjection graph issue → Bool
issueReachable depth graph factSet issue projection =
  reachableWithin depth graph factSet
    (inactiveRuleIds (Algebra.rules graph) (activeRuleIds projection))
    (Algebra.target issue)

record IssueProjectionPromotion
    (depth : Nat)
    (graph : Algebra.LegalGraph)
    (factSet : Algebra.FactSet)
    (issue : Algebra.LegalIssue)
    (executable : ExecutableIssueProjection graph issue) : Set where
  constructor issue-projection-promotion
  field
    executableIssueHit :
      issueReachable depth graph factSet issue executable ≡ true
    proofRelevantProjection : Algebra.IssueProjection graph issue
    proofRelevantIssueDerivation :
      Algebra.IssueReachable graph factSet issue proofRelevantProjection

------------------------------------------------------------------------
-- Finite inclusion-minimal cut search.
------------------------------------------------------------------------

cutBlocksWithin :
  Nat → Algebra.LegalGraph → Algebra.FactSet → Algebra.LegalProposition →
  List String → Bool
cutBlocksWithin depth graph factSet goal cut =
  notᵇ (reachableWithin depth graph factSet cut goal)

everyCutRuleEssential :
  Nat → Algebra.LegalGraph → Algebra.FactSet → Algebra.LegalProposition →
  List String → List String → Bool
everyCutRuleEssential depth graph factSet goal wholeCut [] = true
everyCutRuleEssential depth graph factSet goal wholeCut (r ∷ rs) =
  reachableWithin depth graph factSet (removeString r wholeCut) goal
  &&ᵇ everyCutRuleEssential depth graph factSet goal wholeCut rs

isMinimalCutCandidate :
  Nat → Algebra.LegalGraph → Algebra.FactSet → Algebra.LegalProposition →
  List String → Bool
isMinimalCutCandidate depth graph factSet goal cut =
  cutBlocksWithin depth graph factSet goal cut
  &&ᵇ everyCutRuleEssential depth graph factSet goal cut cut

prependAll : ∀ {A : Set} → A → List (List A) → List (List A)
prependAll x [] = []
prependAll x (xs ∷ xss) = (x ∷ xs) ∷ prependAll x xss

subsets : ∀ {A : Set} → List A → List (List A)
subsets [] = [] ∷ []
subsets (x ∷ xs) =
  let rest = subsets xs
  in append rest (prependAll x rest)

ruleKeys : List Algebra.LegalRule → List String
ruleKeys [] = []
ruleKeys (r ∷ rs) = ruleKey r ∷ ruleKeys rs

data SearchResult (A : Set) : Set where
  found : A → SearchResult A
  notFound : SearchResult A

firstMinimalCutFrom :
  Nat → Algebra.LegalGraph → Algebra.FactSet → Algebra.LegalProposition →
  List (List String) → SearchResult (List String)
firstMinimalCutFrom depth graph factSet goal [] = notFound
firstMinimalCutFrom depth graph factSet goal (cut ∷ cuts) with
  isMinimalCutCandidate depth graph factSet goal cut
... | true = found cut
... | false = firstMinimalCutFrom depth graph factSet goal cuts

searchMinimalCut :
  Nat → Algebra.LegalGraph → Algebra.FactSet → Algebra.LegalProposition →
  SearchResult (List String)
searchMinimalCut depth graph factSet goal =
  firstMinimalCutFrom depth graph factSet goal
    (subsets (ruleKeys (Algebra.rules graph)))

------------------------------------------------------------------------
-- Executable precedent-feature fit / distinguishing search.
------------------------------------------------------------------------

allFeaturesPresent :
  List Algebra.LegalProposition → List Algebra.LegalProposition → Bool
allFeaturesPresent [] current = true
allFeaturesPresent (required ∷ requireds) current =
  memberProposition required current &&ᵇ allFeaturesPresent requireds current

firstMissingFeature :
  List Algebra.LegalProposition → List Algebra.LegalProposition →
  SearchResult Algebra.LegalProposition
firstMissingFeature [] current = notFound
firstMissingFeature (required ∷ requireds) current with memberProposition required current
... | true = firstMissingFeature requireds current
... | false = found required

precedentFeatureFitCandidate :
  Precedent.PrecedentProposition → Precedent.CurrentCase → Bool
precedentFeatureFitCandidate precedent current =
  allFeaturesPresent
    (Precedent.materialFeatures precedent)
    (Precedent.factsAndFeatures current)

minimalDistinguishingCandidate :
  Precedent.PrecedentProposition → Precedent.CurrentCase →
  SearchResult Algebra.LegalProposition
minimalDistinguishingCandidate precedent current =
  firstMissingFeature
    (Precedent.materialFeatures precedent)
    (Precedent.factsAndFeatures current)

------------------------------------------------------------------------
-- Ordered finite transformation search.
------------------------------------------------------------------------

record ExecutableTransformationCandidate
    (goal : Algebra.LegalProposition) : Set where
  constructor executable-transformation-candidate
  field
    candidateLabel : String
    candidateGraph : Algebra.LegalGraph
    candidateFacts : Algebra.FactSet

open ExecutableTransformationCandidate public

firstReopeningTransformation :
  (depth : Nat) →
  (goal : Algebra.LegalProposition) →
  List (ExecutableTransformationCandidate goal) →
  SearchResult (ExecutableTransformationCandidate goal)
firstReopeningTransformation depth goal [] = notFound
firstReopeningTransformation depth goal (candidate ∷ candidates) with
  reachable depth (candidateGraph candidate) (candidateFacts candidate) goal
... | true = found candidate
... | false = firstReopeningTransformation depth goal candidates

------------------------------------------------------------------------
-- Proof-relevant promotion boundaries.
------------------------------------------------------------------------

record ReachabilityPromotion
    (depth : Nat)
    (graph : Algebra.LegalGraph)
    (factSet : Algebra.FactSet)
    (goal : Algebra.LegalProposition) : Set where
  constructor reachability-promotion
  field
    executableHit : reachable depth graph factSet goal ≡ true
    proofRelevantDerivation : Algebra.Reachable graph factSet goal

record CutPromotion
    (depth : Nat)
    (graph : Algebra.LegalGraph)
    (factSet : Algebra.FactSet)
    (goal : Algebra.LegalProposition)
    (candidate : List String) : Set where
  constructor cut-promotion
  field
    executableMinimalCut :
      isMinimalCutCandidate depth graph factSet goal candidate ≡ true
    proofRelevantMinimalCut : Algebra.MinimalCut graph factSet goal

record DistinguishingPromotion
    (precedent : Precedent.PrecedentProposition)
    (current : Precedent.CurrentCase) : Set where
  constructor distinguishing-promotion
  field
    executableFeatureMismatch :
      precedentFeatureFitCandidate precedent current ≡ false
    proofRelevantDistinguishingSet :
      Precedent.MinimalDistinguishingSet precedent current

record TransformationPromotion
    (depth : Nat)
    (goal : Algebra.LegalProposition)
    (candidate : ExecutableTransformationCandidate goal) : Set where
  constructor transformation-promotion
  field
    executableReopens :
      reachable depth (candidateGraph candidate) (candidateFacts candidate) goal
      ≡ true
    typedTransformation : Algebra.LegalTransformation
    proofRelevantReopenedDerivation :
      Algebra.Reachable (candidateGraph candidate) (candidateFacts candidate) goal

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data BooleanReachabilityIsDerivationTree : Set where
data BooleanCutIsProofRelevantMinimalCut : Set where
data MissingFeatureAutomaticallyLegallyMaterial : Set where
data SearchOrderCreatesLegalAuthority : Set where
data ExecutableProjectionCreatesLegalRule : Set where

booleanReachabilityDoesNotBecomeProof : BooleanReachabilityIsDerivationTree → ⊥
booleanReachabilityDoesNotBecomeProof ()

booleanCutDoesNotBecomeProof : BooleanCutIsProofRelevantMinimalCut → ⊥
booleanCutDoesNotBecomeProof ()

featureMismatchDoesNotCreateMateriality :
  MissingFeatureAutomaticallyLegallyMaterial → ⊥
featureMismatchDoesNotCreateMateriality ()

searchOrderDoesNotCreateAuthority : SearchOrderCreatesLegalAuthority → ⊥
searchOrderDoesNotCreateAuthority ()

executableProjectionDoesNotCreateRule : ExecutableProjectionCreatesLegalRule → ⊥
executableProjectionDoesNotCreateRule ()
