module DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact where

------------------------------------------------------------------------
-- PROOF-SEARCH LEAST-PRIVILEGE ADMISSION
--
-- Security/proof-search cross-pollination:
--   raw execution bypass          <-> raw theorem-route bypass
--   authority is not capability  <-> theorem name/string is not a proof
--   capability expansion         <-> hidden hypothesis expansion
--   actuator promotion           <-> programme-scoreboard promotion
--   reward hacking               <-> progress-metric Goodharting
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Typed theorem authority.
------------------------------------------------------------------------

data TheoremAuthority : Set where
  kernelCheckedHere
  kernelCheckedElsewhere
  sourceTheoremMatched
  derivedRepositoryTheorem
  conditionalInterface
  analogyOnly
  conjectural
  : TheoremAuthority

data ClosedLeafCapability : TheoremAuthority → Set where
  hereLeaf : ClosedLeafCapability kernelCheckedHere
  elsewhereLeaf : ClosedLeafCapability kernelCheckedElsewhere
  matchedSourceLeaf : ClosedLeafCapability sourceTheoremMatched
  derivedRepoLeaf : ClosedLeafCapability derivedRepositoryTheorem

analogyCannotCloseLeaf : ClosedLeafCapability analogyOnly → ⊥
analogyCannotCloseLeaf ()

conjectureCannotCloseLeaf : ClosedLeafCapability conjectural → ⊥
conjectureCannotCloseLeaf ()

------------------------------------------------------------------------
-- Route-admission obligations.
------------------------------------------------------------------------

data ExactTarget : Set where exactTarget : ExactTarget
data SameObjectSpine : Set where sameObjectSpine : SameObjectSpine
data PrerequisiteClosure : Set where prerequisiteClosure : PrerequisiteClosure
data NoKnownNoGo : Set where noKnownNoGo : NoKnownNoGo
data NoCircularDependency : Set where noCircularDependency : NoCircularDependency
data NoSilentHypothesisStrengthening : Set where noSilentStrengthening : NoSilentHypothesisStrengthening
data AuthorityAdequacy : Set where authorityAdequacy : AuthorityAdequacy
data NoveltyAgainstRepo : Set where noveltyAgainstRepo : NoveltyAgainstRepo
data FrontierImprovementWitness : Set where frontierImproves : FrontierImprovementWitness

record RouteAdmission : Set where
  constructor route-admission
  field
    exactTargetReceipt : ExactTarget
    sameObjectReceipt : SameObjectSpine
    prerequisiteReceipt : PrerequisiteClosure
    noGoReceipt : NoKnownNoGo
    circularityReceipt : NoCircularDependency
    hypothesisReceipt : NoSilentHypothesisStrengthening
    authorityReceipt : AuthorityAdequacy
    noveltyReceipt : NoveltyAgainstRepo
    frontierReceipt : FrontierImprovementWitness

open RouteAdmission public

data LiveProofSearch : Set where
  admittedLiveRoute : RouteAdmission → LiveProofSearch

elaborateRoute : RouteAdmission → LiveProofSearch
elaborateRoute = admittedLiveRoute

canonicalRouteAdmission : RouteAdmission
canonicalRouteAdmission =
  route-admission
    exactTarget
    sameObjectSpine
    prerequisiteClosure
    noKnownNoGo
    noCircularDependency
    noSilentStrengthening
    authorityAdequacy
    noveltyAgainstRepo
    frontierImproves

canonicalRouteIsLive : LiveProofSearch
canonicalRouteIsLive = elaborateRoute canonicalRouteAdmission

------------------------------------------------------------------------
-- Route errors are first-class instead of late narrative failures.
------------------------------------------------------------------------

data RouteError : Set where
  carrierMismatch
  scopeMismatch
  strengthMismatch
  circularity
  noGoCollision
  hypothesisInflation
  alreadyOwned
  consumerMismatch
  missingPrerequisite
  : RouteError

data RouteDisposition : Set where
  rejected : RouteError → RouteDisposition
  redirectedReuse : RouteDisposition
  admitted : RouteDisposition

rhBalanceRegression : RouteDisposition
rhBalanceRegression = rejected noGoCollision

nsESSRegression : RouteDisposition
nsESSRegression = rejected missingPrerequisite

yMGenericWrapperRegression : RouteDisposition
yMGenericWrapperRegression = rejected consumerMismatch

duplicateTheoremRegression : RouteDisposition
duplicateTheoremRegression = redirectedReuse

------------------------------------------------------------------------
-- Hypothesis budget: only explicit frontier leaves may extend the route.
------------------------------------------------------------------------

data HypothesisClass : Set where
  derivableFromBase
  authenticatedImportedTheorem
  explicitFrontierLeaf
  forbiddenStrengthening
  : HypothesisClass

data PermittedHypothesisAddition : HypothesisClass → Set where
  addDerivable : PermittedHypothesisAddition derivableFromBase
  addImported : PermittedHypothesisAddition authenticatedImportedTheorem
  addFrontierLeaf : PermittedHypothesisAddition explicitFrontierLeaf

forbiddenStrengtheningCannotBeAdded :
  PermittedHypothesisAddition forbiddenStrengthening → ⊥
forbiddenStrengtheningCannotBeAdded ()

------------------------------------------------------------------------
-- Programme promotion is separate from local theorem construction.
------------------------------------------------------------------------

data LocalLemma : Set where usefulLocalLemma : LocalLemma
data ExactConsumerReceipt : Set where exactConsumerReceipt : ExactConsumerReceipt
data ProgrammeProgress : Set where authoritativeProgress : ProgrammeProgress

promote : ExactConsumerReceipt → ProgrammeProgress
promote exactConsumerReceipt = authoritativeProgress

-- No LocalLemma -> ProgrammeProgress function is exposed by this module.

------------------------------------------------------------------------
-- Search metric independence: lemma count need not determine frontier progress.
------------------------------------------------------------------------

data SearchState : Set where
  manyLemmasNoClosure fewerLemmasTrueClosure : SearchState

lemmaCount : SearchState → Nat
lemmaCount manyLemmasNoClosure = suc (suc (suc zero))
lemmaCount fewerLemmasTrueClosure = suc zero

authoritativeFrontierReduced : SearchState → Bool
authoritativeFrontierReduced manyLemmasNoClosure = false
authoritativeFrontierReduced fewerLemmasTrueClosure = true

moreLemmasDoesNotForceProgress :
  authoritativeFrontierReduced manyLemmasNoClosure ≡ true → ⊥
moreLemmasDoesNotForceProgress ()

fewerLemmasCanBeRealProgress :
  authoritativeFrontierReduced fewerLemmasTrueClosure ≡ true
fewerLemmasCanBeRealProgress = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ProofSearchLeastPrivilegeBoundary : Set where
  constructor proof-search-least-privilege-boundary
  field
    theoremNameStringIsProofCapability : Bool
    theoremNameStringIsProofCapabilityIsFalse : theoremNameStringIsProofCapability ≡ false
    routeMayElaborateBeforeAdmission : Bool
    routeMayElaborateBeforeAdmissionIsFalse : routeMayElaborateBeforeAdmission ≡ false
    routeMaySilentlyStrengthenHypotheses : Bool
    routeMaySilentlyStrengthenHypothesesIsFalse : routeMaySilentlyStrengthenHypotheses ≡ false
    localLemmaAutomaticallyMovesProgrammeFrontier : Bool
    localLemmaAutomaticallyMovesProgrammeFrontierIsFalse :
      localLemmaAutomaticallyMovesProgrammeFrontier ≡ false
    lemmaCountIsAuthoritativeProgress : Bool
    lemmaCountIsAuthoritativeProgressIsFalse : lemmaCountIsAuthoritativeProgress ≡ false
    duplicateRouteShouldBeReproved : Bool
    duplicateRouteShouldBeReprovedIsFalse : duplicateRouteShouldBeReproved ≡ false
    reading : String

canonicalProofSearchLeastPrivilegeBoundary : ProofSearchLeastPrivilegeBoundary
canonicalProofSearchLeastPrivilegeBoundary =
  proof-search-least-privilege-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Proof search uses least privilege: candidate routes require an admission receipt before elaboration; theorem authority is typed; hidden hypothesis expansion is forbidden; local lemmas cannot move the programme frontier without an exact consumer receipt; progress is measured by authoritative obligation reduction rather than lemma production."
