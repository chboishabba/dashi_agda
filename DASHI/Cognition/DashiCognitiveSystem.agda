module DASHI.Cognition.DashiCognitiveSystem where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (_+_; _∸_; _⊔_; _≤_)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; toList)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.ResidualPhaseGeometry as RPG
import DASHI.Combinatorics.PDA_MDL.PDA as ExistingPDA
import DASHI.Combinatorics.PDA_MDL.Prelude as MDL

------------------------------------------------------------------------
-- Exact ternary feasibility sign.
------------------------------------------------------------------------

data SignedMargin : Set where
  negativeMargin : Nat → SignedMargin
  boundaryMargin : SignedMargin
  positiveMargin : Nat → SignedMargin

gateFromMargin : SignedMargin → BT.Trit
gateFromMargin (negativeMargin _) = BT.neg
gateFromMargin boundaryMargin = BT.zero
gateFromMargin (positiveMargin _) = BT.pos

GateNotRejected : BT.Trit → Set
GateNotRejected BT.neg = ⊥
GateNotRejected BT.zero = ⊤
GateNotRejected BT.pos = ⊤

survivalWeight : BT.Trit → Nat
survivalWeight BT.neg = 0
survivalWeight BT.zero = 1
survivalWeight BT.pos = 1

infix 4 _∈_

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

------------------------------------------------------------------------
-- Master carrier, directly extending the in-repo PDA/MDL and quotient fibre.
------------------------------------------------------------------------

record DASHICognitiveSystem : Set₁ where
  field
    Hidden      : Set
    Observable  : Set
    Control     : Set
    StackSymbol : Set

    observe : Hidden → Observable
    admissibleWorld : Hidden → Set

    semanticStep : Control → Hidden → BT.Trit → Hidden
    stackStep : Control → List StackSymbol → BT.Trit → List StackSymbol
    margin : Control → Hidden → List StackSymbol → SignedMargin

    grammarCost : List BT.Trit → MDL.CodeLength
    modelCost : MDL.CodeLength
    distortion : Observable → Observable → MDL.CodeLength

    coarseGrain : Nat → Hidden → Hidden
    involution : Hidden → Hidden

    coarseObservationStable :
      ∀ scale hidden → observe (coarseGrain scale hidden) ≡ observe hidden

    involutionObservationStable :
      ∀ hidden → observe (involution hidden) ≡ observe hidden

open DASHICognitiveSystem public

asExistingPDA : (system : DASHICognitiveSystem) →
  ExistingPDA.PDA (Hidden system) (Observable system)
asExistingPDA system = record
  { observe = observe system
  ; admissible = admissibleWorld system
  ; costPDA = modelCost system
  }

hiddenProjection : (system : DASHICognitiveSystem) →
  RPG.Projection (Hidden system) (Observable system)
hiddenProjection system = record { observe = observe system }

HiddenFibre :
  (system : DASHICognitiveSystem) → Observable system → Set
HiddenFibre system observable = RPG.Fibre (hiddenProjection system) observable

ObservedEquivalent :
  (system : DASHICognitiveSystem) → Hidden system → Hidden system → Set
ObservedEquivalent system left right =
  observe system left ≡ observe system right

------------------------------------------------------------------------
-- Configurations, derivations, and prefix-closed admissibility witnesses.
------------------------------------------------------------------------

record Configuration (system : DASHICognitiveSystem) : Set where
  constructor configuration
  field
    hiddenState : Hidden system
    obligationStack : List (StackSymbol system)

open Configuration public

stepConfiguration :
  (system : DASHICognitiveSystem) →
  Control system →
  Configuration system →
  BT.Trit →
  Configuration system
stepConfiguration system control config token =
  configuration
    (semanticStep system control (hiddenState config) token)
    (stackStep system control (obligationStack config) token)

runConfiguration :
  (system : DASHICognitiveSystem) →
  Control system →
  Configuration system →
  List BT.Trit →
  Configuration system
runConfiguration system control config [] = config
runConfiguration system control config (token ∷ tokens) =
  runConfiguration system control
    (stepConfiguration system control config token)
    tokens

configurationGate :
  (system : DASHICognitiveSystem) →
  Control system →
  Configuration system →
  BT.Trit
configurationGate system control config =
  gateFromMargin
    (margin system control (hiddenState config) (obligationStack config))

AllPrefixesAdmissible :
  (system : DASHICognitiveSystem) →
  Control system →
  Configuration system →
  List BT.Trit →
  Set
AllPrefixesAdmissible system control config [] = ⊤
AllPrefixesAdmissible system control config (token ∷ tokens) =
  let next = stepConfiguration system control config token in
  admissibleWorld system (hiddenState next)
  × GateNotRejected (configurationGate system control next)
  × AllPrefixesAdmissible system control next tokens

record Accepted
    (system : DASHICognitiveSystem)
    (control : Control system)
    (start : Configuration system)
    (tokens : List BT.Trit) : Set where
  field
    everyPrefixAdmissible :
      AllPrefixesAdmissible system control start tokens

    terminalStackClosed :
      obligationStack (runConfiguration system control start tokens) ≡ []

    terminalCommitted :
      configurationGate system control
        (runConfiguration system control start tokens)
      ≡ BT.pos

LanguageAtDepth :
  (system : DASHICognitiveSystem) →
  Control system →
  Configuration system →
  Nat →
  Set
LanguageAtDepth system control start depth =
  Σ (Vec BT.Trit depth)
    (λ address → Accepted system control start (toList address))

firstPrefixSurvives :
  ∀ {system control start token tokens} →
  AllPrefixesAdmissible system control start (token ∷ tokens) →
  GateNotRejected
    (configurationGate system control
      (stepConfiguration system control start token))
firstPrefixSurvives evidence = proj₁ (proj₂ evidence)

------------------------------------------------------------------------
-- Classwise stability over the lossy observation quotient.
------------------------------------------------------------------------

record StableObservedClass
    (system : DASHICognitiveSystem)
    (representative : Hidden system) : Set where
  field
    coarseStable :
      ∀ scale →
      ObservedEquivalent system
        (coarseGrain system scale representative)
        representative

    involutionStable :
      ObservedEquivalent system
        (involution system representative)
        representative

canonicalStableObservedClass :
  (system : DASHICognitiveSystem) →
  (representative : Hidden system) →
  StableObservedClass system representative
canonicalStableObservedClass system representative = record
  { coarseStable =
      λ scale → coarseObservationStable system scale representative
  ; involutionStable = involutionObservationStable system representative
  }

------------------------------------------------------------------------
-- Constructive two-part MDL and exact finite-difference slope.
------------------------------------------------------------------------

MDLScore :
  (system : DASHICognitiveSystem) →
  Observable system →
  Control system →
  Configuration system →
  List BT.Trit →
  MDL.CodeLength
MDLScore system target control start tokens =
  modelCost system
  + grammarCost system tokens
  + distortion system target
      (observe system
        (hiddenState (runConfiguration system control start tokens)))

record DerivationArgMin
    (system : DASHICognitiveSystem)
    (target : Observable system)
    (control : Control system)
    (start : Configuration system)
    (candidates : List (List BT.Trit)) : Set where
  field
    best : List BT.Trit
    bestIsCandidate : best ∈ candidates
    minimal :
      ∀ candidate → candidate ∈ candidates →
      MDLScore system target control start best
      ≤ MDLScore system target control start candidate

record MDLFiniteDifference : Set where
  constructor mdlFiniteDifference
  field
    rise : Nat
    fall : Nat

mdlFiniteDifference : Nat → Nat → MDLFiniteDifference
mdlFiniteDifference before after = record
  { rise = after ∸ before
  ; fall = before ∸ after
  }

------------------------------------------------------------------------
-- Four complementary finite observables.
------------------------------------------------------------------------

branchingCount :
  (system : DASHICognitiveSystem) →
  Control system →
  Configuration system →
  Nat
branchingCount system control config =
  survivalWeight (configurationGate system control
    (stepConfiguration system control config BT.neg))
  + survivalWeight (configurationGate system control
    (stepConfiguration system control config BT.zero))
  + survivalWeight (configurationGate system control
    (stepConfiguration system control config BT.pos))

max3 : Nat → Nat → Nat → Nat
max3 a b c = (a ⊔ b) ⊔ c

mutual
  depthToFailure :
    (system : DASHICognitiveSystem) →
    Control system →
    Nat →
    Configuration system →
    Nat
  depthToFailure system control zero config = 0
  depthToFailure system control (suc fuel) config =
    max3
      (branchDepth system control fuel config BT.neg)
      (branchDepth system control fuel config BT.zero)
      (branchDepth system control fuel config BT.pos)

  branchDepth :
    (system : DASHICognitiveSystem) →
    Control system →
    Nat →
    Configuration system →
    BT.Trit →
    Nat
  branchDepth system control fuel config token with
    configurationGate system control
      (stepConfiguration system control config token)
  ... | BT.neg = 0
  ... | BT.zero =
    suc (depthToFailure system control fuel
      (stepConfiguration system control config token))
  ... | BT.pos =
    suc (depthToFailure system control fuel
      (stepConfiguration system control config token))

stackDepth : ∀ {system} → Configuration system → Nat
stackDepth config = length (obligationStack config)

data LanguagePhase : Set where
  collapsedPhase : LanguagePhase
  criticalPhase : LanguagePhase
  productivePhase : LanguagePhase

phaseFromBranching : Nat → LanguagePhase
phaseFromBranching zero = collapsedPhase
phaseFromBranching (suc zero) = criticalPhase
phaseFromBranching (suc (suc _)) = productivePhase

record PhaseObservables : Set where
  constructor phaseObservables
  field
    survivingDepth : Nat
    feasibleBranching : Nat
    mdlSlope : MDLFiniteDifference
    openObligationDepth : Nat
    languagePhase : LanguagePhase

observePhase :
  (system : DASHICognitiveSystem) →
  Control system →
  Nat →
  Configuration system →
  Nat →
  Nat →
  PhaseObservables
observePhase system control fuel config previousMDL currentMDL =
  let branches = branchingCount system control config in
  phaseObservables
    (depthToFailure system control fuel config)
    branches
    (mdlFiniteDifference previousMDL currentMDL)
    (stackDepth config)
    (phaseFromBranching branches)
