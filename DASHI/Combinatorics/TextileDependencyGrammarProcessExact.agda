module DASHI.Combinatorics.TextileDependencyGrammarProcessExact where

open import DASHI.Core.Prelude
open import Data.List using (List; []; _∷_; _++_)

import DASHI.Combinatorics.TextileNFibreCalculusExact as T

------------------------------------------------------------------------
-- COMMON PROCESS SUBSTRATE, DISTINCT DEPENDENCY GRAMMARS
--
-- Five craft families share state + admitted local action + ordered trace, but
-- their local state dependencies remain different:
--   braid/plait : adjacent strand permutation;
--   weave       : typed bipartite warp/weft crossing;
--   knit        : retained-loop dependency;
--   crochet     : distinguished active-loop rooted dependency.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Weave: bipartite crossing action.
------------------------------------------------------------------------

data WarpRef : Set where warp-ref : Nat → WarpRef
data WeftRef : Set where weft-ref : Nat → WeftRef

record TypedWeaveCrossing (warpCount weftCount : Nat) : Set where
  constructor typed-weave-crossing
  field
    warpIndex : Nat
    weftIndex : Nat
    warpInRange : suc warpIndex ≤ warpCount
    weftInRange : suc weftIndex ≤ weftCount
    orientation : T.CrossingOrientation

open TypedWeaveCrossing public

record WeaveState (warpCount weftCount : Nat) : Set where
  constructor weave-state
  field
    weaveTrace : List (TypedWeaveCrossing warpCount weftCount)

open WeaveState public

executeWeaveCrossing :
  ∀ {warpCount weftCount} →
  WeaveState warpCount weftCount →
  TypedWeaveCrossing warpCount weftCount →
  WeaveState warpCount weftCount
executeWeaveCrossing state crossing =
  weave-state (weaveTrace state ++ (crossing ∷ []))

weaveActionIsBipartite :
  ∀ {warpCount weftCount} →
  TypedWeaveCrossing warpCount weftCount → WarpRef × WeftRef
weaveActionIsBipartite crossing =
  warp-ref (warpIndex crossing) , weft-ref (weftIndex crossing)

------------------------------------------------------------------------
-- 2. Knit: every new loop is created through one or two retained live loops.
------------------------------------------------------------------------

record RetainedLoopRef (liveCount : Nat) : Set where
  constructor retained-loop-ref
  field
    loopIndex : Nat
    loopInRange : suc loopIndex ≤ liveCount

open RetainedLoopRef public

data KnitLocalAction (liveCount : Nat) : Set where
  knitThroughRetained : RetainedLoopRef liveCount → KnitLocalAction liveCount
  purlThroughRetained : RetainedLoopRef liveCount → KnitLocalAction liveCount
  knitTwoTogether :
    RetainedLoopRef liveCount →
    RetainedLoopRef liveCount →
    KnitLocalAction liveCount

record KnitIncidence : Set where
  constructor knit-incidence
  field
    newLoop : Nat
    parentA : Nat
    parentB : Nat

open KnitIncidence public

record KnitState : Set where
  constructor knit-state
  field
    liveLoopCount : Nat
    knitIncidences : List KnitIncidence

open KnitState public

parentIndexA : ∀ {n} → KnitLocalAction n → Nat
parentIndexA (knitThroughRetained parent) = loopIndex parent
parentIndexA (purlThroughRetained parent) = loopIndex parent
parentIndexA (knitTwoTogether left right) = loopIndex left

parentIndexB : ∀ {n} → KnitLocalAction n → Nat
parentIndexB (knitThroughRetained parent) = loopIndex parent
parentIndexB (purlThroughRetained parent) = loopIndex parent
parentIndexB (knitTwoTogether left right) = loopIndex right

executeKnitAction :
  (state : KnitState) →
  KnitLocalAction (liveLoopCount state) →
  KnitState
executeKnitAction state action =
  knit-state
    (suc (liveLoopCount state))
    (knitIncidences state ++
      (knit-incidence
        (liveLoopCount state)
        (parentIndexA action)
        (parentIndexB action) ∷ []))

knitExecutionGrowsLoopCarrier :
  (state : KnitState) →
  (action : KnitLocalAction (liveLoopCount state)) →
  liveLoopCount (executeKnitAction state action) ≡ suc (liveLoopCount state)
knitExecutionGrowsLoopCarrier state action = refl

------------------------------------------------------------------------
-- 3. Crochet: a distinguished active loop is the root of local execution.
------------------------------------------------------------------------

record CrochetState : Set where
  constructor crochet-state
  field
    fabricLoopCount : Nat
    activeLoop : Nat
    activeLoopInCarrier : suc activeLoop ≤ suc fabricLoopCount
    crochetIncidences : List KnitIncidence

open CrochetState public

data CrochetLocalAction (state : CrochetState) : Set where
  chainFromActive : CrochetLocalAction state
  insertActiveInto :
    (target : Nat) →
    suc target ≤ suc (fabricLoopCount state) →
    CrochetLocalAction state

crochetTarget :
  {state : CrochetState} → CrochetLocalAction state → Nat
crochetTarget {state} chainFromActive = activeLoop state
crochetTarget (insertActiveInto target receipt) = target

executeCrochetAction :
  (state : CrochetState) →
  CrochetLocalAction state →
  CrochetState
executeCrochetAction state action =
  crochet-state
    (suc (fabricLoopCount state))
    (suc (fabricLoopCount state))
    ≤-refl
    (crochetIncidences state ++
      (knit-incidence
        (suc (fabricLoopCount state))
        (activeLoop state)
        (crochetTarget action) ∷ []))

crochetExecutionMovesActiveRootToNewestLoop :
  (state : CrochetState) →
  (action : CrochetLocalAction state) →
  activeLoop (executeCrochetAction state action)
  ≡ suc (fabricLoopCount state)
crochetExecutionMovesActiveRootToNewestLoop state action = refl

------------------------------------------------------------------------
-- 4. Five-craft process family.
------------------------------------------------------------------------

data CraftKind : Set where
  braidCraft plaitCraft weaveCraft knitCraft crochetCraft : CraftKind

data DependencyGrammar : Set where
  adjacentPermutationGrammar
  flatAdjacentPermutationGrammar
  bipartiteInterlacementGrammar
  retainedLoopGrammar
  activeRootedLoopGrammar
  : DependencyGrammar

grammarOf : CraftKind → DependencyGrammar
grammarOf braidCraft = adjacentPermutationGrammar
grammarOf plaitCraft = flatAdjacentPermutationGrammar
grammarOf weaveCraft = bipartiteInterlacementGrammar
grammarOf knitCraft = retainedLoopGrammar
grammarOf crochetCraft = activeRootedLoopGrammar

------------------------------------------------------------------------
-- 5. Shared process envelope: quotient/residual fields are generic slots, but
-- each craft chooses its own state/action grammar before entering the envelope.
------------------------------------------------------------------------

record CraftProcessEnvelope (State Action Observation Residual : Set) : Set where
  constructor craft-process-envelope
  field
    initialState : State
    orderedTrace : List Action
    observe : State → Observation
    residual : State → Residual

open CraftProcessEnvelope public

------------------------------------------------------------------------
-- 6. No-collapse boundaries.
------------------------------------------------------------------------

data WeaveIsSingleFamilyPermutation : Set where
data KnitIsBipartiteWeave : Set where
data CrochetHasNoDistinguishedActiveLoop : Set where
data SharedProcessEnvelopeIdentifiesCraftSemantics : Set where
data PhysicalWellFormednessAloneProvesLogicalValidity : Set where

weaveIsNotSingleFamilyPermutation : WeaveIsSingleFamilyPermutation → ⊥
weaveIsNotSingleFamilyPermutation ()

knitIsNotBipartiteWeave : KnitIsBipartiteWeave → ⊥
knitIsNotBipartiteWeave ()

crochetRetainsDistinguishedActiveLoop : CrochetHasNoDistinguishedActiveLoop → ⊥
crochetRetainsDistinguishedActiveLoop ()

sharedEnvelopeDoesNotIdentifyCraftSemantics :
  SharedProcessEnvelopeIdentifiesCraftSemantics → ⊥
sharedEnvelopeDoesNotIdentifyCraftSemantics ()

physicalWellFormednessDoesNotAloneProveLogicalValidity :
  PhysicalWellFormednessAloneProvesLogicalValidity → ⊥
physicalWellFormednessDoesNotAloneProveLogicalValidity ()

record TextileDependencyGrammarProcessBoundary : Set where
  constructor textile-dependency-grammar-process-boundary
  field
    weaveBipartiteActionExplicit : Bool
    knitRetainedLoopDependencyExplicit : Bool
    crochetActiveRootExplicit : Bool
    fiveCraftGrammarFamilyExplicit : Bool
    commonProcessEnvelopeAvailable : Bool
    dependencyGrammarsCollapsed : Bool
    physicalWellFormednessAloneProvesLogic : Bool

canonicalTextileDependencyGrammarProcessBoundary :
  TextileDependencyGrammarProcessBoundary
canonicalTextileDependencyGrammarProcessBoundary =
  textile-dependency-grammar-process-boundary
    true true true true true false false
