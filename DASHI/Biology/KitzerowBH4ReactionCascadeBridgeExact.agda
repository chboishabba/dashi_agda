module DASHI.Biology.KitzerowBH4ReactionCascadeBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Biology.KitzerowBH4CascadeExact as Cascade
import DASHI.Biology.KitzerowBH4ReactionChemistryExact as Reaction
import DASHI.Biology.KitzerowBH4SynthesisRegenerationExact as Cycle

------------------------------------------------------------------------
-- Bridge the coarse biological graph to literal repo-native reactions.
-- A branch may be reaction-backed without the whole causal path being proved.
------------------------------------------------------------------------

record ReactionBackedBranch : Set where
  constructor reactionBackedBranch
  field
    branchLabel : String
    biologicalGraphReference : String
    reactions : List Chemistry.Transition
    sharedBH4SpeciesReference : String
    reactionIdentityPaid : Bool
    reactionIdentityPaidIsTrue : reactionIdentityPaid ≡ true
    causalBranchClosurePaid : Bool
    causalBranchClosurePaidIsFalse : causalBranchClosurePaid ≡ false

open ReactionBackedBranch public

aaaHReactionBranch : ReactionBackedBranch
aaaHReactionBranch =
  reactionBackedBranch
    "AAAH / aromatic amino-acid hydroxylase branch"
    "KitzerowBH4CascadeExact: aaaHBranch"
    (Reaction.pahReaction ∷ Reaction.thReaction ∷ Reaction.tphReaction ∷ [])
    "Reaction.bh4 is the shared explicit BH4 species consumed by PAH/TH/TPH net reactions"
    true refl false refl

nosReactionBranch : ReactionBackedBranch
nosReactionBranch =
  reactionBackedBranch
    "NOS branch"
    "KitzerowBH4CascadeExact: nosBranch"
    (Reaction.nosCoupledReaction ∷ Reaction.nosUncoupledReaction ∷ [])
    "Reaction.bh4 is explicit catalytic context for the coupled branch; uncoupled branch is represented separately"
    true refl false refl

agmoReactionBranch : ReactionBackedBranch
agmoReactionBranch =
  reactionBackedBranch
    "AGMO ether-lipid branch"
    "KitzerowBH4CascadeExact: agmoBranch"
    (Reaction.agmoReaction ∷ [])
    "Reaction.bh4 is an explicit AGMO reactant/cofactor coordinate with BH2 product in the assay-level reaction representation"
    true refl false refl

bh4SupplyRecycleBranch : ReactionBackedBranch
bh4SupplyRecycleBranch =
  reactionBackedBranch
    "BH4 synthesis and regeneration"
    "central GCH1/redox-regulated BH4 supply coordinate"
    Cycle.canonicalBH4SupplyAndRecycleTransitions
    "GCH1/PTPS/SPR supply and PCD/DHPR recycle converge on the same Reaction.bh4 species object"
    true refl false refl

record ReactionCascadeBridgeBoundary : Set where
  constructor reactionCascadeBridgeBoundary
  field
    biologicalNodeMayStandInForLiteralReaction : Bool
    biologicalNodeMayStandInForLiteralReactionIsFalse :
      biologicalNodeMayStandInForLiteralReaction ≡ false
    branchReactionIdentityNowExplicit : Bool
    branchReactionIdentityNowExplicitIsTrue :
      branchReactionIdentityNowExplicit ≡ true
    sharedBH4SpeciesProvesFluxReallocation : Bool
    sharedBH4SpeciesProvesFluxReallocationIsFalse :
      sharedBH4SpeciesProvesFluxReallocation ≡ false
    reactionNetworkProvesAutismCausation : Bool
    reactionNetworkProvesAutismCausationIsFalse :
      reactionNetworkProvesAutismCausation ≡ false

canonicalReactionCascadeBridgeBoundary : ReactionCascadeBridgeBoundary
canonicalReactionCascadeBridgeBoundary =
  reactionCascadeBridgeBoundary false refl true refl false refl false refl

-- Keep the candidate graph owner visible at this bridge.  Importing it does not
-- upgrade any edge status.
candidateCascade : Cascade.KitzerowBH4Cascade
candidateCascade = Cascade.canonicalKitzerowBH4Cascade
