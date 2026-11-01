module DASHI.Cognition.PNF.ExactVsRelevantResidualExact where

------------------------------------------------------------------------
-- EXACT VS CONSUMER-RELEVANT RESIDUAL
--
-- The spoken telescope example makes the distinction concrete.  For the
-- bounded consumer "who was seen?", the two fine parses are relevant-equivalent
-- and no parse residual is needed to preserve the answer.  Exact reconstruction
-- of the represented semantic branch still requires the parse coordinate.
--
-- Thus relevant residual complexity can be strictly lower than exact residual
-- complexity without promoting the coarse answer into universal semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SpokenTelescopeConsumerProjectionExact as Spoken

whoSeenRelevant : Spoken.SpokenPNFState → Spoken.SpokenPNFState → Set
whoSeenRelevant left right =
  Spoken.whoSeenProjection left ≡ Spoken.whoSeenProjection right

instrumentPossessionRelevantEquivalent :
  whoSeenRelevant Spoken.instrumentState Spoken.possessionState
instrumentPossessionRelevantEquivalent = refl

------------------------------------------------------------------------
-- Residual costs for this finite pair.
------------------------------------------------------------------------

data ResidualPurpose : Set where
  preserveWhoSeenAnswer : ResidualPurpose
  reconstructExactParse : ResidualPurpose

minimalResidualCost : ResidualPurpose → Nat
minimalResidualCost preserveWhoSeenAnswer = zero
minimalResidualCost reconstructExactParse = suc zero

relevantResidualCostIsZero :
  minimalResidualCost preserveWhoSeenAnswer ≡ 0
relevantResidualCostIsZero = refl

exactResidualCostIsOne :
  minimalResidualCost reconstructExactParse ≡ 1
exactResidualCostIsOne = refl

------------------------------------------------------------------------
-- Exact zero-residual no-go for the two parses: a single reconstruction from
-- the shared who-seen answer cannot equal both distinct fine states.
------------------------------------------------------------------------

record WhoSeenOnlyExactReopening : Set₁ where
  constructor whoSeenOnlyExactReopening
  field
    reopen : Spoken.Participant → Spoken.SpokenPNFState
    reopensInstrument :
      reopen (Spoken.whoSeenProjection Spoken.instrumentState)
      ≡ Spoken.instrumentState
    reopensPossession :
      reopen (Spoken.whoSeenProjection Spoken.possessionState)
      ≡ Spoken.possessionState

open WhoSeenOnlyExactReopening public

instrumentNotPossession :
  Spoken.instrumentState ≡ Spoken.possessionState → ⊥
instrumentNotPossession ()

whoSeenOnlyCannotReopenBothExactly : WhoSeenOnlyExactReopening → ⊥
whoSeenOnlyCannotReopenBothExactly reopening =
  instrumentNotPossession
    (transEquality
      (symmetry (reopensInstrument reopening))
      (reopensPossession reopening))
  where
    symmetry :
      ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    symmetry refl = refl

    transEquality :
      ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    transEquality refl refl = refl

------------------------------------------------------------------------
-- The retained parse coordinate reopens both exact branches.
------------------------------------------------------------------------

parseResidualReopensBoth :
  (parse : Spoken.TelescopeParse) →
  Spoken.reopenFromSeenAnswer Spoken.john parse
  ≡
  Spoken.spokenPNFState
    parse
    Spoken.syntacticAttachmentResidual
    Spoken.askWhoSeen
parseResidualReopensBoth Spoken.instrumentParse = refl
parseResidualReopensBoth Spoken.possessionParse = refl
