module DASHI.Philosophy.ClosureInteractionLaws where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Philosophy.ClosureKinds as Closure

------------------------------------------------------------------------
-- Different closure kinds do not collapse into one another.

record ClosureInteractionBoundary : Set where
  constructor closureInteractionBoundary
  field
    epistemicImpliesPolitical : Bool
    practicalImpliesRelational : Bool
    administrativeImpliesEpistemic : Bool
    politicalImpliesRelational : Bool
    unresolvedResidualBlocksEpistemicClosure : Bool
    grammarMustRemainVisible : Bool

open ClosureInteractionBoundary public

canonicalClosureInteractionBoundary : ClosureInteractionBoundary
canonicalClosureInteractionBoundary =
  closureInteractionBoundary
    false
    false
    false
    false
    true
    true

canonicalAdministrativeDoesNotImplyEpistemic :
  administrativeImpliesEpistemic canonicalClosureInteractionBoundary
  ≡ false
canonicalAdministrativeDoesNotImplyEpistemic = refl

record UnresolvedResidualClosureReceipt
       (Grammar Claim Residual : Set) : Set₁ where
  field
    grammar : Grammar
    claim : Claim
    residual : Residual
    administrativeClosure :
      Closure.ClosureReceipt Grammar Claim
    residualUnresolved : Set
    epistemicClosureBlocked : Set

open UnresolvedResidualClosureReceipt public

record ConditionalClosureBridge
       (Grammar Claim Evidence : Set) : Set₁ where
  field
    sourceKind : Closure.ClosureKind
    targetKind : Closure.ClosureKind
    grammar : Grammar
    claim : Claim
    evidence : Evidence
    bridgeConditions : Set
    noUnconditionalPromotion : Set

open ConditionalClosureBridge public
