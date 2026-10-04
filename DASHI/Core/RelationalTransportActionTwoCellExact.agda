module DASHI.Core.RelationalTransportActionTwoCellExact where

------------------------------------------------------------------------
-- EXTENSIONAL 2-CELLS BETWEEN RELATIONAL TRANSPORT ACTIONS
--
-- DASHI CONTRIBUTION
--
-- RelationalTransportGroupoidActionExact proves transport laws modulo the
-- pointwise action relation f ≈ g.  Here that relation is packaged as an
-- explicit 2-cell carrier between parallel transport homs.
--
-- A TransportAction2Cell f g is exactly:
--
--   forall x, forward f x = forward g x.
--
-- Identity, reversal, vertical composition and left/right whiskering are
-- constructed.  This yields a locally proof-relevant action-2-cell calculus
-- sufficient to state concrete transition cocycles.
--
-- It is NOT promoted to a bicategory or 2-groupoid: no theorem here identifies
-- proof/receipt-bearing transport records, supplies general horizontal
-- composition interchange at record level, or constructs higher associators.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.RelationalSelfDescentExact as Existing
import DASHI.Core.RelationalTransportGroupoidActionExact as Groupoid

TransportAction2Cell :
  {State : Set}
  {source target : Existing.RelationalPatch} →
  Groupoid.RelTransportHom State source target →
  Groupoid.RelTransportHom State source target →
  Set
TransportAction2Cell = Groupoid._≈_

identity2Cell :
  {State : Set}
  {source target : Existing.RelationalPatch}
  {f : Groupoid.RelTransportHom State source target} →
  TransportAction2Cell f f
identity2Cell =
  Groupoid.extensionalRefl

reverse2Cell :
  {State : Set}
  {source target : Existing.RelationalPatch}
  {f g : Groupoid.RelTransportHom State source target} →
  TransportAction2Cell f g →
  TransportAction2Cell g f
reverse2Cell =
  Groupoid.extensionalSym

verticalCompose :
  {State : Set}
  {source target : Existing.RelationalPatch}
  {f g h : Groupoid.RelTransportHom State source target} →
  TransportAction2Cell f g →
  TransportAction2Cell g h →
  TransportAction2Cell f h
verticalCompose =
  Groupoid.extensionalTrans

leftWhisker :
  {State : Set}
  {a b c : Existing.RelationalPatch}
  {f g : Groupoid.RelTransportHom State a b} →
  (h : Groupoid.RelTransportHom State b c) →
  TransportAction2Cell f g →
  TransportAction2Cell
    (Groupoid.composeHom h f)
    (Groupoid.composeHom h g)
leftWhisker h cell state =
  cong (Groupoid.forward h) (cell state)

rightWhisker :
  {State : Set}
  {a b c : Existing.RelationalPatch}
  {f g : Groupoid.RelTransportHom State b c} →
  (h : Groupoid.RelTransportHom State a b) →
  TransportAction2Cell f g →
  TransportAction2Cell
    (Groupoid.composeHom f h)
    (Groupoid.composeHom g h)
rightWhisker h cell state =
  cell (Groupoid.forward h state)

verticalIdentityLeft :
  {State : Set}
  {source target : Existing.RelationalPatch}
  {f g : Groupoid.RelTransportHom State source target}
  (cell : TransportAction2Cell f g) →
  (state : State) →
  verticalCompose identity2Cell cell state
  ≡ cell state
verticalIdentityLeft cell state = refl

verticalIdentityRight :
  {State : Set}
  {source target : Existing.RelationalPatch}
  {f g : Groupoid.RelTransportHom State source target}
  (cell : TransportAction2Cell f g) →
  (state : State) →
  verticalCompose cell identity2Cell state
  ≡ cell state
verticalIdentityRight cell state = refl

verticalAssociative :
  {State : Set}
  {source target : Existing.RelationalPatch}
  {f g h k : Groupoid.RelTransportHom State source target}
  (alpha : TransportAction2Cell f g)
  (beta : TransportAction2Cell g h)
  (gamma : TransportAction2Cell h k) →
  (state : State) →
  verticalCompose (verticalCompose alpha beta) gamma state
  ≡ verticalCompose alpha (verticalCompose beta gamma) state
verticalAssociative alpha beta gamma state
  with alpha state | beta state | gamma state
... | refl | refl | refl = refl

data ActionTwoCellCalculusIsBicategory : Set where
data ActionTwoCellCalculusIsStrictTwoGroupoid : Set where

actionTwoCellsDoNotAutoPromoteToBicategory :
  ActionTwoCellCalculusIsBicategory → ⊥
actionTwoCellsDoNotAutoPromoteToBicategory ()

actionTwoCellsDoNotAutoPromoteToStrictTwoGroupoid :
  ActionTwoCellCalculusIsStrictTwoGroupoid → ⊥
actionTwoCellsDoNotAutoPromoteToStrictTwoGroupoid ()

record RelationalTransportActionTwoCellBoundary : Set where
  constructor relational-transport-action-two-cell-boundary
  field
    parallelActionTwoCellsConstructed : Bool
    identityTwoCellConstructed : Bool
    reverseTwoCellConstructed : Bool
    verticalCompositionConstructed : Bool
    leftWhiskeringConstructed : Bool
    rightWhiskeringConstructed : Bool
    verticalIdentityLawsProved : Bool
    verticalAssociativityProved : Bool
    bicategoryClaimed : Bool
    strictTwoGroupoidClaimed : Bool

canonicalRelationalTransportActionTwoCellBoundary :
  RelationalTransportActionTwoCellBoundary
canonicalRelationalTransportActionTwoCellBoundary =
  relational-transport-action-two-cell-boundary
    true true true true true true true true false false
