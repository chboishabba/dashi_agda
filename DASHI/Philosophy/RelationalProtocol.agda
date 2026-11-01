module DASHI.Philosophy.RelationalProtocol where

open import Agda.Primitive using (Set₁)

------------------------------------------------------------------------
-- Tlurey is a trust-indexed relation, not a universal dialectical engine.

record TlureyWitness (A B : Set) : Set₁ where
  field
    relates :
      A →
      B →
      Set

    trust :
      Set

    care :
      Set

    sharedHistory :
      Set

    permissionToChallenge :
      Set

    commitmentToRepair :
      Set

    nonInstrumentalRecognition :
      Set

open TlureyWitness public

------------------------------------------------------------------------
-- Respect -> Connect -> Reflect -> Direct.
--
-- Each stage carries the previous witness.  Direct action is therefore only
-- constructible from a reflected relation.

record Respected (S : Set) : Set₁ where
  constructor respected
  field
    state :
      S

    respectWitness :
      Set

open Respected public

record Connected (S : Set) : Set₁ where
  constructor connected
  field
    respectedState :
      Respected S

    connectionWitness :
      Set

open Connected public

record Reflected (S : Set) : Set₁ where
  constructor reflected
  field
    connectedState :
      Connected S

    reflectionWitness :
      Set

open Reflected public

record DirectedAction (S Action : Set) : Set₁ where
  constructor directedAction
  field
    reflectedState :
      Reflected S

    action :
      Action

    actionBoundary :
      Set

open DirectedAction public

direct :
  ∀ {S Action : Set} →
  Reflected S →
  Action →
  Set →
  DirectedAction S Action
direct r a boundary =
  directedAction r a boundary
