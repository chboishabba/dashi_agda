{-# OPTIONS --safe #-}
module DASHI.Reasoning.FederatedTieredMoEFiniteExact where

-- A finite, source-independent federation witness. Actual WAN, cryptography,
-- PyTorch, dtype/quantisation and kernel correctness are NOT established.
-- Reuse the PR #1442 full joint-state quotient / signed-history wire owners
-- for actual selected execution; here we isolate placement admission.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

data Peer : Set where
  localPeer remotePeer : Peer

data Revision : Set where
  old new : Revision

data Expert : Set where
  expert0 expert1 : Expert

data Result (A : Set) : Set where
  reject : Result A
  accept : A → Result A

route : Bool → Expert
route false = expert0
route true  = expert1

owner : Expert → Peer
owner expert0 = localPeer
owner expert1 = remotePeer

weight : Revision → Expert → Nat
weight old expert0 = 3
weight old expert1 = 5
weight new expert0 = 4
weight new expert1 = 6

-- A cache or remote peer must report an exact model AND history revision.
-- Admission is explicit, not inferred from a digest or expert ID.
admit : Bool → Bool → Nat → Result Nat
admit false _ _ = reject
admit true false _ = reject
admit true true output = accept output

selected : Revision → Bool → Nat
selected revision input = weight revision (route input)

-- The source-side reference may evaluate locally or ask an owner.
-- On exact model+history matches, a placement change has no effect on
-- the value returned, because it calls the SAME selected expert.
execute : Peer → Revision → Bool → Bool → Bool → Result Nat
execute peer revision input modelOK historyOK =
  admit modelOK historyOK (selected revision input)

localRemoteAgrees :
  (revision : Revision) (input : Bool) →
  execute localPeer revision input true true ≡
  execute remotePeer revision input true true
localRemoteAgrees revision input = refl

admittedFederatedEqualsReference :
  (peer : Peer) (revision : Revision) (input : Bool) →
  execute peer revision input true true ≡
  accept (selected revision input)
admittedFederatedEqualsReference peer revision input = refl

staleModelRejected :
  (peer : Peer) (revision : Revision) (input : Bool) →
  execute peer revision input false true ≡ reject
staleModelRejected peer revision input = refl

staleHistoryRejected :
  (peer : Peer) (revision : Revision) (input : Bool) →
  execute peer revision input true false ≡ reject
staleHistoryRejected peer revision input = refl

-- An exact expert identifier with a stale revision changes the result.
staleExpertValueCannotPassForNew :
  weight old expert0 ≡ weight new expert0 → 
  false ≡ true
staleExpertValueCannotPassForNew ()

-- A routing change may change the required peer; this is relevant to
-- Sophontic interventions applied BEFORE the router.
flip : Bool → Bool
flip false = true
flip true = false

preRouterSteeringMovesSelectedExpert :
  route (flip false) ≡ expert1
preRouterSteeringMovesSelectedExpert = refl

preRouterSteeringMovesOwner :
  owner (route (flip false)) ≡ remotePeer
preRouterSteeringMovesOwner = refl

-- The apparent source/remote equivalence above assumes a total oracle
-- giving exact weights for every peer. Thus it is a finite admission
-- contract, NOT a proof of physical storage, reachability or transport.
