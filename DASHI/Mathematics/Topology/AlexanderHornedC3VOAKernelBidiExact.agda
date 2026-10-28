module DASHI.Mathematics.Topology.AlexanderHornedC3VOAKernelBidiExact where

------------------------------------------------------------------------
-- NONABELIAN FINITE-QUOTIENT VOA ACTION: INFORMATION LOST.
--
-- Reuses exact consumer non-descent infrastructure already in DASHI.
-- For a selected actor quotient G -> Q and two distinct G elements
-- that Q identifies, no consumer demanding recovery of the full G
-- element can factor through Q. If Q acts faithfully on the selected
-- VOA, the same information gap holds for observing the FULL VOA
-- AUTOMORPHISM (not only a chosen expectation value).
--
-- Intended concrete instance: G is the abstract 3-root Hatcher group,
-- Q=A5^3 (or semidirect A5^3 ⋊ C3), and the pair is
--    m^5 vs e,     m^5 != e in G,     q(m^5)=q(e).
-- Those concrete source-group and finite A5 quotient instances are
-- not manufactured by declaring this conditional bridge.
--
-- Source/attribution: FormalClaimTransportGeometryExact and
-- ConsumerDescentMinimalObserverExact own the BIDI theorem;
-- Hatcher owns the free-group injection needed for m^5 != e.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

record NonfaithfulVOAGroupActor : Set₁ where
  field
    SourceGroup : Set
    FiniteActor : Set
    identitySource : SourceGroup
    essentialKernelWord : SourceGroup
    actorOf : SourceGroup → FiniteActor
    kernelWordInvisible :
      actorOf essentialKernelWord ≡ actorOf identitySource
    kernelWordNontrivial :
      essentialKernelWord ≡ identitySource → ⊥

open NonfaithfulVOAGroupActor public

kernelWordBlocksFullSourceRecovery :
  (source : NonfaithfulVOAGroupActor) →
  Transport.ClaimNonTransportWitness
    (actorOf source) (λ x → x)
kernelWordBlocksFullSourceRecovery source =
  Descent.consumerNonDescentWitness
    (essentialKernelWord source)
    (identitySource source)
    (kernelWordInvisible source)
    (kernelWordNontrivial source)

cannotRecoverExteriorGroupFromSelectedVOAActor :
  (source : NonfaithfulVOAGroupActor) →
  Transport.ClaimTransport
    (actorOf source) (λ x → x) → ⊥
cannotRecoverExteriorGroupFromSelectedVOAActor source =
  Transport.claimNonTransportWitnessBlocksTransport
    (kernelWordBlocksFullSourceRecovery source)

-- Any observable computed from the finite actor is also blind to
-- the same kernel pair, including matrix coefficients, grade
-- characters and all state actions of that quotient.
kernelWordInvisibleToEveryActorObservation :
  (source : NonfaithfulVOAGroupActor) →
  {Observed : Set} →
  (observe : FiniteActor source → Observed) →
  observe (actorOf source (essentialKernelWord source))
    ≡ observe (actorOf source (identitySource source))
kernelWordInvisibleToEveryActorObservation source observe =
  cong observe (kernelWordInvisible source)
