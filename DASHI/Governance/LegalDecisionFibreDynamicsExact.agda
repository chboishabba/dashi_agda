module DASHI.Governance.LegalDecisionFibreDynamicsExact where

------------------------------------------------------------------------
-- HIDDEN LEGAL-DECISION DYNAMICS AT FIXED OFFICIAL SURFACE
--
-- The double-projection theorem gives static collisions.  This module turns
-- those collisions into exact fibre-preserving dynamics using the already-
-- merged generic `FibrePreservingDynamicsExact` owner.
--
-- Three witness states share one official surface:
--   * blocked commitment + donor relation;
--   * unresolved inaction + donor relation;
--   * blocked commitment + adoptive relation.
--
-- One involution moves only the decision-history coordinate; another moves
-- only the authority-route coordinate.  Both remain invisible at the official
-- surface.  The two hidden motions do not commute, so update order can matter
-- even while every intermediate state projects to the same official result.
--
-- This is a finite structural witness.  It is not a claim that any real legal
-- process literally has these three states or these exact dynamics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.FibreOrderNonfactorabilityExact as Order
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Governance.LegalDecisionDoubleProjectionExact as Legal

------------------------------------------------------------------------
-- 1. A finite witness subcarrier inside one official legal fibre.
------------------------------------------------------------------------

data LegalFibreWitnessState : Set where
  blockedDonorState unresolvedDonorState blockedAdoptiveState : LegalFibreWitnessState

toLegalEpisode : LegalFibreWitnessState → Legal.LegalDecisionEpisode
toLegalEpisode blockedDonorState = Legal.blockedDonor
toLegalEpisode unresolvedDonorState = Legal.unresolvedDonor
toLegalEpisode blockedAdoptiveState = Legal.blockedAdoptive

witnessOfficialSurface : LegalFibreWitnessState → Legal.OfficialSurface
witnessOfficialSurface state = Legal.officialSurface (toLegalEpisode state)

allWitnessStatesShareOfficialSurface :
  (state : LegalFibreWitnessState) →
  witnessOfficialSurface state ≡ witnessOfficialSurface blockedDonorState
allWitnessStatesShareOfficialSurface blockedDonorState = refl
allWitnessStatesShareOfficialSurface unresolvedDonorState = refl
allWitnessStatesShareOfficialSurface blockedAdoptiveState = refl

record LegalOfficialFibre (surface : Legal.OfficialSurface) : Set where
  constructor legalOfficialFibre
  field
    witnessState : LegalFibreWitnessState
    liesOver : witnessOfficialSurface witnessState ≡ surface

open LegalOfficialFibre public

legalDecisionFibreCore : Fibre.FibreRestrictionCore
legalDecisionFibreCore =
  Fibre.fibreRestrictionCore
    LegalFibreWitnessState
    Legal.OfficialSurface
    ⊤
    witnessOfficialSurface
    LegalOfficialFibre
    (λ _ surface → LegalOfficialFibre surface)
    true
    false

------------------------------------------------------------------------
-- 2. Hidden decision-history involution.
------------------------------------------------------------------------

decisionMotion : LegalFibreWitnessState → LegalFibreWitnessState
decisionMotion blockedDonorState = unresolvedDonorState
decisionMotion unresolvedDonorState = blockedDonorState
decisionMotion blockedAdoptiveState = blockedAdoptiveState

decisionMotionPreservesOfficialSurface :
  Dynamics.SurfaceInvariant legalDecisionFibreCore decisionMotion
decisionMotionPreservesOfficialSurface blockedDonorState = refl
decisionMotionPreservesOfficialSurface unresolvedDonorState = refl
decisionMotionPreservesOfficialSurface blockedAdoptiveState = refl

decisionMotionInvolutive :
  (state : LegalFibreWitnessState) →
  decisionMotion (decisionMotion state) ≡ state
decisionMotionInvolutive blockedDonorState = refl
decisionMotionInvolutive unresolvedDonorState = refl
decisionMotionInvolutive blockedAdoptiveState = refl

decisionFibreAutomorphism : Dynamics.FibreAutomorphism legalDecisionFibreCore
decisionFibreAutomorphism =
  Dynamics.fibreAutomorphism
    decisionMotion
    decisionMotion
    decisionMotionPreservesOfficialSurface
    decisionMotionPreservesOfficialSurface
    decisionMotionInvolutive
    decisionMotionInvolutive

decisionMotionActuallyMovesBlockedDonor :
  decisionMotion blockedDonorState ≡ blockedDonorState → ⊥
decisionMotionActuallyMovesBlockedDonor ()

decisionNontrivialFibreAutomorphism :
  Dynamics.NontrivialFibreAutomorphism legalDecisionFibreCore
decisionNontrivialFibreAutomorphism =
  Dynamics.nontrivialFibreAutomorphism
    decisionFibreAutomorphism
    blockedDonorState
    decisionMotionActuallyMovesBlockedDonor

decisionHiddenTransition :
  Dynamics.HiddenTransition legalDecisionFibreCore decisionMotion blockedDonorState
decisionHiddenTransition =
  Dynamics.nontrivialFibreAutomorphismCreatesHiddenTransition
    decisionNontrivialFibreAutomorphism

------------------------------------------------------------------------
-- 3. Hidden authority-route involution.
------------------------------------------------------------------------

authorityMotion : LegalFibreWitnessState → LegalFibreWitnessState
authorityMotion blockedDonorState = blockedAdoptiveState
authorityMotion unresolvedDonorState = unresolvedDonorState
authorityMotion blockedAdoptiveState = blockedDonorState

authorityMotionPreservesOfficialSurface :
  Dynamics.SurfaceInvariant legalDecisionFibreCore authorityMotion
authorityMotionPreservesOfficialSurface blockedDonorState = refl
authorityMotionPreservesOfficialSurface unresolvedDonorState = refl
authorityMotionPreservesOfficialSurface blockedAdoptiveState = refl

authorityMotionInvolutive :
  (state : LegalFibreWitnessState) →
  authorityMotion (authorityMotion state) ≡ state
authorityMotionInvolutive blockedDonorState = refl
authorityMotionInvolutive unresolvedDonorState = refl
authorityMotionInvolutive blockedAdoptiveState = refl

authorityFibreAutomorphism : Dynamics.FibreAutomorphism legalDecisionFibreCore
authorityFibreAutomorphism =
  Dynamics.fibreAutomorphism
    authorityMotion
    authorityMotion
    authorityMotionPreservesOfficialSurface
    authorityMotionPreservesOfficialSurface
    authorityMotionInvolutive
    authorityMotionInvolutive

authorityMotionActuallyMovesBlockedDonor :
  authorityMotion blockedDonorState ≡ blockedDonorState → ⊥
authorityMotionActuallyMovesBlockedDonor ()

authorityNontrivialFibreAutomorphism :
  Dynamics.NontrivialFibreAutomorphism legalDecisionFibreCore
authorityNontrivialFibreAutomorphism =
  Dynamics.nontrivialFibreAutomorphism
    authorityFibreAutomorphism
    blockedDonorState
    authorityMotionActuallyMovesBlockedDonor

authorityHiddenTransition :
  Dynamics.HiddenTransition legalDecisionFibreCore authorityMotion blockedDonorState
authorityHiddenTransition =
  Dynamics.nontrivialFibreAutomorphismCreatesHiddenTransition
    authorityNontrivialFibreAutomorphism

------------------------------------------------------------------------
-- 4. The two hidden motions are noncommutative.
------------------------------------------------------------------------

decisionAfterAuthorityAtBlocked : LegalFibreWitnessState
decisionAfterAuthorityAtBlocked =
  decisionMotion (authorityMotion blockedDonorState)

authorityAfterDecisionAtBlocked : LegalFibreWitnessState
authorityAfterDecisionAtBlocked =
  authorityMotion (decisionMotion blockedDonorState)

decisionAfterAuthorityIsAdoptive :
  decisionAfterAuthorityAtBlocked ≡ blockedAdoptiveState
decisionAfterAuthorityIsAdoptive = refl

authorityAfterDecisionIsUnresolved :
  authorityAfterDecisionAtBlocked ≡ unresolvedDonorState
authorityAfterDecisionIsUnresolved = refl

hiddenMotionsDoNotCommuteAtBlocked :
  decisionAfterAuthorityAtBlocked ≡ authorityAfterDecisionAtBlocked → ⊥
hiddenMotionsDoNotCommuteAtBlocked ()

bothCompositeOrdersRemainOfficiallyInvisible :
  witnessOfficialSurface decisionAfterAuthorityAtBlocked
  ≡ witnessOfficialSurface authorityAfterDecisionAtBlocked
bothCompositeOrdersRemainOfficiallyInvisible = refl

------------------------------------------------------------------------
-- 5. Generic order non-factorability instantiated on the legal fibre.
------------------------------------------------------------------------

legalHiddenOrderNonfactorability :
  NF.NonFactorabilityWitness
    (Order.orderedSurface decisionMotion authorityMotion blockedDonorState)
    (Order.orderedEndpoint decisionMotion authorityMotion blockedDonorState)
legalHiddenOrderNonfactorability =
  Order.automorphismOrderNonfactorability
    decisionFibreAutomorphism
    authorityFibreAutomorphism
    blockedDonorState
    hiddenMotionsDoNotCommuteAtBlocked

officialSurfaceCannotDecodeHiddenUpdateOrder :
  NF.FactorsThrough
    (Order.orderedSurface decisionMotion authorityMotion blockedDonorState)
    (Order.orderedEndpoint decisionMotion authorityMotion blockedDonorState) →
  ⊥
officialSurfaceCannotDecodeHiddenUpdateOrder =
  NF.witnessRulesOutEveryFlatFactorisation
    legalHiddenOrderNonfactorability

------------------------------------------------------------------------
-- 6. Consequences: official projection is noninjective and hidden update order
-- cannot be reconstructed from the official endpoint.
------------------------------------------------------------------------

officialProjectionNoninjectiveFromDecisionMotion :
  ((left right : LegalFibreWitnessState) →
    witnessOfficialSurface left ≡ witnessOfficialSurface right →
    left ≡ right) →
  ⊥
officialProjectionNoninjectiveFromDecisionMotion =
  Dynamics.nontrivialFibreAutomorphismBlocksProjectionInjectivity
    decisionNontrivialFibreAutomorphism

officialProjectionNoninjectiveFromAuthorityMotion :
  ((left right : LegalFibreWitnessState) →
    witnessOfficialSurface left ≡ witnessOfficialSurface right →
    left ≡ right) →
  ⊥
officialProjectionNoninjectiveFromAuthorityMotion =
  Dynamics.nontrivialFibreAutomorphismBlocksProjectionInjectivity
    authorityNontrivialFibreAutomorphism

record LegalDecisionFibreDynamicsBoundary : Set where
  constructor legalDecisionFibreDynamicsBoundary
  field
    decisionStateCanMoveAtFixedOfficialSurface : Bool
    authorityRouteCanMoveAtFixedOfficialSurface : Bool
    hiddenDecisionAndAuthorityUpdatesMustCommute : Bool
    sameOfficialEndpointDeterminesHiddenUpdateOrder : Bool
    officialProjectionInjectiveOnWitnessFibre : Bool

canonicalLegalDecisionFibreDynamicsBoundary : LegalDecisionFibreDynamicsBoundary
canonicalLegalDecisionFibreDynamicsBoundary =
  legalDecisionFibreDynamicsBoundary true true false false false
