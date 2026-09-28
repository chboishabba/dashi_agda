module DASHI.Reasoning.Trialectic369DyadicC3LocalComplementSymmetryExact where

------------------------------------------------------------------------
-- PARTICIPANT C3 SYMMETRY OF THE DYADIC T4 x T5 FACTORIZATIONS
--
-- DASHI CONTRIBUTION
--
-- Relabel participants cyclically by
--
--   new A = old B
--   new B = old C
--   new C = old A.
--
-- This gives an exact order-three action on ObserverMatrix3 and cycles the
-- three dyadic locals:
--
--   U_AB(rho M)   = U_BC(M)
--   U_AB(rho^2 M) = U_CA(M).
--
-- Hence the AB T4 x T5 factorization is only a chosen chart representative;
-- BC and CA are exact C3-conjugate decompositions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.Trialectic369DescentNaturalityExact as Descent
import DASHI.Reasoning.Trialectic369DyadicLocalComplementFactorizationExact as Factor

------------------------------------------------------------------------
-- 1. Exact participant C3 action on observer matrices.
------------------------------------------------------------------------

rotateABC :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Observer.ObserverMatrix3 SSP.SSPTrit
rotateABC matrix =
  Observer.observerMatrix3
    (Observer.bB matrix)
    (Observer.bC matrix)
    (Observer.bA matrix)

    (Observer.cB matrix)
    (Observer.cC matrix)
    (Observer.cA matrix)

    (Observer.aB matrix)
    (Observer.aC matrix)
    (Observer.aA matrix)

rotateABCTwice :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Observer.ObserverMatrix3 SSP.SSPTrit
rotateABCTwice matrix =
  rotateABC (rotateABC matrix)

rotateABCThreeTimes :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  rotateABC (rotateABC (rotateABC matrix)) ≡ matrix
rotateABCThreeTimes
  (Observer.observerMatrix3
    aa ab ac
    ba bb bc
    ca cb cc) = refl

------------------------------------------------------------------------
-- 2. Local-section retyping under the C3 action.
------------------------------------------------------------------------

bcAsAB : Descent.BCSection -> Descent.ABSection
bcAsAB (Descent.bc-section bb bc cb cc) =
  Descent.ab-section bb bc cb cc

caAsAB : Descent.CASection -> Descent.ABSection
caAsAB (Descent.ca-section cc ca ac aa) =
  Descent.ab-section cc ca ac aa

abAsBC : Descent.ABSection -> Descent.BCSection
abAsBC (Descent.ab-section aa ab ba bb) =
  Descent.bc-section aa ab ba bb

bcAsCA : Descent.BCSection -> Descent.CASection
bcAsCA (Descent.bc-section bb bc cb cc) =
  Descent.ca-section bb bc cb cc

caAsBC : Descent.CASection -> Descent.BCSection
caAsBC (Descent.ca-section cc ca ac aa) =
  Descent.bc-section cc ca ac aa

abAsCA : Descent.ABSection -> Descent.CASection
abAsCA (Descent.ab-section aa ab ba bb) =
  Descent.ca-section aa ab ba bb

abRestrictionAfterRotateIsBC :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Descent.restrictAB (rotateABC matrix)
  ≡ bcAsAB (Descent.restrictBC matrix)
abRestrictionAfterRotateIsBC matrix = refl

abRestrictionAfterRotateTwiceIsCA :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Descent.restrictAB (rotateABCTwice matrix)
  ≡ caAsAB (Descent.restrictCA matrix)
abRestrictionAfterRotateTwiceIsCA matrix = refl

bcRestrictionAfterRotateIsCA :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Descent.restrictBC (rotateABC matrix)
  ≡ caAsBC (Descent.restrictCA matrix)
bcRestrictionAfterRotateIsCA matrix = refl

caRestrictionAfterRotateIsAB :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Descent.restrictCA (rotateABC matrix)
  ≡ abAsCA (Descent.restrictAB matrix)
caRestrictionAfterRotateIsAB matrix = refl

------------------------------------------------------------------------
-- 3. Explicit BC / CA complements.
------------------------------------------------------------------------

record BCComplement5 : Set where
  constructor bc-complement5
  field
    ba : SSP.SSPTrit
    ca : SSP.SSPTrit
    aa : SSP.SSPTrit
    ab : SSP.SSPTrit
    ac : SSP.SSPTrit

open BCComplement5 public

observerBCComplement :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  BCComplement5
observerBCComplement matrix =
  bc-complement5
    (Observer.bA matrix)
    (Observer.cA matrix)
    (Observer.aA matrix)
    (Observer.aB matrix)
    (Observer.aC matrix)

record CAComplement5 : Set where
  constructor ca-complement5
  field
    cb : SSP.SSPTrit
    ab : SSP.SSPTrit
    bb : SSP.SSPTrit
    bc : SSP.SSPTrit
    ba : SSP.SSPTrit

open CAComplement5 public

observerCAComplement :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  CAComplement5
observerCAComplement matrix =
  ca-complement5
    (Observer.cB matrix)
    (Observer.aB matrix)
    (Observer.bB matrix)
    (Observer.bC matrix)
    (Observer.bA matrix)

------------------------------------------------------------------------
-- 4. C3 identifies the complements as well.
------------------------------------------------------------------------

bcComplementAsABComplement :
  BCComplement5 -> Factor.ABComplement5
bcComplementAsABComplement
  (bc-complement5 ba ca aa ab ac) =
  Factor.ab-complement5
    ba ca aa ab ac

caComplementAsABComplement :
  CAComplement5 -> Factor.ABComplement5
caComplementAsABComplement
  (ca-complement5 cb ab bb bc ba) =
  Factor.ab-complement5
    cb ab bb bc ba

abComplementAfterRotateIsBCComplement :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Factor.observerABComplement (rotateABC matrix)
  ≡ bcComplementAsABComplement (observerBCComplement matrix)
abComplementAfterRotateIsBCComplement matrix = refl

abComplementAfterRotateTwiceIsCAComplement :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Factor.observerABComplement (rotateABCTwice matrix)
  ≡ caComplementAsABComplement (observerCAComplement matrix)
abComplementAfterRotateTwiceIsCAComplement matrix = refl

------------------------------------------------------------------------
-- 5. Firewall.
------------------------------------------------------------------------

data ParticipantC3IsSameAsSquareD4Rotation : Set where
data C3ChartOrbitCreatesIntrinsicPreferredLocal : Set where
data C3SymmetryCreatesEmpiricalMeaning : Set where

participantC3NotIdentifiedWithSquareD4Rotation :
  ParticipantC3IsSameAsSquareD4Rotation -> ⊥
participantC3NotIdentifiedWithSquareD4Rotation ()

c3OrbitDoesNotCreatePreferredChart :
  C3ChartOrbitCreatesIntrinsicPreferredLocal -> ⊥
c3OrbitDoesNotCreatePreferredChart ()

c3SymmetryDoesNotCreateEmpiricalMeaning :
  C3SymmetryCreatesEmpiricalMeaning -> ⊥
c3SymmetryDoesNotCreateEmpiricalMeaning ()

record Trialectic369DyadicC3LocalComplementSymmetryBoundary : Set where
  constructor trialectic-369-dyadic-c3-local-complement-symmetry-boundary
  field
    participantC3ActionOwned : Bool
    participantC3OrderThree : Bool
    abCyclesToBC : Bool
    abCyclesTwiceToCA : Bool
    complementsCycleWithLocals : Bool
    allThreeT4xT5ChartsConjugate : Bool
    squareD4IdentifiedWithParticipantC3 : Bool
    preferredDyadicChartClaimed : Bool

canonicalTrialectic369DyadicC3LocalComplementSymmetryBoundary :
  Trialectic369DyadicC3LocalComplementSymmetryBoundary
canonicalTrialectic369DyadicC3LocalComplementSymmetryBoundary =
  trialectic-369-dyadic-c3-local-complement-symmetry-boundary
    true true true true true true false false
