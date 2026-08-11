module DASHI.Physics.Closure.NSTriadKNComCrossChannelRoundTripRound39Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Proceedings of the Symposium on Ergodic Theory, 1955.
-- DOI: no DOI assigned to the cited historical conference article.
--
-- DASHI CONTRIBUTION
--
-- Round 37/38 proved that Com is entirely the two cross channels.  Write
--
--   U = PTQ  (fine -> coarse),
--   V = QTP  (coarse -> fine).
--
-- This module proves the extra structure suggested by that reduction:
--
--   U^2 = 0,
--   V^2 = 0,
--   T_odd^2 = UV + VU.
--
-- The two surviving second-order terms are diagonal round trips:
--
--   P -> Q -> P,   Q -> P -> Q.
--
-- Both carry the same scalar product b*c on the exact two-channel carrier.
-- This is the sharp algebraic target for the remaining physical Gram/Cotlar
-- realization: pair products should be identified with cross-fibre round-trip
-- overlaps, not arbitrary full-space products.
--
-- The Round-37 channel involution J swaps U and V after conjugating T.  If a
-- literal physical transport is J-equivariant, one cross-channel coefficient
-- determines the other.  The physical equivariance/Gram identification is
-- deliberately left as an explicit producer rather than assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≡_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNComPQCrossChannelRound37Exact as PQ
import DASHI.Physics.Closure.NSTriadKNComPQInvolutionRound37Exact as J
import DASHI.Physics.Closure.NSTriadKNComZ2GradingRound38Exact as Grading

composeTransport : PQ.LinearTransport2 → PQ.LinearTransport2 → PQ.LinearTransport2
composeTransport left right =
  PQ.linear-transport2
    (PQ.coarseToCoarse left * PQ.coarseToCoarse right
      + PQ.fineToCoarse left * PQ.coarseToFine right)
    (PQ.coarseToCoarse left * PQ.fineToCoarse right
      + PQ.fineToCoarse left * PQ.fineToFine right)
    (PQ.coarseToFine left * PQ.coarseToCoarse right
      + PQ.fineToFine left * PQ.coarseToFine right)
    (PQ.coarseToFine left * PQ.fineToCoarse right
      + PQ.fineToFine left * PQ.fineToFine right)

composeTransportMeaning : ∀ left right state →
  PQ.applyTransport (composeTransport left right) state
  ≡ PQ.applyTransport left (PQ.applyTransport right state)
composeTransportMeaning left right (PQ.split-state x y) =
  PQ.stateExt
    (solve
      ( PQ.coarseToCoarse left
      ∷ PQ.fineToCoarse left
      ∷ PQ.coarseToFine left
      ∷ PQ.fineToFine left
      ∷ PQ.coarseToCoarse right
      ∷ PQ.fineToCoarse right
      ∷ PQ.coarseToFine right
      ∷ PQ.fineToFine right
      ∷ x ∷ y ∷ []))
    (solve
      ( PQ.coarseToCoarse left
      ∷ PQ.fineToCoarse left
      ∷ PQ.coarseToFine left
      ∷ PQ.fineToFine left
      ∷ PQ.coarseToCoarse right
      ∷ PQ.fineToCoarse right
      ∷ PQ.coarseToFine right
      ∷ PQ.fineToFine right
      ∷ x ∷ y ∷ []))

upperCrossChannel lowerCrossChannel : PQ.LinearTransport2 → PQ.LinearTransport2
upperCrossChannel transport =
  PQ.linear-transport2 0ℚ (PQ.fineToCoarse transport) 0ℚ 0ℚ
lowerCrossChannel transport =
  PQ.linear-transport2 0ℚ 0ℚ (PQ.coarseToFine transport) 0ℚ

upperCrossChannelAction : ∀ transport state →
  PQ.applyTransport (upperCrossChannel transport) state
  ≡ PQ.fineToCoarseChannel transport state
upperCrossChannelAction transport (PQ.split-state x y) =
  PQ.stateExt
    (solve (PQ.fineToCoarse transport ∷ y ∷ []))
    refl

lowerCrossChannelAction : ∀ transport state →
  PQ.applyTransport (lowerCrossChannel transport) state
  ≡ PQ.coarseToFineChannel transport state
lowerCrossChannelAction transport (PQ.split-state x y) =
  PQ.stateExt
    refl
    (solve (PQ.coarseToFine transport ∷ x ∷ []))

upperCrossChannelNilpotent : ∀ transport →
  composeTransport
    (upperCrossChannel transport)
    (upperCrossChannel transport)
  ≡ PQ.linear-transport2 0ℚ 0ℚ 0ℚ 0ℚ
upperCrossChannelNilpotent transport =
  Grading.transportExt
    (solve (PQ.fineToCoarse transport ∷ []))
    (solve (PQ.fineToCoarse transport ∷ []))
    (solve (PQ.fineToCoarse transport ∷ []))
    (solve (PQ.fineToCoarse transport ∷ []))

lowerCrossChannelNilpotent : ∀ transport →
  composeTransport
    (lowerCrossChannel transport)
    (lowerCrossChannel transport)
  ≡ PQ.linear-transport2 0ℚ 0ℚ 0ℚ 0ℚ
lowerCrossChannelNilpotent transport =
  Grading.transportExt
    (solve (PQ.coarseToFine transport ∷ []))
    (solve (PQ.coarseToFine transport ∷ []))
    (solve (PQ.coarseToFine transport ∷ []))
    (solve (PQ.coarseToFine transport ∷ []))

upperAfterLower : PQ.LinearTransport2 → PQ.LinearTransport2
upperAfterLower transport =
  composeTransport
    (upperCrossChannel transport)
    (lowerCrossChannel transport)

lowerAfterUpper : PQ.LinearTransport2 → PQ.LinearTransport2
lowerAfterUpper transport =
  composeTransport
    (lowerCrossChannel transport)
    (upperCrossChannel transport)

upperAfterLowerIsCoarseRoundTrip : ∀ transport →
  upperAfterLower transport
  ≡ PQ.linear-transport2
      (PQ.fineToCoarse transport * PQ.coarseToFine transport)
      0ℚ 0ℚ 0ℚ
upperAfterLowerIsCoarseRoundTrip transport =
  Grading.transportExt
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))

lowerAfterUpperIsFineRoundTrip : ∀ transport →
  lowerAfterUpper transport
  ≡ PQ.linear-transport2
      0ℚ 0ℚ 0ℚ
      (PQ.coarseToFine transport * PQ.fineToCoarse transport)
lowerAfterUpperIsFineRoundTrip transport =
  Grading.transportExt
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))

oddSquareIsCrossFibreRoundTrips : ∀ transport →
  composeTransport
    (Grading.oddTransport transport)
    (Grading.oddTransport transport)
  ≡
  Grading.transportAdd
    (upperAfterLower transport)
    (lowerAfterUpper transport)
oddSquareIsCrossFibreRoundTrips transport =
  Grading.transportExt
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))

roundTripCoefficient : PQ.LinearTransport2 → ℚ
roundTripCoefficient transport =
  PQ.fineToCoarse transport * PQ.coarseToFine transport

coarseFineRoundTripsHaveSameCoefficient : ∀ transport →
  PQ.coarseToCoarse (upperAfterLower transport)
  ≡ PQ.fineToFine (lowerAfterUpper transport)
coarseFineRoundTripsHaveSameCoefficient transport =
  solve
    (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ [])

involutionSwapsUpperToLower : ∀ transport →
  J.conjugateTransportByInvolution (upperCrossChannel transport)
  ≡ lowerCrossChannel (J.conjugateTransportByInvolution transport)
involutionSwapsUpperToLower transport =
  Grading.transportExt refl refl refl refl

involutionSwapsLowerToUpper : ∀ transport →
  J.conjugateTransportByInvolution (lowerCrossChannel transport)
  ≡ upperCrossChannel (J.conjugateTransportByInvolution transport)
involutionSwapsLowerToUpper transport =
  Grading.transportExt refl refl refl refl

record JEquivariantTransport (transport : PQ.LinearTransport2) : Set where
  field
    invariantUnderChannelInvolution :
      J.conjugateTransportByInvolution transport ≡ transport

open JEquivariantTransport public

jEquivarianceForcesCrossChannelEquality :
  ∀ {transport} →
  JEquivariantTransport transport →
  PQ.fineToCoarse transport ≡ PQ.coarseToFine transport
jEquivarianceForcesCrossChannelEquality {transport} witness =
  cong PQ.fineToCoarse (invariantUnderChannelInvolution witness)

comCrossChannelRoundTripAlgebraClosed : Bool
comCrossChannelRoundTripAlgebraClosed = true

physicalComRoundTripGramRealizationConstructed : Bool
physicalComRoundTripGramRealizationConstructed = false

physicalComJEquivarianceConstructed : Bool
physicalComJEquivarianceConstructed = false

comCrossChannelRoundTripAlgebraClosedIsTrue :
  comCrossChannelRoundTripAlgebraClosed ≡ true
comCrossChannelRoundTripAlgebraClosedIsTrue = refl
