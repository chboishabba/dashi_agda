module DASHI.Physics.Closure.NSTriadKNComAdjointCollapseRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Test the stronger post-Round-39 Com reduction suggested by incompressible
-- transport.  On the exact two-channel carrier, the standard Euclidean
-- pairing has:
--
--   P* = P, Q* = Q,
--   T* = transpose(T).
--
-- If the physical transport is skew-adjoint, T* = -T, then for
--
--   U = PTQ, V = QTP
--
-- the cross channels satisfy
--
--   V = - U*.
--
-- Consequently
--
--   [P,T] = U - V = U + U*
--
-- is self-adjoint and its square has the two identical Gram faces b^2 on the
-- coarse/fine blocks.  Thus one cross-channel Gram estimate determines both
-- sides; the optional Round-39 J-equivariance is not needed for this collapse.
--
-- The module also proves the Z2 anti-commutation audit invariant
--
--   Gamma T_odd = - T_odd Gamma.
--
-- The repository's official finite hard projector is already self-adjoint by
-- the finite Hermitian/Parseval theorem; that physical fact is reused here.
-- The remaining physical input is the literal low-transport skew-adjoint
-- realization and its identification with the Round-35 Gram cells.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComPQCrossChannelRound37Exact as PQ
import DASHI.Physics.Closure.NSTriadKNComZ2GradingRound38Exact as Grading
import DASHI.Physics.Closure.NSTriadKNComCrossChannelRoundTripRound39Exact as Round39
import DASHI.Physics.Closure.NSTriadKNOfficialFiniteFourierHermitianParsevalExact as OfficialParseval

statePairing : PQ.SplitState → PQ.SplitState → ℚ
statePairing left right =
  PQ.coarse left * PQ.coarse right + PQ.detail left * PQ.detail right

transportTranspose : PQ.LinearTransport2 → PQ.LinearTransport2
transportTranspose transport =
  PQ.linear-transport2
    (PQ.coarseToCoarse transport)
    (PQ.coarseToFine transport)
    (PQ.fineToCoarse transport)
    (PQ.fineToFine transport)

transportNegate : PQ.LinearTransport2 → PQ.LinearTransport2
transportNegate transport =
  PQ.linear-transport2
    (- PQ.coarseToCoarse transport)
    (- PQ.fineToCoarse transport)
    (- PQ.coarseToFine transport)
    (- PQ.fineToFine transport)

transportTransposeIsAdjoint : ∀ transport left right →
  statePairing (PQ.applyTransport transport left) right
  ≡ statePairing left (PQ.applyTransport (transportTranspose transport) right)
transportTransposeIsAdjoint transport
    (PQ.split-state x y) (PQ.split-state u v) =
  solve
    ( PQ.coarseToCoarse transport
    ∷ PQ.fineToCoarse transport
    ∷ PQ.coarseToFine transport
    ∷ PQ.fineToFine transport
    ∷ x ∷ y ∷ u ∷ v ∷ [])

coarseProjectionSelfAdjoint : ∀ left right →
  statePairing (PQ.projectCoarse left) right
  ≡ statePairing left (PQ.projectCoarse right)
coarseProjectionSelfAdjoint (PQ.split-state x y) (PQ.split-state u v) =
  solve (x ∷ y ∷ u ∷ v ∷ [])

fineProjectionSelfAdjoint : ∀ left right →
  statePairing (PQ.projectFine left) right
  ≡ statePairing left (PQ.projectFine right)
fineProjectionSelfAdjoint (PQ.split-state x y) (PQ.split-state u v) =
  solve (x ∷ y ∷ u ∷ v ∷ [])

record SkewAdjointTransport2 (transport : PQ.LinearTransport2) : Set where
  constructor skew-adjoint-transport2
  field
    transposeIsNegative :
      transportTranspose transport ≡ transportNegate transport

open SkewAdjointTransport2 public

skewAdjointPairingIdentity :
  ∀ {transport} →
  SkewAdjointTransport2 transport →
  ∀ left right →
  statePairing (PQ.applyTransport transport left) right
  ≡ - statePairing left (PQ.applyTransport transport right)
skewAdjointPairingIdentity {transport} skew left right =
  trans
    (transportTransposeIsAdjoint transport left right)
    (trans
      (cong
        (statePairing left ∘ PQ.applyTransport)
        (transposeIsNegative skew))
      (solve
        ( PQ.coarseToCoarse transport
        ∷ PQ.fineToCoarse transport
        ∷ PQ.coarseToFine transport
        ∷ PQ.fineToFine transport
        ∷ PQ.coarse left ∷ PQ.detail left
        ∷ PQ.coarse right ∷ PQ.detail right
        ∷ [])))
  where
  _∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
  (f ∘ g) x = f (g x)

skewAdjointForcesCrossChannelsNegativeAdjoints :
  ∀ {transport} →
  SkewAdjointTransport2 transport →
  PQ.coarseToFine transport ≡ - PQ.fineToCoarse transport
skewAdjointForcesCrossChannelsNegativeAdjoints {transport} skew =
  cong PQ.fineToCoarse (transposeIsNegative skew)

upperChannelAdjoint : PQ.LinearTransport2 → PQ.LinearTransport2
upperChannelAdjoint transport =
  transportTranspose (Round39.upperCrossChannel transport)

negativeUpperChannelAdjoint : PQ.LinearTransport2 → PQ.LinearTransport2
negativeUpperChannelAdjoint transport =
  transportNegate (upperChannelAdjoint transport)

lowerChannelIsNegativeUpperAdjoint :
  ∀ {transport} →
  SkewAdjointTransport2 transport →
  Round39.lowerCrossChannel transport
  ≡ negativeUpperChannelAdjoint transport
lowerChannelIsNegativeUpperAdjoint {transport} skew =
  let cross = skewAdjointForcesCrossChannelsNegativeAdjoints skew
  in
  Grading.transportExt
    refl
    refl
    (sym cross)
    refl

commutatorTransport : PQ.LinearTransport2 → PQ.LinearTransport2
commutatorTransport transport =
  PQ.linear-transport2
    0ℚ
    (PQ.fineToCoarse transport)
    (- PQ.coarseToFine transport)
    0ℚ

commutatorTransportAction : ∀ transport state →
  PQ.applyTransport (commutatorTransport transport) state
  ≡ PQ.commutator transport state
commutatorTransportAction transport (PQ.split-state x y) =
  PQ.stateExt
    (solve
      ( PQ.coarseToCoarse transport
      ∷ PQ.fineToCoarse transport
      ∷ x ∷ y ∷ []))
    (solve
      ( PQ.coarseToFine transport
      ∷ PQ.fineToFine transport
      ∷ x ∷ []))

commutatorBecomesSymmetricOffDiagonal :
  ∀ {transport} →
  SkewAdjointTransport2 transport →
  commutatorTransport transport
  ≡ PQ.linear-transport2
      0ℚ
      (PQ.fineToCoarse transport)
      (PQ.fineToCoarse transport)
      0ℚ
commutatorBecomesSymmetricOffDiagonal {transport} skew =
  let cross = skewAdjointForcesCrossChannelsNegativeAdjoints skew
  in
  Grading.transportExt
    refl
    refl
    (trans
      (cong -_ cross)
      (solve (PQ.fineToCoarse transport ∷ [])))
    refl

commutatorTransportSelfAdjoint :
  ∀ {transport} →
  SkewAdjointTransport2 transport →
  transportTranspose (commutatorTransport transport)
  ≡ commutatorTransport transport
commutatorTransportSelfAdjoint {transport} skew =
  let symmetric = commutatorBecomesSymmetricOffDiagonal skew
  in
  trans
    (cong transportTranspose symmetric)
    (trans
      (Grading.transportExt refl refl refl refl)
      (sym symmetric))

commutatorSquareSingleGram :
  ∀ {transport} →
  SkewAdjointTransport2 transport →
  Round39.composeTransport
    (commutatorTransport transport)
    (commutatorTransport transport)
  ≡ PQ.linear-transport2
      (PQ.fineToCoarse transport * PQ.fineToCoarse transport)
      0ℚ 0ℚ
      (PQ.fineToCoarse transport * PQ.fineToCoarse transport)
commutatorSquareSingleGram {transport} skew =
  let cross = skewAdjointForcesCrossChannelsNegativeAdjoints skew
  in
  Grading.transportExt
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))
    (solve
      (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))
    (trans
      (solve
        (PQ.fineToCoarse transport ∷ PQ.coarseToFine transport ∷ []))
      refl)

------------------------------------------------------------------------
-- Z2 audit invariant: odd transport switches grade and nothing else.
------------------------------------------------------------------------

oddTransportAnticommutesWithGrading : ∀ transport state →
  Grading.grading
    (PQ.applyTransport (Grading.oddTransport transport) state)
  ≡
  Grading.stateScale (- 1ℚ)
    (PQ.applyTransport
      (Grading.oddTransport transport)
      (Grading.grading state))
oddTransportAnticommutesWithGrading
    transport (PQ.split-state x y) =
  PQ.stateExt
    (solve
      (PQ.fineToCoarse transport ∷ x ∷ y ∷ []))
    (solve
      (PQ.coarseToFine transport ∷ x ∷ y ∷ []))

oddTransportAnticommutatorZero : ∀ transport state →
  PQ.stateAdd
    (Grading.grading
      (PQ.applyTransport (Grading.oddTransport transport) state))
    (PQ.applyTransport
      (Grading.oddTransport transport)
      (Grading.grading state))
  ≡ PQ.zeroState
oddTransportAnticommutatorZero transport (PQ.split-state x y) =
  PQ.stateExt
    (solve (PQ.fineToCoarse transport ∷ x ∷ y ∷ []))
    (solve (PQ.coarseToFine transport ∷ x ∷ y ∷ []))

------------------------------------------------------------------------
-- Physical status.
------------------------------------------------------------------------

physicalHardShellProjectionSelfAdjointReused : Bool
physicalHardShellProjectionSelfAdjointReused =
  OfficialParseval.officialPhysicalHardProjectorOrthogonalConstructed

physicalLowTransportSkewAdjointConstructed : Bool
physicalLowTransportSkewAdjointConstructed = false

physicalOddTransportSingleGramRealizationConstructed : Bool
physicalOddTransportSingleGramRealizationConstructed = false

comAdjointCollapseAlgebraClosed : Bool
comAdjointCollapseAlgebraClosed = true

physicalHardShellProjectionSelfAdjointReusedIsTrue :
  physicalHardShellProjectionSelfAdjointReused ≡ true
physicalHardShellProjectionSelfAdjointReusedIsTrue =
  OfficialParseval.officialPhysicalHardProjectorOrthogonalConstructedIsTrue

comAdjointCollapseAlgebraClosedIsTrue :
  comAdjointCollapseAlgebraClosed ≡ true
comAdjointCollapseAlgebraClosedIsTrue = refl
