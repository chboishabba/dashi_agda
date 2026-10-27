module DASHI.Unified.TOE369TetratedCornerCocycleConvergenceExact where

------------------------------------------------------------------------
-- TOE 369 convergence: reuse only. No new physical identification.
-- Original group-theory precedents: Dixon--Mortimer; Nekrashevych.
-- Original DASHI constructions remain owned by their source modules.
-- This bridge was prepared with OpenAI ChatGPT assistance.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369NonaryTritSquareExact as Square
import DASHI.Moonshine.Base369Pointed729CornerTritSquareBidiExact as Corner
import DASHI.Biology.SelfIndexedParetoHyperfabricTetrationExact as Tower
import DASHI.Moonshine.Monster369NDimParetoTetrationBridgeExact as MonsterTower
import DASHI.Core.ParetoSymmetryQuotientAdmissionExact as Admission
import DASHI.Moonshine.Monster369DiscriminatorSymmetryBoundaryExact as Guard
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed
import DASHI.Analysis.PickoverSignedZeroTorque369GridExact as ABC

-- Nine-as-square is a two-sided *carrier* chart, not a C9 -> C3^2
-- group isomorphism.
toeNonarySquareRoundTrip :
  (square : Square.TritSquare) →
  Square.nonaryDigitToTritSquare (Square.tritSquareToNonaryDigit square)
  ≡ square
toeNonarySquareRoundTrip = Square.tritSquareRoundTrip

-- Corner-trit-square is an exact reverse chart over all 729 addresses.
toeCornerSquareRoundTrip :
  (state : Corner.CornerCompleted729) →
  Corner.toCornerCompleted729 (Corner.fromCornerCompleted729 state)
  ≡ state
toeCornerSquareRoundTrip = Corner.toAfterFromCornerCompleted729

-- The tower is a genuine typed recurrence, not a merely symbolic marker.
toeNineAxisSeed : Tower.paretoAxisCount 1 ≡ 9
toeNineAxisSeed = Tower.paretoAxisCountOne

toeNineTetrationRecurrence :
  (n : Nat) →
  Tower.paretoAxisCount (suc n)
  ≡ DASHI.Biology.TernaryHypercubeHyperfabricExact.powNat 9
      (Tower.paretoAxisCount n)
toeNineTetrationRecurrence = Tower.paretoAxisCountRecurrence

-- ABC position action is already an exact S3-like generator witness
-- over the existing torque bracket cube. Its cyclic generator is order 3.
toeABCTripleCycle :
  (cube : ABC.Cube27) →
  ABC.rotateABC (ABC.rotateABC (ABC.rotateABC cube)) ≡ cube
toeABCTripleCycle = ABC.rotateABCThree

toeABCOpposition :
  (cube : ABC.Cube27) →
  ABC.reflectABC (ABC.reflectABC cube) ≡ cube
toeABCOpposition = ABC.reflectABCTwo

toeABCBraid :
  (cube : ABC.Cube27) →
  ABC.reflectABC (ABC.rotateABC (ABC.reflectABC cube))
  ≡ ABC.rotateABC (ABC.rotateABC cube)
toeABCBraid = ABC.reflectRotateReflect

-- Exact non-promotion owners are imported into this TOE root.
-- They enforce carrier symmetry != semantic Pareto automorphism;
-- finite voxel symmetry != actual Monster representation;
-- and finite bracket orientation != physical continuous SO(3).
toeMonsterSemanticNonPromotion :
  Guard.ternaryVoxelIsMonsterRepresentation
    Guard.canonicalMonster369DiscriminatorSymmetryBoundary
  ≡ false
toeMonsterSemanticNonPromotion = refl

toeCarrierSymmetryNeedsQualification :
  Guard.carrierSymmetryPreservesExperimentMeaningAutomatically
    Guard.canonicalMonster369DiscriminatorSymmetryBoundary
  ≡ false
toeCarrierSymmetryNeedsQualification = refl

toeTetratedAxesAgreeWith369 :
  Tower.paretoAxisCount 1 ≡ MonsterTower.base369NineAxes
toeTetratedAxesAgreeWith369 =
  MonsterTower.selfIndexedLevelOneAxisCountIsNine
