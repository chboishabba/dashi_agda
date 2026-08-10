module DASHI.Physics.Closure.NSTriadKNComPQCrossChannelRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- DASHI CONTRIBUTION
--
-- Make the coarse/detail decomposition of the Round-36 Com naturality defect
-- exact on the smallest nontrivial carrier.  With complementary projections
--
--   P(x,y) = (x,0),   Q(x,y) = (0,y),   I = P + Q,
--
-- and a literal two-channel transport
--
--             [ a  b ]
--   T(x,y) =  [      ] (x,y),
--             [ c  d ]
--
-- the commutator has no diagonal contribution:
--
--   [P,T] = PT - TP = PTQ - QTP.
--
-- More precisely,
--
--   [P,T](x,y) = (b y, - c x)
--
-- and therefore the exact squared defect is
--
--   ||[P,T](x,y)||^2 = b^2 y^2 + c^2 x^2.
--
-- This proves that all failure of coarse transport naturality lives in the
-- coarse<->fine cross channels.  The remaining physical Navier--Stokes Com
-- theorem is consequently not a shell-arithmetic problem: it must identify
-- the literal shell operator products with these cross-channel maps and then
-- use the existing Round-35 Gram/Cotlar envelope.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

record SplitState : Set where
  constructor split-state
  field
    coarse detail : ℚ

open SplitState public

stateExt : ∀ {left right : SplitState} →
  coarse left ≡ coarse right →
  detail left ≡ detail right →
  left ≡ right
stateExt
  {split-state leftCoarse leftDetail}
  {split-state .leftCoarse .leftDetail}
  refl refl = refl

zeroState : SplitState
zeroState = split-state 0ℚ 0ℚ

stateAdd : SplitState → SplitState → SplitState
stateAdd (split-state ax ay) (split-state bx by) =
  split-state (ax + bx) (ay + by)

stateSubtract : SplitState → SplitState → SplitState
stateSubtract (split-state ax ay) (split-state bx by) =
  split-state (ax - bx) (ay - by)

projectCoarse : SplitState → SplitState
projectCoarse (split-state x y) = split-state x 0ℚ

projectFine : SplitState → SplitState
projectFine (split-state x y) = split-state 0ℚ y

projectCoarseIdempotent : ∀ state →
  projectCoarse (projectCoarse state) ≡ projectCoarse state
projectCoarseIdempotent (split-state x y) = refl

projectFineIdempotent : ∀ state →
  projectFine (projectFine state) ≡ projectFine state
projectFineIdempotent (split-state x y) = refl

coarseFineResolutionOfIdentity : ∀ state →
  stateAdd (projectCoarse state) (projectFine state) ≡ state
coarseFineResolutionOfIdentity (split-state x y) =
  stateExt (solve (x ∷ [])) (solve (y ∷ []))

coarseAfterFineZero : ∀ state →
  projectCoarse (projectFine state) ≡ zeroState
coarseAfterFineZero (split-state x y) = refl

fineAfterCoarseZero : ∀ state →
  projectFine (projectCoarse state) ≡ zeroState
fineAfterCoarseZero (split-state x y) = refl

record LinearTransport2 : Set where
  constructor linear-transport2
  field
    coarseToCoarse fineToCoarse coarseToFine fineToFine : ℚ

open LinearTransport2 public

applyTransport : LinearTransport2 → SplitState → SplitState
applyTransport transport (split-state x y) =
  split-state
    (coarseToCoarse transport * x + fineToCoarse transport * y)
    (coarseToFine transport * x + fineToFine transport * y)

commutator : LinearTransport2 → SplitState → SplitState
commutator transport state =
  stateSubtract
    (projectCoarse (applyTransport transport state))
    (applyTransport transport (projectCoarse state))

fineToCoarseChannel : LinearTransport2 → SplitState → SplitState
fineToCoarseChannel transport state =
  projectCoarse (applyTransport transport (projectFine state))

coarseToFineChannel : LinearTransport2 → SplitState → SplitState
coarseToFineChannel transport state =
  projectFine (applyTransport transport (projectCoarse state))

crossChannelDefect : LinearTransport2 → SplitState → SplitState
crossChannelDefect transport state =
  stateSubtract
    (fineToCoarseChannel transport state)
    (coarseToFineChannel transport state)

commutatorCoordinates : ∀ transport state →
  commutator transport state
  ≡ split-state
      (fineToCoarse transport * detail state)
      (- (coarseToFine transport * coarse state))
commutatorCoordinates transport (split-state x y) =
  stateExt
    (solve
      ( coarseToCoarse transport
      ∷ fineToCoarse transport
      ∷ x ∷ y ∷ []))
    (solve
      ( coarseToFine transport
      ∷ fineToFine transport
      ∷ x ∷ []))

fineToCoarseCoordinates : ∀ transport state →
  fineToCoarseChannel transport state
  ≡ split-state (fineToCoarse transport * detail state) 0ℚ
fineToCoarseCoordinates transport (split-state x y) =
  stateExt
    (solve
      ( coarseToCoarse transport
      ∷ fineToCoarse transport
      ∷ y ∷ []))
    refl

coarseToFineCoordinates : ∀ transport state →
  coarseToFineChannel transport state
  ≡ split-state 0ℚ (coarseToFine transport * coarse state)
coarseToFineCoordinates transport (split-state x y) =
  stateExt
    refl
    (solve
      ( coarseToFine transport
      ∷ fineToFine transport
      ∷ x ∷ []))

commutatorIsCrossChannelDifference : ∀ transport state →
  commutator transport state ≡ crossChannelDefect transport state
commutatorIsCrossChannelDifference transport (split-state x y) =
  stateExt
    (solve
      ( coarseToCoarse transport
      ∷ fineToCoarse transport
      ∷ coarseToFine transport
      ∷ fineToFine transport
      ∷ x ∷ y ∷ []))
    (solve
      ( coarseToCoarse transport
      ∷ fineToCoarse transport
      ∷ coarseToFine transport
      ∷ fineToFine transport
      ∷ x ∷ y ∷ []))

stateNormSquared : SplitState → ℚ
stateNormSquared state =
  coarse state * coarse state + detail state * detail state

commutatorNormSquaredCrossChannelExact : ∀ transport state →
  stateNormSquared (commutator transport state)
  ≡
  (fineToCoarse transport * fineToCoarse transport)
    * (detail state * detail state)
  +
  (coarseToFine transport * coarseToFine transport)
    * (coarse state * coarse state)
commutatorNormSquaredCrossChannelExact transport (split-state x y) =
  solve
    ( coarseToCoarse transport
    ∷ fineToCoarse transport
    ∷ coarseToFine transport
    ∷ fineToFine transport
    ∷ x ∷ y ∷ [])

coarseBasis fineBasis : SplitState
coarseBasis = split-state 1ℚ 0ℚ
fineBasis = split-state 0ℚ 1ℚ

commutatorOnCoarseBasis : ∀ transport →
  commutator transport coarseBasis
  ≡ split-state 0ℚ (- coarseToFine transport)
commutatorOnCoarseBasis transport =
  stateExt
    (solve
      (coarseToCoarse transport ∷ fineToCoarse transport ∷ []))
    (solve
      (coarseToFine transport ∷ fineToFine transport ∷ []))

commutatorOnFineBasis : ∀ transport →
  commutator transport fineBasis
  ≡ split-state (fineToCoarse transport) 0ℚ
commutatorOnFineBasis transport =
  stateExt
    (solve
      (coarseToCoarse transport ∷ fineToCoarse transport ∷ []))
    (solve
      (coarseToFine transport ∷ fineToFine transport ∷ []))

diagonalTransport : ℚ → ℚ → LinearTransport2
diagonalTransport coarseMultiplier fineMultiplier =
  linear-transport2 coarseMultiplier 0ℚ 0ℚ fineMultiplier

diagonalTransportCommutesWithCoarseProjection :
  ∀ coarseMultiplier fineMultiplier state →
  commutator (diagonalTransport coarseMultiplier fineMultiplier) state
  ≡ zeroState
diagonalTransportCommutesWithCoarseProjection
    coarseMultiplier fineMultiplier (split-state x y) =
  stateExt
    (solve (coarseMultiplier ∷ x ∷ y ∷ []))
    (solve (fineMultiplier ∷ x ∷ []))

comPQCrossChannelAlgebraClosed : Bool
comPQCrossChannelAlgebraClosed = true

physicalComCrossChannelOperatorRealizationConstructed : Bool
physicalComCrossChannelOperatorRealizationConstructed = false

comPQCrossChannelAlgebraClosedIsTrue :
  comPQCrossChannelAlgebraClosed ≡ true
comPQCrossChannelAlgebraClosedIsTrue = refl

physicalComCrossChannelOperatorRealizationConstructedIsFalse :
  physicalComCrossChannelOperatorRealizationConstructed ≡ false
physicalComCrossChannelOperatorRealizationConstructedIsFalse = refl
