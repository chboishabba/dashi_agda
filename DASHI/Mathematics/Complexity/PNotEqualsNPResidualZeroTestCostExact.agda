module DASHI.Mathematics.Complexity.PNotEqualsNPResidualZeroTestCostExact where

------------------------------------------------------------------------
-- ONE-BIT ZERO TEST, LINEAR CONSTRUCTION COST
--
-- Complement to:
--   PNotEqualsNPGenericGateResidualCubeExact
--   PNotEqualsNPExactResidualSummaryBitLowerBoundExact
--
-- Although the full raw residual vector needs g bits for exact reopening, the
-- single semantic property
--
--   "are ALL residuals false?"
--
-- can be represented by one Boolean bit.
--
-- However the direct exact zero-test still consumes every residual coordinate.
-- Thus:
--
--   residual reconstruction width  = g
--   zero/nonzero output width       = 1
--   direct deterministic work       = g coordinates
--
-- This is the exact distinction needed by P11: short semantic output is not
-- the breakthrough; resource-bounded derivation of that output is.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _,_)
open import Data.Vec.Base using (Vec; []; _∷_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit

------------------------------------------------------------------------
-- Exact semantic zero test.
------------------------------------------------------------------------

allResidualsZero :
  ∀ {width : Nat} →
  Vec Bool width →
  Bool
allResidualsZero [] =
  true
allResidualsZero (residual ∷ residuals) =
  Cook.andBool
    (Cook.notBool residual)
    (allResidualsZero residuals)

allFalseVector :
  (width : Nat) →
  Vec Bool width
allFalseVector zero =
  []
allFalseVector (suc width) =
  false ∷ allFalseVector width

allFalseVectorAccepted :
  (width : Nat) →
  allResidualsZero (allFalseVector width)
  ≡ true
allFalseVectorAccepted zero =
  refl
allFalseVectorAccepted (suc width)
    rewrite allFalseVectorAccepted width =
  refl

------------------------------------------------------------------------
-- Any true residual coordinate forces rejection.
------------------------------------------------------------------------

ResidualViolation :
  ∀ {width : Nat} →
  Vec Bool width →
  Set
ResidualViolation {width} residuals =
  Σ (Fin width) λ index →
    Circuit.lookupVec index residuals
    ≡ true

trueCoordinateForcesZeroTestFalse :
  ∀ {width : Nat}
    (residuals : Vec Bool width) →
  ResidualViolation residuals →
  allResidualsZero residuals
  ≡ false
trueCoordinateForcesZeroTestFalse
    (false ∷ residuals)
    (fzero , ())
trueCoordinateForcesZeroTestFalse
    (true ∷ residuals)
    (fzero , refl) =
  refl
trueCoordinateForcesZeroTestFalse
    (false ∷ residuals)
    (fsuc index , residualTrue)
    rewrite
      trueCoordinateForcesZeroTestFalse
        residuals
        (index , residualTrue) =
  refl
trueCoordinateForcesZeroTestFalse
    (true ∷ residuals)
    (fsuc index , residualTrue) =
  refl

------------------------------------------------------------------------
-- Direct evaluation cost accounting.
------------------------------------------------------------------------

zeroTestCoordinatesRead :
  ∀ {width : Nat} →
  Vec Bool width →
  Nat
zeroTestCoordinatesRead [] =
  zero
zeroTestCoordinatesRead (residual ∷ residuals) =
  suc (zeroTestCoordinatesRead residuals)

zeroTestReadsEveryCoordinate :
  ∀ {width : Nat}
    (residuals : Vec Bool width) →
  zeroTestCoordinatesRead residuals
  ≡ width
zeroTestReadsEveryCoordinate [] =
  refl
zeroTestReadsEveryCoordinate (residual ∷ residuals)
    rewrite zeroTestReadsEveryCoordinate residuals =
  refl

------------------------------------------------------------------------
-- Research consequence.
--
-- There is no information-theoretic obstacle to a tiny ZERO/NONZERO semantic
-- answer.  The obstacle is producing that answer without scanning/evaluating
-- the whole unconstrained residual object or hiding the computation in an
-- omniscient constructor.
------------------------------------------------------------------------
