module DASHI.Crypto.MLKEMExactResidualTouchLowerBoundExact where

------------------------------------------------------------------------
-- ML-KEM: EXACT MATERIALISED RESIDUAL TOUCH LOWER BOUND
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Finite-field uncertainty source:
-- Martino Borello; Patrick Sole,
-- "The uncertainty principle over finite fields",
-- Discrete Mathematics 345 (2022), 112670.
-- DOI: 10.1016/j.disc.2021.112670.
--
-- PURPOSE
--
-- Move the uncertainty result from an abstract verifier-work variable onto a
-- concrete operational resource: the number of cells changed/touched by an
-- exact, explicitly materialised residual state.
--
-- If a residual cell is updated by
--
--     r' = r - d,
--
-- then d != 0 forces r' != r in any commutative ring.  Hence, for an exact
-- residual array whose update discipline requires every changed cell to be
-- touched/materialised, changed-cell count is bounded by touch count.
--
-- Combining that fact with the existing singular-budget uncertainty law
--
--     128 <= s * (changed + sigma)
--
-- gives
--
--     128 <= s * (touches + sigma).
--
-- This is a state-update/memory-touch lower bound, NOT a generic wall-clock or
-- instruction-count lower bound.  Compressed/lazy verifier states are outside
-- this materialised-state theorem and must be handled by a separate sufficient-
-- state/readout theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (nothing)
open import Data.Nat using (Nat; _≤_; _+_; _*_ ; z≤n; s≤s)
import Data.Nat.Properties as NatP
import Tactic.RingSolver.Core.AlmostCommutativeRing as RingCore
import Tactic.RingSolver.NonReflective as RingSolver

------------------------------------------------------------------------
-- Same-cell algebra: subtracting a nonzero delta cannot leave an exact
-- residual cell unchanged.
------------------------------------------------------------------------

module _ {c ℓ : Level} (R : CommutativeRing c ℓ) where

  open CommutativeRing R
    renaming
      ( Carrier to F
      ; _+_ to _⊕_
      ; -_ to neg
      ; 0# to 0F
      )

  private
    solverRing : RingCore.AlmostCommutativeRing c ℓ
    solverRing = RingCore.fromCommutativeRing R (λ _ → nothing)

    module S = RingSolver solverRing

  residualUpdate : F → F → F
  residualUpdate residual delta = residual ⊕ neg delta

  residualUnchangedForcesZeroDelta :
    (residual delta : F) →
    residualUpdate residual delta ≡ residual →
    delta ≡ 0F
  residualUnchangedForcesZeroDelta residual delta updateEqual =
    S.solve 2
      (λ residual delta → delta S.⊜ S.con 0)
      updateEqual
      residual delta

  nonzeroDeltaChangesResidual :
    (residual delta : F) →
    (delta ≡ 0F → ⊥) →
    residualUpdate residual delta ≡ residual →
    ⊥
  nonzeroDeltaChangesResidual residual delta deltaNonzero updateEqual =
    deltaNonzero
      (residualUnchangedForcesZeroDelta residual delta updateEqual)

------------------------------------------------------------------------
-- Exact materialised residual-cell outcome alphabet.
--
-- There is deliberately no constructor for "changed and untouched".  That is
-- the operational meaning of an exact explicitly materialised residual array:
-- every cell whose value changes must be updated/materialised by the primitive.
------------------------------------------------------------------------

data ExactResidualCellOutcome : Set where
  unchangedUntouched
  unchangedTouched
  changedTouched : ExactResidualCellOutcome

changedWeight : ExactResidualCellOutcome → Nat
changedWeight unchangedUntouched = 0
changedWeight unchangedTouched = 0
changedWeight changedTouched = 1

touchWeight : ExactResidualCellOutcome → Nat
touchWeight unchangedUntouched = 0
touchWeight unchangedTouched = 1
touchWeight changedTouched = 1

changedWithinTouches :
  (outcome : ExactResidualCellOutcome) →
  changedWeight outcome ≤ touchWeight outcome
changedWithinTouches unchangedUntouched = z≤n
changedWithinTouches unchangedTouched = z≤n
changedWithinTouches changedTouched = s≤s z≤n

sumWeight :
  (ExactResidualCellOutcome → Nat) →
  List ExactResidualCellOutcome → Nat
sumWeight weight [] = 0
sumWeight weight (outcome ∷ rest) =
  weight outcome + sumWeight weight rest

changedCellCount : List ExactResidualCellOutcome → Nat
changedCellCount = sumWeight changedWeight

touchCount : List ExactResidualCellOutcome → Nat
touchCount = sumWeight touchWeight

changedCellCountWithinTouches :
  (outcomes : List ExactResidualCellOutcome) →
  changedCellCount outcomes ≤ touchCount outcomes
changedCellCountWithinTouches [] = z≤n
changedCellCountWithinTouches (outcome ∷ rest) =
  NatP.+-mono-≤
    (changedWithinTouches outcome)
    (changedCellCountWithinTouches rest)

------------------------------------------------------------------------
-- Uncertainty -> exact residual-touch resource.
------------------------------------------------------------------------

exactResidualTouchObstruction128 :
  (sourceSupport singularBudget : Nat) →
  (outcomes : List ExactResidualCellOutcome) →
  128 ≤ sourceSupport * (changedCellCount outcomes + singularBudget) →
  128 ≤ sourceSupport * (touchCount outcomes + singularBudget)
exactResidualTouchObstruction128
  sourceSupport singularBudget outcomes uncertaintyChanged =
  NatP.≤-trans
    uncertaintyChanged
    (NatP.*-monoʳ-≤ sourceSupport
      (NatP.+-mono-≤
        (changedCellCountWithinTouches outcomes)
        NatP.≤-refl))

fullRankExactResidualTouchObstruction128 :
  (sourceSupport : Nat) →
  (outcomes : List ExactResidualCellOutcome) →
  128 ≤ sourceSupport * changedCellCount outcomes →
  128 ≤ sourceSupport * touchCount outcomes
fullRankExactResidualTouchObstruction128
  sourceSupport outcomes uncertaintyChanged =
  NatP.≤-trans
    uncertaintyChanged
    (NatP.*-monoʳ-≤ sourceSupport
      (changedCellCountWithinTouches outcomes))

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- The ring theorem above proves the same-cell semantic fact:
-- a nonzero residual delta changes the exact residual value.
--
-- The outcome alphabet then formalises one specific implementation resource:
-- an explicitly materialised exact residual state where changed cells are
-- touched.  It does not claim that every possible ML-KEM recovery algorithm
-- maintains such a state.  A compressed/lazy/symbolic verifier can avoid this
-- resource only by moving the burden into its state update/readout semantics;
-- proving a representation-independent sufficient-state lower bound is the
-- next, stronger research seam.
------------------------------------------------------------------------
