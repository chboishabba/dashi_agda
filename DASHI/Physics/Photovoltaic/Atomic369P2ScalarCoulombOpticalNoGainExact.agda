module DASHI.Physics.Photovoltaic.Atomic369P2ScalarCoulombOpticalNoGainExact where

-- Atomic 369 photovoltaic MAX-CUT: eliminate a false mechanism.
-- Source-reuse: exact selected 2p^2 Coulomb execution.
-- The computed Vee=(21/128) I_3 is scalar ON THIS RESTRICTED SECTOR.
-- Uniform identity shifts cannot produce transition-energy splitting INSIDE
-- that same sector, or rotate its eigenvectors. This is NOT a statement about
-- transitions to other sectors, correlations outside this projection, or
-- real crystals. Agda compiler acceptance NOT yet run.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
import Data.Nat.Properties as N
import DASHI.Physics.Chemistry.AtomicPeriodicTable369P2CoulombExecutionExact as P2

eqSym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
eqSym refl = refl

eqTrans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
eqTrans refl yz = yz

eqCong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
eqCong f refl = refl

-- Prove it on the actual source-owned selected three-state carrier,
-- rather than copying the 21/128 numeric coefficient.
allSelectedDiagonalCoulombEqual :
  (i : P2.P2Basis) ->
  P2.coulombMatrixElement i i ≡ P2.p2CoulombEnergy
allSelectedDiagonalCoulombEqual P2.p2NegZero = refl
allSelectedDiagonalCoulombEqual P2.p2NegPos = refl
allSelectedDiagonalCoulombEqual P2.p2ZeroPos = refl

-- Exact scalar matrix condition, off-diagonals vanish in source basis.
selectedOffDiagonalNegZeroNegPos :
  P2.coulombMatrixElement P2.p2NegZero P2.p2NegPos
  ≡ P2.zeroRational
selectedOffDiagonalNegZeroNegPos = refl

selectedOffDiagonalNegZeroZeroPos :
  P2.coulombMatrixElement P2.p2NegZero P2.p2ZeroPos
  ≡ P2.zeroRational
selectedOffDiagonalNegZeroZeroPos = refl

selectedOffDiagonalNegPosZeroPos :
  P2.coulombMatrixElement P2.p2NegPos P2.p2ZeroPos
  ≡ P2.zeroRational
selectedOffDiagonalNegPosZeroPos = refl

-- In any additive commutative energy representation, applying the same
-- shift to two levels preserves the original gap. Nat is a discrete
-- non-negative gap witness; the lemma is generic in the common shift.
-- A real-energy Hilbert/spectral operator analogue remains a physical gate.
uniformIdentityShiftPreservesSelectedGap :
  (lower gap commonShift : Nat) ->
  (lower + commonShift) + gap
  ≡ (lower + gap) + commonShift
uniformIdentityShiftPreservesSelectedGap lower gap commonShift =
  eqTrans
    (N.+-assoc lower commonShift gap)
    (eqTrans
      (eqCong (lower +_) (N.+-comm commonShift gap))
      (eqSym (N.+-assoc lower gap commonShift)))

-- Thus the scalar restricted p^2 Coulomb term is NOT the sought
-- oscillator-strength / bandgap enhancement. Candidate physical gains
-- must arise from a non-scalar material Hamiltonian, a transition involving
-- another physical sector, state-dependent coupling, or real carrier dynamics.
