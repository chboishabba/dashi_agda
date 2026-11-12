module DASHI.Physics.YangMills.YMClayD2ObservedDecayDoesNotForceFullSpectralGapExact where

------------------------------------------------------------------------
-- D2 OS-HAMILTONIAN NEGATIVE CONTROL (finite discrete transfer model).
--
-- Selected observable correlation decay does not by itself establish
-- a positive spectral gap on ALL non-vacuum states of the SAME
-- reconstructed Hilbert space.
--
-- Concrete 3-mode toy: vacuum fixed, an observed excitation killed
-- by the transfer, an unobserved NONVACUUM excitation exactly fixed.
--
-- This is a fully constructed discrete transfer/certificate model,
-- not an interacting Wilson reflection-positive Hilbert space and
-- not a claim about the physical OS Hamiltonian spectrum.
--
-- The genuine physical D2 obligation requires source-identifying
-- the Wilson observable family with a dense/separating OS subspace
-- and a decay estimate uniform enough to extend to its completion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

data Bit : Set where
  b0 b1 : Bit

data Empty : Set where

data ThreeMode : Set where
  mode : Bit → Bit → Bit → ThreeMode

vacuum : ThreeMode
vacuum = mode b1 b0 b0

zeroState : ThreeMode
zeroState = mode b0 b0 b0

observedExcitation : ThreeMode
observedExcitation = mode b0 b1 b0

hiddenExcitation : ThreeMode
hiddenExcitation = mode b0 b0 b1

-- Orthogonal projection-like discrete transfer: observed sector
-- disappears after one step; vacuum and hidden mode remain fixed.
transfer : ThreeMode → ThreeMode
transfer (mode v o h) = mode v b0 h

transferVacuumFixed : transfer vacuum ≡ vacuum
transferVacuumFixed = refl

transferObservedVanishes :
  transfer observedExcitation ≡ zeroState
transferObservedVanishes = refl

transferHiddenUndamped :
  transfer hiddenExcitation ≡ hiddenExcitation
transferHiddenUndamped = refl

hiddenIsNotVacuum : hiddenExcitation ≡ vacuum → Empty
hiddenIsNotVacuum ()

hiddenIsNotZero : hiddenExcitation ≡ zeroState → Empty
hiddenIsNotZero ()

-- The same transfer is maximally contractive on the selected
-- observed excitation and not contractive at all on another
-- nonzero, non-vacuum mode.  Any spectral gap claim deduced
-- from only the observed test is therefore missing an operator-
-- wide or dense-subspace estimate and the SAME-OS identification.

------------------------------------------------------------------------
-- D2 SECOND, INDEPENDENT NEGATIVE CONTROL: DENSITY IS NOT A GAP.
--
-- Even if EVERY finite-support spectral test belongs to a dense core,
-- pointwise decay with mode-dependent rates 1/(n+1) does not imply
-- one uniform positive rate on the completion.  The Hilbert-space
-- example is H e_n = (1/(n+1)) e_n on the non-vacuum orthonormal
-- basis, H vacuum = 0; finite-support vectors are dense in l2.
--
-- The native proof below pays the FINITE/COUNTABLE arithmetic
-- obstruction: a proposed common reciprocal gap denominator K would
-- have to bound every n+1.  Taking n=K contradicts succ K <= K.
--
-- It does NOT assert that this toy is a physical OS Hamiltonian or
-- that a quantitative dense-source covariance estimate is impossible.
-- The unpaid physical D2 payment is a UNIFORM operator/dense-core
-- estimate on the SAME E1 reconstructed Hilbert space.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤nat_
data _≤nat_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤nat n
  s≤s : ∀ {m n} → m ≤nat n → suc m ≤nat suc n

sucNeverBelowSelf : (n : Nat) → suc n ≤nat n → Empty
sucNeverBelowSelf zero ()
sucNeverBelowSelf (suc n) (s≤s impossible) =
  sucNeverBelowSelf n impossible

-- Index n names the positive mode of eigenvalue 1/(n+1).
-- All modes have a strictly positive individual denominator.
spectralModeReciprocalDenominator : Nat → Nat
spectralModeReciprocalDenominator n = suc n

-- A uniform gap m>0 together with the Archimedean property would
-- supply a natural K with 1/K <= m and hence n+1 <= K for every mode.
-- This theorem refutes that latter integer certificate constructively.
noUniformPositiveReciprocalGapCertificate :
  (K : Nat) →
  ((n : Nat) → spectralModeReciprocalDenominator n ≤nat K) →
  Empty
noUniformPositiveReciprocalGapCertificate K purported =
  sucNeverBelowSelf K (purported K)

-- The crucial logical distinction from the existing 3-mode example:
-- ALL individual positive modes occur in the stated countable family.
-- The problem is missing UNIFORMITY, not an invisible selected sector.
