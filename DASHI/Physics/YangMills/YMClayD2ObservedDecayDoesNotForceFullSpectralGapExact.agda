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
