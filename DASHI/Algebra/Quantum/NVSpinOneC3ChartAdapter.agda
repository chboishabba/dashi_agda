module DASHI.Algebra.Quantum.NVSpinOneC3ChartAdapter where

-- Exact C3 level-label chart for NV spin-one research.
-- Reuses the repository's established finite C3 action and generic
-- equivariance gate; this is not a physical three-level unitary claim.
-- A basis intertwiner to the physical spin-one carrier must be supplied
-- before the chart can transport Hamiltonians or quantum gates.

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Core.ThreeChannelC3EquivarianceGateExact as Gate
import DASHI.Algebra.Quantum.NVSpinOneMulticoreAdapter as NV
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Algebra.TriadicDepthOneCharacters as Phases

-- These are the *labels* of a chosen ordered spin-one basis, not the
-- physical spin eigenstates themselves.
SpinOneLevelLabel : Set
SpinOneLevelLabel = C3.C3

cycleLabel : SpinOneLevelLabel → SpinOneLevelLabel
cycleLabel = C3.act C3.c1

cycleLabelCubed : ∀ x →
  cycleLabel (cycleLabel (cycleLabel x)) ≡ x
cycleLabelCubed C3.c0 = refl
cycleLabelCubed C3.c1 = refl
cycleLabelCubed C3.c2 = refl

levelC3Action : Gate.OrderThreeAction SpinOneLevelLabel
levelC3Action = record
  { rotate = cycleLabel
  ; rotateCubed = cycleLabelCubed
  }

-- An exact bridge from finite C3 labels to the symbolic cyclotomic
-- phases already formalised in the repository.
labelPhase : SpinOneLevelLabel → Phases.C3Phase
labelPhase C3.c0 = Fourier.one
labelPhase C3.c1 = Fourier.zeta
labelPhase C3.c2 = Fourier.zetaSquared

-- The structure is available already, without introducing any new
-- dimension assumption or identifying C3 with the physical spin group.
spinOneDimensionIsThree : NV.nvElectronCarrierDimension ≡ 3
spinOneDimensionIsThree = NV.nvElectronCarrierDimensionIsThree

-- The next physical seam is a *separately witnessed* basis encoding,
-- with a demonstrated intertwiner (if any).  Cyclic permutation of
-- three basis labels is NOT, by itself, a spin-rotation symmetry of
-- the NV Hamiltonian; D Sz^2 generally breaks such an identification.
