module DASHI.Physics.Photovoltaic.PV369P2CoulombSolarNonPromotionExact where

-- M3 reuse-first obstruction to a false "369 photovoltaic splitting".
--
-- Original owner:
-- DASHI.Physics.Chemistry.AtomicPeriodicTable369P2CoulombExecutionExact
-- on the common-spin hydrogenic 2p^2 antisymmetric orbital sector.
-- Existing EXACT result: projected Vee = (21/128) * I_3.
--
-- This scalar 2p² Coulomb operator is an interaction-sensitive
-- computation, yet it cannot by itself split the three canonical
-- selected basis energies or generate a 369-distinct optical transition.
-- No arbitrary 369 solar wavelength bins are introduced.
-- A real GaAs [111] semiconductor mechanism must provide a DIFFERENT
-- actual crystal/spin-orbit/piezo/strain/defect or light-matter operator,
-- testable on the same eight-band material, source, EQE and loaded IV.
-- This theorem does NOT claim full atomic degeneracy or no possible
-- physical 369 mechanism outside the selected exact 2p² carrier.
-- Local Agda Golden acceptance is OPEN.

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Chemistry.AtomicPeriodicTable369P2CoulombExecutionExact as P2
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ManyBodyHamiltonianTerminalMaxCutExact as Atom
import DASHI.Physics.Chemistry.AtomicPeriodicTable369SymmetryProjectionCompilerExact as Projection
import DASHI.Physics.Photovoltaic.Atomic369BasisTransportNoFreeGainExact as Basis
import DASHI.Physics.Photovoltaic.GaAs111OpticalDeviceSourceWeldExact as Optical

-- This is exact source-reuse, not a distinct physical solar Hamiltonian.
allThreeP2DiagonalEnergiesIdentical :
  (x : P2.P2Basis) ->
  P2.coulombMatrixElement x x ≡ P2.p2CoulombEnergy
allThreeP2DiagonalEnergiesIdentical P2.p2NegZero = refl
allThreeP2DiagonalEnergiesIdentical P2.p2NegPos = refl
allThreeP2DiagonalEnergiesIdentical P2.p2ZeroPos = refl

-- Original exact p² C3 covariance on the same canonical basis, reused.
p2CoulombC3Symmetry :
  (x y : P2.P2Basis) ->
  P2.coulombMatrixElement (P2.p2C3Step x) (P2.p2C3Step y)
    ≡ P2.coulombMatrixElement x y
p2CoulombC3Symmetry = P2.coulombMatrixIsC3Invariant

-- All off-diagonal elements are zero on this selected P2 chart.
p2OffDiagonalNegZeroNegPos :
  P2.coulombMatrixElement P2.p2NegZero P2.p2NegPos
    ≡ P2.zeroRational
p2OffDiagonalNegZeroNegPos = refl

p2OffDiagonalNegZeroZeroPos :
  P2.coulombMatrixElement P2.p2NegZero P2.p2ZeroPos
    ≡ P2.zeroRational
p2OffDiagonalNegZeroZeroPos = refl

p2OffDiagonalNegPosZeroPos :
  P2.coulombMatrixElement P2.p2NegPos P2.p2ZeroPos
    ≡ P2.zeroRational
p2OffDiagonalNegPosZeroPos = refl

-- THE LIVE LEAF is not an extra assumption of solar benefit:
-- same-body action and selected CI from original projection compiler,
-- then physical crystal/environment coupling, measured wavelength-
-- resolved absorption, extracted carriers and terminal IV.
-- See original Atom.firstLiveLeaf.
