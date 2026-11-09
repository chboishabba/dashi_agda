module DASHI.Physics.Chemistry.AtomicPeriodicTable369Nickel41ElectronAccountingExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Molecular electron accounting for SOURCE-PRINTED nickel 41-atom structures.
--
-- Coordinates/source: Zhao et al., arXiv:2506.22408, section VI.9.2.
-- These equations concern nuclear CHARGES and combinatorics, not an
-- inferred periodic-table electronic Hamiltonian, quantum chemical
-- orbital selection, or a measurement of total molecular spin/charge.
--
-- Source composition (for each of B, BC, C): Ni1 P2 C13 O1 H24.
-- Atomic nuclear charges: Ni28, P15, C6, O8, H1.
------------------------------------------------------------------------

record Source41Composition : Set where
  constructor source41Composition
  field
    nickel : Nat
    phosphorus : Nat
    carbon : Nat
    oxygen : Nat
    hydrogen : Nat

open Source41Composition public

sourceB : Source41Composition
sourceB = source41Composition 1 2 13 1 24

sourceBC : Source41Composition
sourceBC = source41Composition 1 2 13 1 24

sourceC : Source41Composition
sourceC = source41Composition 1 2 13 1 24

atomCount : Source41Composition → Nat
atomCount c =
  nickel c + phosphorus c + carbon c + oxygen c + hydrogen c

nuclearCharge : Source41Composition → Nat
nuclearCharge c =
  28 * nickel c +
  15 * phosphorus c +
  6 * carbon c +
  8 * oxygen c +
  hydrogen c

sourceBHas41Atoms : atomCount sourceB ≡ 41
sourceBHas41Atoms = refl

sourceBCHas41Atoms : atomCount sourceBC ≡ 41
sourceBCHas41Atoms = refl

sourceCHas41Atoms : atomCount sourceC ≡ 41
sourceCHas41Atoms = refl

sourceNuclearChargeIs168 : nuclearCharge sourceB ≡ 168
sourceNuclearChargeIs168 = refl

sourceBCNuclearChargeIs168 : nuclearCharge sourceBC ≡ 168
sourceBCNuclearChargeIs168 = refl

sourceCNuclearChargeIs168 : nuclearCharge sourceC ≡ 168
sourceCNuclearChargeIs168 = refl

sameSourceCompositions :
  sourceB ≡ sourceBC × sourceBC ≡ sourceC
sameSourceCompositions = refl , refl

------------------------------------------------------------------------
-- Conditional neutral singlet occupancy hypothesis.
--
-- Neutral charge/spin are NOT read from XYZ, and these equalities do NOT
-- certify the original paper's selected spin/charge, orbitals or basis.
------------------------------------------------------------------------

sourceEightActiveElectrons : Nat
sourceEightActiveElectrons = 8

sourceEightActiveOrbitals : Nat
sourceEightActiveOrbitals = 8

selectedAlphaElectrons : Nat
selectedAlphaElectrons = 4

selectedBetaElectrons : Nat
selectedBetaElectrons = 4

selectedCorePairsIfNeutral : Nat
selectedCorePairsIfNeutral = 80

eightActiveElectronsSplitIntoFourAndFour :
  selectedAlphaElectrons + selectedBetaElectrons ≡ sourceEightActiveElectrons
eightActiveElectronsSplitIntoFourAndFour = refl

neutralSingletHypothesisRecovers168Electrons :
  2 * selectedCorePairsIfNeutral + sourceEightActiveElectrons ≡
  nuclearCharge sourceB
neutralSingletHypothesisRecovers168Electrons = refl

fullSpinUpCountIfNeutral :
  selectedCorePairsIfNeutral + selectedAlphaElectrons ≡ 84
fullSpinUpCountIfNeutral = refl

fullSpinDownCountIfNeutral :
  selectedCorePairsIfNeutral + selectedBetaElectrons ≡ 84
fullSpinDownCountIfNeutral = refl

-- No claims about the independent source's actual physical charge/spin
-- follow from these neutral-sector numerical equalities.
