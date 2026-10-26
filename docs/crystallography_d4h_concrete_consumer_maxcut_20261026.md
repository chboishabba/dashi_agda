# PR #1261 max-cut: concrete D4h consumer fixture and compiler remediation

## This cut (2026-10-26)
- Added `TetragonalFiniteCrystalConsumerExact.agda`: a concrete
  `CrystalRealization` based on the existing D4h normal form,
  full finite eight-site group action, and the native 369
  `AtomicIndex`. Classifies the synthetic instance as tP / 4/mmm.
- Repaired missing unqualified Boolean and quarter-turn constructor
  imports in `TetragonalD4hFullActionExact.agda`, which contains
  finite exhaustive proof terms. Source changes are not an Agda
  compiler receipt; Agda is not available in this execution runtime.

## Precisely what the concrete instance demonstrates
This is an *end-to-end finite interface fixture*: group actions,
composition/identity witnesses, pairing-preserving map, species
preservation, and scalar invariant observable. It is not a physical
lattice realization: Direct and Reciprocal are both eight-site
enumerations, Pairing is equality, BandEnergy is a zero fixture,
and the synthetic mono-species labels do not identify any material.

## Highest Pareto proof frontier
1. Run Agda against the complete imported dependency cone and repair
   actual elaboration failures; not CI-dependent.
2. Build the direct integer lattice + reciprocal contragredient
   representation over Z³, with an invariant pairing lemma,
   and prove W(B2)×W(A1) preserves the tetragonal metric.
3. Instantiate that nontrivial lattice model with source 369 atomic
   decorations and site orbits.
4. Reuse B3/B4 to build the fcc diamond two-sublattice Seitz
   structure, then NV ordered-defect stabilizers and separate
   spin-one Hamiltonian covariance/obstructions (PRs #1238/#1262).
5. Consume generic hyperfabric/T4/T9/T18 local-global interfaces
   where compatible site/channel actions are actually supplied.
   XOR is optional seam bookkeeping, not the project centre.
6. Expand the 7/14/32 catalogues into verified representations,
   authoritative 230-space-group operation data, and observable
   validation (Bloch/ODMR/diffraction).

## Attribution
Classical crystallography, group theory and Fourier lattice
duality remain original-source prior art; code donors remain
attributed to their original modules/PRs. No finite enumeration
is promoted to a proof of quantum physics or empirical structure.
