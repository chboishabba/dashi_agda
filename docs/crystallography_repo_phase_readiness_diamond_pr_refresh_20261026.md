# PR #1261 repository/roadmap assessment, 2026-10-26 (new diamond donors)

## Implemented in this cut
- The previous source-level D4h integer coordinate action now also carries
  generator proofs: quarter-turn order four; vertical reflection
  conjugates quarter-turn to inverse; horizontal mirror centralises both.
  Proofs require only an involutive scalar negation.
- Locally executed independent `/mnt/data/tetragonal_integer_audit.py`
  using exact Python integers: 16 distinct matrices, sample diagonal
  tetragonal metric invariance and Fourier dot-product invariance.
  This is a sample numeric audit, not a universal Agda lattice theorem.

## Donor refresh from current PR search
- #1270, `SaxonQFiniteQutritLogicalEncodingExact.agda`:
  source-attributed multicore NV/qutrit encoding. Distinguish a
  logical qutrit representation from crystallographic C3 action or
  unrestricted physical Hamiltonian gate fidelity.
- #1269, `NVMCGQuantumComputingSameObjectWeldExact.agda`,
  `NVPhotonHistoryFiniteSumExact.agda` and
  `NVPhotonObserverRefinementExact.agda`:
  finite photon histories, observation/refinement and the
  measured-readout bridge. Their evidence must remain separate
  from the underlying Hamiltonian and crystal symmetry.
- #1262: spin-one zero-field-splitting obstruction to cycling
  all three spin labels as though they were a spatial C3.
- #1238: NV <111> orientation and optical/magnetic finite
  readout prior art.
- #1115/#1076: material-specific Seitz/Bloch representation
  techniques, transferable only as interfaces.

## Current repo state (by real deliverables)
1. **Finite symmetry:** D4h abstract 16 normal form,
   matrix generator action, finite eight-site carrier and
   exact source-level group/action case split; substantial but
   Agda typechecking receipt open.
2. **Crystallographic classification:** 7 crystal systems,
   14 Bravais and 32 point-group labels, *not* classification
   proofs or a 230-group operation catalogue.
3. **Lattice:** generic involutive scalar 3-coordinate action
   with generator relations; finite numerical orthogonality
   checks. Formal direct/reciprocal `Z³` bilinear pairing
   and metric proof are next.
4. **Ternary geometry/hyperfabric:** Punctured 27 = 8+9+9
   partial decoding with two-sided successful decode proofs,
   13 antipodal projective directions and four diamond
   body axes; other branches own pants/T4/T9/T18 and
   original antipodal adjacency. Keep XOR auxiliary.
5. **Physical species:** existing atomic 369 Z,N,e model
   consumed by source-level species-labelled fixtures,
   not a real lattice decoration over a space group.
6. **Diamond:** fcc/Fd-3m spatial realization, ordered
   N/vacancy stabiliser, orbital/spin symmetry, Bloch
   Hamiltonian covariance, multicore qutrit and measured
   photon-readout chain are distinct live obligations.

## Pareto phase cut and acceptance tests

**P1 — Kernel-grade group/lattice mathematics.**
Source Agda compile of D4h cone; reduce the 623 kB
exhaustive action file where possible; show 16 faithful
integral matrices, metric preservation, dual pairing
and inverse transpose. Check both tP and tI basis
conventions without conflating a primitive basis with
the conventional cell.

**P2 — Concrete 3D crystallography.**
Define tetragonal/diamond lattice basis + centring,
Seitz affine group operations, point-group stabilisers
and exact 3D position/reciprocal pairing. Produce one
model with actual site coordinates rather than a
permutation-only synthetic fixture.

**P3 — Physical quantum-material consumers.**
Use source atomic 369 electrons/protons and fermion
shell data, true diamond cubic basis, NV defect
stabiliser, Hamiltonian symmetry/obstruction.
Consume #1270's qutrit/multicore and #1269's photon
observer work only after operator/measurement
composition conditions are explicit.

**P4 — Generalisation/validation.**
7/14/32 model representatives and eventually 230
IUCr type records with independently checked
spglib/International Tables conventions; physical
spectra, Bloch/ODMR/diffraction calibrations and
held-out discriminating experiments.

**Supporting cross-validation:** 27→26→13→4,
T4/T9/T18, pants/hyperfabric consistency,
W(B4) embeddings and residual-preserving observer
proofs. The goal is common reusable mathematics,
not identifying unrelated algebraic structures
because they share 13/27/111/3.

## Critical correction to claims
Kernel compilation is not established by the emitted
Agda source or Python audits. Metric preservation on
tested diagonal metrics is not an Agda proof of all
integer/rational tetragonal metrics. Nonsymmorphic
diamond and device spectroscopy are not yet proved
by the crystal classification fixtures. Claims about
original sources, source-code proof obligations,
physical device data and independent external
corroboration remain separate.

## Attribution
IUCr/classical lattice/space-group theory; original
quantum NV, Bloch, spin-one and experimental research;
original DASHI owner files and PR #1270/#1269/
#1262/#1238/#1115/#1076 remain source authorities.
PR #1261 authorship is restricted to its
adapter/proof/documentation contribution.
