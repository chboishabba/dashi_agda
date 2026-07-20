# DNA chemistry-native four-adic sheet formalism

## Status

This tranche is a typed candidate/bridge surface. It formalises the carrier,
rank hierarchy, involutions, operational chemistry Hamiltonian terms, and the
bounded role of ternary quotient coordinates. It does **not** claim a complete
quantum-chemical derivation of synthesis, PCR, sequencing, folding, or storage
capacity.

## Carrier

`DASHI.Biology.DNAChemistryCarrier` defines the exact finite alphabet
`A/C/G/T`, complement, reverse-complement, and the exact UV coordinate chart:

- `U`: GC/AT strength class;
- `V`: purine/pyrimidine class.

The UV pair is bijective on the four bases. It is not promoted into a complete
microscopic chemistry model.

## Rank and lift hierarchy

`DASHI.Geometry.DNAFourAdicSheetLift` records the structural ladder:

- point: one base;
- 4-line: four points;
- 16-sheet: four lines;
- 64-voxel: four sheets;
- 256-supervoxel: four voxels.

The constructors and projections make the finite lift recognisable. A sheet is
rank two, not a plotting convention. A voxel is a typed stack of sheets, and a
supervoxel is a typed stack of voxels. Recursive exponent/tetration readings
remain symbolic beyond the materialised finite carrier.

The module also defines an abstract `RecognisableSheetLift` interface. A detail
sheet is a signed residual between a fine representative and the broadcast of
its next-coarser representative. The residual carrier reuses the canonical
`SSPTrit` `-1/0/+1` surface already present in the repository.

## Chemistry Hamiltonian boundary

`DASHI.Biology.DNAChemistryHamiltonianBoundary` separates exact codec-state
constraints from operational physical approximations:

- GC debt and configured run/motif bans are exact state-machine predicates;
- nearest-neighbour Delta G is an empirical local thermodynamic approximation;
- hairpin and dimer kernels are cross-rank reverse-complement interaction
  approximations;
- PCR, synthesis, and sequencing risk remain pipeline-dependent operational
  observables.

The canonical first configuration records:

- maximum homopolymer run `4` (so `GG` is permitted; a fifth repeated base is
  rejected);
- minimum hairpin stem `8`;
- search radius `64`;
- exact, one-mismatch, and two-mismatch classes;
- hard reverse-complement / near-reverse-complement gates;
- multiscale U and V balance;
- nearest-neighbour Delta G scoring.

Microscopic chemistry is exact in principle through the full physical
Hamiltonian, but this codec does not carry the complete molecular/environmental
microstate. The quotient is therefore operational: sequences are grouped by the
chemistry basin the writing/reading pipeline can distinguish.

## Ternary quotient boundary

`DASHI.Biology.DNAChemistryTritQuotientBridge` keeps CAGT primitive. Ternary is
used only as a signed residual or chemistry-margin coordinate:

- negative;
- neutral;
- positive.

It is not claimed to reconstruct base identity or to force every encoder step
into arity three. Payload transport must use the actual admissible fibre
(`1/2/3/4` choices), while sparse tight events may contribute to lifted checks.
This directly corrects the earlier temptation to identify a stored plane with a
mathematical band or to treat ternary as the physical DNA alphabet.

## Relation to existing DASHI formalism

This tranche deliberately reuses:

- `DASHI.Foundations.SSPTritCarrier` for the canonical signed residual;
- the repository's recognisable lift / supervoxel vocabulary;
- involution-equivariant bridge discipline;
- receipt-gated, fail-closed candidate boundaries.

`DASHI.Biology.DNAChemistryFormalismRegression` is the compact import and
witness surface for the full tranche.
