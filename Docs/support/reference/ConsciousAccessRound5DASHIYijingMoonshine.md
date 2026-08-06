# Conscious-access round five: DASHI/Yijing, oriented zero, symmetry, and natural systems

This tranche crystallises the finite formal spine developed in the DASHI/Yijing discussion. It is stacked on the round-four p-adic reasoning-field branch and reuses the existing balanced-trit carrier, SSP 3/6/9 ultrametric, hypervoxel/braid core, deterministic coarse-graining no-go, dynamic effective topology, morphogenesis, natural-growth, ecological, Navier--Stokes, and Yang--Mills surfaces.

The branch does not claim that the Yijing is a physical quantum system, that the Monster representation has been restricted to the proposed DASHI sectors, that grokking must realise E8 or the Leech lattice, that a graph Laplacian is the whole brain, that divination predicts external facts, or that either Clay problem has been solved.

## Balanced-ternary Yijing carrier

`DASHIYijingTernaryDivinationExact.agda` replaces a binary line carrier by the existing DASHI trit:

```text
negative / zero / positive
```

It proves:

```text
3^3 = 27       ternary trigrams
3^6 = 729      paired ternary trigrams / ternary hexagrams
3^9 = 19683    one 3 x 3 ternary sheet
```

Yin/yang is a context-indexed observation. The same trit can reverse observed polarity under a reversed view. Zero remains unresolved rather than being assigned a universal meaning such as synthesis. Moving positions form a Boolean mask; a moving position applies sign inversion, which fixes zero. A reading retains question context, initial state, moving mask, resulting state, PNF atoms, and authority type.

## Received Yijing relational operators

`DASHIYijingRelationalOperatorsExact.agda` preserves the received four-valued casting surface:

```text
6 = old / changing yin
7 = young / stable yang
8 = young / stable yin
9 = old / changing yang
```

Each casting value has an exact primary polarity, moving-line flag, and resulting polarity. A six-line cast compiles to an initial ternary hexagram, a moving mask, and a resulting hexagram.

The module also includes:

- lower and upper trigram decomposition with exact recomposition;
- the eight received images: heaven, earth, thunder, wind/wood, water, fire, mountain, and lake/marsh;
- an explicit `ternaryBeyondReceivedEight` result for zero-containing DASHI trigrams;
- positions 1 through 6 and their entry, inner-development, threshold, outer-entry, governing-centre, and culmination stages;
- centrality at positions 2 and 5;
- conventional odd/yang and even/yin positional expectations without identifying positional correctness with moral goodness;
- the correspondence involution `1 <-> 4`, `2 <-> 5`, and `3 <-> 6`;
- nonzero opposition, so two zero lines are not falsely classified as opposed;
- reversal, whole-state complement, trigram exchange, and their involution proofs;
- later nuclear extraction `(x1,x2,x3,x4,x5,x6) -> (x2,x3,x4,x3,x4,x5)`.

The nuclear operator is typed as a later interpretive construction rather than asserted to belong to the earliest Zhouyi layer.

## Oriented zero and continuous approach

`OrientedZeroWaveTransitionExact.agda` refines the transition state to

```text
-1, -0, +0, +1.
```

The coarse projection identifies both zero germs:

```text
coarse(-0) = coarse(+0) = 0,
```

while the refined state preserves direction of approach. The finite wave carrier likewise retains side at magnitude zero. This is a path/residual refinement of ternary zero, not a demand that every consumer adopt a four-valued truth carrier.

## Dialectical square symmetry and spiral lift

`DialecticalSheetSpiralExact.agda` gives a literal 3 x 3 sheet with quarter rotation, reflection, and global sign inversion. It proves:

```text
rotation^4 = identity
reflection^2 = identity
negation^2 = identity
```

The lifted state adds historical height and spiral sense. Four rotations return the projected sheet while increasing height by four. Reflection flips spiral sense. Hence recurrence in projection does not erase history:

```text
same projected pattern != same lifted dialectical state.
```

This is a typed screw/helical model, not a Navier--Stokes regularity proof.

## Triadic braid and path residual

`TriadicBraidDialecticExact.agda` gives three ternary strands and adjacent generators `sigma1` and `sigma2`. The finite endpoint action proves the Artin/Yang--Baxter relation:

```text
sigma1 sigma2 sigma1 = sigma2 sigma1 sigma2
```

at the endpoint level. A separate residual retains braid-word kind, crossing count, orientation, and historical level. Thus equivalent endpoints need not erase the path that produced them. The finite swap action factors through the symmetric group and is explicitly not claimed to be a faithful braid-group representation.

## Hypercube, hypervoxel, and hyperfabric tower

`TernaryHypercubeHyperfabricExact.agda` distinguishes:

```text
binary carrier:   2^n hypercube vertices
ternary carrier:  3^n lattice points in the cubical hull
oriented zero:    4^n refined transition microstates
```

It records the scale spine:

```text
3
3 x 3             = 9
3 x 9             = 27
6 x 9             = 54
9 x 9             = 81
9 x 9 x 3         = 243
(9 x 9 x 9) x 3   = 2187 sites
```

Mediated-path, unrestricted-Hamming, and cyclic-phase transition geometries are separate types. Product growth is kept distinct from fixed-base tetration. Principled fibre transitions retain source type, target type, transition kind, and residual preservation.

`TernaryCubeStrataExact.agda` makes the resulting three-dimensional shape exact:

```text
8 vertices
12 edge midpoints
6 face centres
1 cube centre
----------------
27 ternary points
```

Binary points occupy the vertex stratum. Ternary points have the same cubical convex hull but a richer stratified combinatorics containing boundaries, intermediates, and centre.

## Cantor restriction, wheel phase, and diffusion

`TernaryCantorWheelDiffusionExact.agda` separates the full balanced-ternary address space from the polar Cantor restriction:

```text
full depth-3 ternary address count = 3^3 = 27
polar depth-3 address count        = 2^3 = 8
```

It also defines a period-three wheel observation

```text
negative -> zero -> positive -> negative
```

and proves three rotations return the state. This cyclic phase geometry is not identified with the ordered mediated path `negative <-> zero <-> positive`. The module adds finite wheel diffusion and self-similar refinement while explicitly declining to claim a unique standard object universally called the “Cantor wheel”.

## The `19683` / `196883` symmetry candidate

`TernaryMonsterSymmetryCandidateExact.agda` formalises the proposed construction rather than dismissing it as decimal coincidence.

The raw nine-cell permutation representation of `D4` is recorded as

```text
R^9 = 3 A1 + B1 + B2 + 2 E,
```

with dimension nine and no raw `A2` component. An orientation, pseudoscalar, or braid refinement is therefore needed to realise the reflection-odd species.

The five `D4` irrep species are paired with two dialectical orientations:

```text
5 x 2 = 10 sectors.
```

Each proposed sector carries a complete `3^9` configuration fibre. The checked arithmetic is:

```text
10 x 19683 = 196830
196830 + 53 = 196883
47 x 59 x 71 = 196883
```

The full fifteen-prime Ogg list is represented; `47`, `59`, and `71` are Ogg primes, while `53` is not. Finite trial-division data records the primality evidence relevant to `53`, but prime cardinality is not equated with an irreducible representation.

A typed `MonsterRestrictionCandidate` records the proposed bulk-plus-residual shape. Promotion remains blocked until there is a natural action, intertwiner, invariant form, actual restriction/decomposition theorem, graded character, and modular or automorphic result.

## FRACTRAN over SSP channels

`FRACTRANSSPTransitionExact.agda` attaches guarded prime-valuation control flow to the existing `SSP369Ultrametric` address carrier. The state contains exponents for

```text
47, 53, 59, 71,
```

an SSP 3/6/9 address, and an oriented-zero residual. Rules implement:

```text
47 -> 59 -> 71 -> 47
53 -> 47
```

with explicit first-enabled priority. SSP address type is preserved. This is a finite typed FRACTRAN-style example, not a universal program or constructed Monster action.

## Grokking, Fourier modes, E8, and the Leech lattice

`SpectralGrokkingLatticeExact.agda` constructs a three-phase cyclic character carrier and its `3 x 3 = 9` pair space. The three-cycle Laplacian has one constant mode and two degenerate contrast modes. A finite grokking trajectory separates memorisation, circuit formation, and cleanup; cleanup removes irregular components while retaining three symmetry-adapted components.

E8 and Leech are typed as eight- and twenty-four-dimensional exceptional-lattice candidates. No theorem forces either geometry from the finite grokking witness.

## Classical sources of quantum-like appearance

`ClassicalQuantumLikeCoarseGrainingExact.agda` directly reuses the repository's deterministic-microdynamics/non-closed-macroprojection theorem. It adds exact classical examples of:

- noncommuting context updates;
- identical visible zero with distinct latent paths;
- different next observations from those paths;
- symmetry-restricted accessible state counts;
- representation-labelled finite packets.

The boundary leaves the Born rule, complex amplitudes, tensor-product composition, Bell separation, and contextuality inequalities unproved. Context, coarse-graining, and latent path dependence are reconstruction ingredients, not a completed quantum reconstruction.

`DASHIQuantumLikeEntropyOscillatorExact.agda` additionally records:

```text
2^14 = 16384 < 19683 < 32768 = 2^15.
```

Finite mixing is treated as arrival at a stationary distribution rather than quantum condensation. A discrete oscillator is built as a graph-Laplacian contribution plus a potential. Correlation claims require fixed encoding, declared metric, alternative-count correction, a null model, and held-out replication.

## Associative divination and PNF

`AssociativeDivinationPNFExact.agda` distinguishes symbolic casting, cold cues, warm base rates, hot prior information, reader pattern recognition, and participant completion. Feedback updates an explicit reading state. Psychoanalytic/free-associative traces record what is selected, rejected, elaborated, or affectively marked.

PNF constructors keep autobiographical hypotheses separate from external predictions and independent verification. Narrative retrieval is typed across place, story, rhythm, image, kinship, and ecology fibres. This supports multi-index memory without reducing Indigenous knowledge systems to mnemonic tricks or promoting recovered-memory authority.

## Neural representation and Laplacian observation

`NeuralRepresentationLaplacianExact.agda` separates representational geometry, population activation, modulatory dynamics, effective connectivity, Laplacian variation, and coarse observation. The same input evolves differently under inhibited and recurrent regimes. Two distinct microscopic population states have the same fMRI-like regional aggregate while retaining different Laplacian variation.

The graph Laplacian is therefore a relational/diffusion object, not the entire neural system or a complete inverse of coarse measurement.

## Natural-system hyperfabric

`NaturalSystemsHyperfabricExact.agda` cross-pollinates existing DASHI biology and ecology modules through a typed finite architecture. It contains:

- the finite logistic law `x -> x(4-x)`;
- one-step diffusion down a concentration gradient;
- activator--inhibitor reaction and material use;
- bioelectric target repair;
- multiway histories with the same visible endpoint and different residuals;
- forest channels for carbon, nitrogen, water, signalling, pathogens, and competition.

A material transfer is not definitionally altruistic cooperation. Bioelectric state is not a sole morphogenetic cause. One equation is not promoted to a universal natural-system theory. Simard supplies field-transfer provenance; Stamets supplies bounded architectural and restoration-oriented mycelial provenance, with explicit exclusion of universal forest-intention claims.

## Navier--Stokes and Yang--Mills bridge

`NSYMDialecticalFieldBridgeExact.agda` gives a finite vorticity screw motion whose planar phase returns after four steps while axial level rises. It separates strain multiplication from rotation.

The gauge side has a finite plaquette holonomy/curvature witness, a gauge-like all-edge flip preserving the finite curvature bit, a vacuum sector, and a positive finite excitation gap. Representation-labelled packets retain gauge invariance and propagation status as separate fields.

The module does not promote:

- screw motion to three-dimensional Navier--Stokes regularity;
- the right-hand rule to determinism sufficient for the Clay problem;
- a finite lattice gap to continuum quantum Yang--Mills existence and mass gap;
- an irrep label to a complete energy law;
- coarse-graining plus latent paths to all quantum predictions.

## Provenance and validation

`ConsciousAccessRound5SourceAtlas.agda` and `ConsciousAccessRound5ExtendedSourceAtlas.agda` record author, title, venue, year, DOI or an explicit no-DOI/ISBN marker, imported role, and excluded promotion for twenty-three sources. They cover grokking, E8/Leech, monstrous moonshine, Ogg primes, FRACTRAN, logistic dynamics, bioelectric morphogenesis, reaction--diffusion, mycorrhizal transfer, Stamets's mycelial architecture, psychic reading, Freud, narrative memory, Aboriginal memory techniques, Zhouyi history, braid theory, fractal geometry, spectral graph theory, lattice gauge theory, the two Clay statements, and multiway rewriting.

The focused checker is:

```bash
bash scripts/check_conscious_access_round5.sh
```

It first runs the complete round-four checker, scans every round-five Agda module for holes, postulates, unsafe options, unsolved metas, and placeholder right-hand sides, then kernel-checks both:

```text
DASHI/Biology/ConsciousAccessRound5Regression.agda
DASHI/Biology/Everything.agda
```

The workflow installs Nix, resolves `.#agda-with-dashi-deps` from the committed `flake.lock`, prints the actual Agda version, and supplies that exact executable to the checker.