# Round Five event, cyclic, and p-adic renderer continuation

This continuation integrates supplied sections 671–835 as a finite exact Agda theorem spine. It extends the earlier affine-slice, five-class, renderer-parity, graph-to-field, ternary-carry, prefix-LOD, and retained-address modules rather than replacing them.

## Event-generated filament fields

`DASHI/Visualisation/EventFilamentFieldExact.agda` records the typed pipeline

```text
event record
-> positive kernel contribution
-> additive scalar and class fields
-> temporal graph or explicit trajectory
-> ridge/tube observation
-> inverse-density display
```

The module separates full-covariance intent from the finite executable axis-scale witness, corrects the separation-to-sharpness direction, separates bandwidth from boundary steepness, blocks raw signed GELU from being treated as density, and proves exact additive field and class-closure examples.

Time carried as a coordinate or external parameter does not create a thread. A thread requires overlap, explicit trajectories, tangent-aligned support, or a continuous curve-supported measure. Forward temporal edges carry an indexed `Before` witness, and turn cost belongs to a three-event segment rather than one edge.

Binary corner labels and ternary hierarchical labels form a product carrier. A declared two-bit/two-trit family has `4 * 9 = 36` states; neither label is definitionally the other. The phrase “1-adic” remains informal rather than a standard number field.

Inverse density changes observation polarity without introducing negative source mass. Isosurfaces, superlevel regions, and void sublevel regions remain separate types. The ridge boundary records that a one-dimensional ridge in ambient dimension four has three normal directions; it does not promote a slice ridge to an ambient smooth ridge theorem.

## Self-consistent renderer

`DASHI/Visualisation/SelfConsistentEventRendererExact.agda` separates active and passive frame conventions, continuous query coordinates, hierarchical addresses, positive kernels, base density, feedback sharpness, ambiguity attenuation, class composition, calibration, colour, luminance, and opacity.

The supplied feedback is implicit. The implementation therefore provides both:

```text
base pass -> density band -> bounded sharpness -> second pass
```

and a complete finite fixed-point example with a unique fixed state reached in two iterations. The finite result is not promoted to a continuum Banach contraction theorem.

Shared-prefix affinity increases with shared depth. The legacy decreasing table is retained only as a counterexample. Product and additive couplings between continuous and ultrametric affinity are distinct modelling choices.

Uniform ambiguity attenuation changes total visibility but cancels from normalised class composition. Class-specific attenuation can change composition. A void channel provides exact denominator closure. Frame-maximum, fixed-reference, and robust calibration are distinct modes.

Opacity proportional to density renders opaque threads; inverse luminance renders dense threads dark and voids bright. The two channels are not conflated. An exact finite counterexample proves that nonlinear CMYK conversion is not an additive fixed matrix map.

Mass-preserving sharpening is represented by distinct broad and sharp kernels with equal total mass. Hierarchical gating can reduce visible mass; explicit renormalisation restores the declared event mass.

## Ternary cyclic algebra and dialectical annotation

`DASHI/Biology/TernaryCyclicDialecticExact.agda` reuses `TriadicCarryResidualExact.agda` and keeps three operators distinct:

```text
cyclicAdd3       : Z/3 x Z/3 -> Z/3
tex              : bespoke balanced-trit operator
addCarry3        : trit x trit x carry -> digit x carry
```

The exact group laws, inverse, failure of Boolean self-cancellation, one-hot cyclic-convolution exactness, balanced carry reconstruction, and involution compatibility are retained.

A nontrivial automorphism swaps residues one and two while preserving addition. Therefore labels such as opposition and sublation are external semantic annotations, not intrinsic residue meanings. Four-valued positive/negative evidence remains a separate carrier from the three residues.

The corrected priority-disjoint `tex` table is proved unequal to cyclic addition and has explicit failures of commutativity and associativity. Triadic truth, designated values, truth order, cyclic phase, and dialectical labels are distinct types.

The soft layer uses cyclic convolution of nonnegative three-channel masses. It is exact on one-hot states and preserves total mass multiplicatively in the declared finite sample. A three-root phase character transports cyclic addition to phase multiplication.

## Renderable p-adic reasoning field

`DASHI/Biology/RenderablePadicReasoningFieldExact.agda` extends the existing prefix-cylinder and render bridge modules.

Project glyph strings, ordinary decimals, and canonical ternary prefixes are separate syntax classes. Truncation is an exact quotient projection but has a concrete information-loss witness: different child prefixes share one parent.

A depth-two-resolved kernel is exactly constant on two depth-three addresses that differ only in their final digit. This makes prefix caching a theorem of the declared kernel, not only an implementation optimisation.

The corrected finite counts are:

```text
3^6 = 729   = 9^3
3^9 = 19683 = 27^3
```

The depth-nine Morton-like map consumes digits `0,3,6` for `x`, `1,4,7` for `y`, and `2,5,8` for `z`; the canonical sample maps to voxel `(15,23,1)`.

LOD is retained digit depth. Parent mass is the sum of child masses, while a uniform-density parent satisfies the division-free certificate `3 * parent = sum children`. Class masses are aggregated before normalisation; a finite unequal-mass counterexample shows why averaging child weights is not equivalent.

Adaptive refinement, sparse prefix nodes, MIP, straight-alpha, additive-emission, and isosurface modes are typed separately. Per-voxel self-normalisation maps every positive density to the same opacity in the counterexample; shared calibration retains contrast.

The finished finite object retains state carrier, measure/activity/class declarations, quotient depth, observation geometry, colour and opacity maps, and exact address metadata. The final image remains a non-injective observation, not the primary reasoning state.

## Provenance

`DASHI/Visualisation/EventPadicSourceAtlas.agda` records author, title, venue, year, DOI or an explicit no-DOI marker, imported role, and excluded promotion for ten records:

- Bernard W. Silverman, *Density Estimation for Statistics and Data Analysis*, DOI `10.1201/9781315140919`;
- Umut Ozertem and Deniz Erdogmus, *Locally Defined Principal Curves and Surfaces*, JMLR 12, no DOI assigned;
- Genovese, Perone-Pacifico, Verdinelli, and Wasserman, *Nonparametric Ridge Estimation*, DOI `10.1214/14-AOS1218`;
- Marc Levoy, *Display of Surfaces from Volume Data*, DOI `10.1109/38.511`;
- Nelson Max, *Optical Models for Direct Volume Rendering*, DOI `10.1109/2945.468400`;
- Stefan Banach, *Sur les operations dans les ensembles abstraits et leur application aux equations integrales*, DOI `10.4064/fm-3-1-133-181`;
- G. M. Morton, *A Computer Oriented Geodetic Data Base and a New Technique in File Sequencing*, no DOI assigned;
- Jean-Pierre Serre, *A Course in Arithmetic*, DOI `10.1007/978-1-4684-9884-4`;
- Alain M. Robert, *A Course in p-adic Analysis*, DOI `10.1007/978-1-4757-3254-2`;
- David Williams, *Probability with Martingales*, DOI `10.1017/CBO9780511813658`.

## Integration and validation

The cumulative boundary and regression are:

```text
DASHI/Visualisation/EventPadicContinuationBoundary.agda
DASHI/Visualisation/EventPadicContinuationRegression.agda
```

They are imported by both domain roots and by `Round5CompleteBoundary.agda`. The combined source boundary verifies the additional count of ten. `scripts/check_unification_round5.sh` scans every new file and targets the continuation regression, visualisation root, biology root, complete Round Five boundary, foundations root, and unified root.

No continuum ridge-recovery theorem, statistical consistency result, Banach contraction for the full renderer, complete p-adic analysis library, canonical Euclidean embedding, physical optical model, or observed continuous thought trajectory is claimed by the finite sources.
