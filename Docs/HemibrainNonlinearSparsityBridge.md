# Hemibrain nonlinear sparsity bridge

This lane extends the abstract atomic → affine/local → nonlinear → exploded
pipeline into the theorem surfaces needed by the dashiBRAIN hemibrain work.

## Modules

- `FiniteWeightedThresholdGraph.agda`
  - finite node enumeration;
  - weighted adjacency and baseline/null operator;
  - concrete residual sum;
  - deadzone classifier;
  - exact graph-kernel instance and implementation correspondence.

- `QuantitativeNonlinearSparsity.agda`
  - finite counting interface;
  - `Defect ⊆ LowMargin` implies
    `count Defect ≤ count LowMargin`;
  - sparse low-margin certificates transfer to sparse defect certificates.

- `ExplodedGraphGeometry.agda`
  - paths and exact distances;
  - signed induced edges and components;
  - largest signed component certificate;
  - boundary shells;
  - single-source and multi-source affiliation;
  - neutral islands and defect shells.

- `ThresholdKernelRenormalisation.agda`
  - fine/coarse kernel maps;
  - commutation defect;
  - locality-preserving and locality-destroying witnesses;
  - exploded-support preservation and all-positive-collapse certificates;
  - finite coarse-run certificate surface.

- `L1Separation.agda`
  - ordered scalar and l1-style objective surface;
  - separable proximal representation;
  - theorem that any non-coordinate DASHI witness excludes a separable l1
    proximal representation;
  - corresponding scalar-threshold/ReLU exclusion.

- `ThresholdCSPCores.agda`
  - restricted satisfiability;
  - minimal inconsistent cores;
  - repair/removal sets;
  - explicit certificate required before identifying observed defects with
    minimal cores.

- `BiologicalEvidenceBridge.agda`
  - neuron metadata;
  - enrichment and perturbation evidence;
  - typed biological interpretation claims;
  - no constructor from geometry alone to a biological claim.

- `HemibrainRunCertificates.agda`
  - random-block, degree-binned, ROI, hop-radius and degenerate voxel receipts;
  - each receipt is explicitly particular-run data, not a universal theorem.

## Main theorem chain

For a finite weighted graph `G`, baseline `B`, ternary state `s`, and deadzone
classifier `D`, the concrete residual is

```text
h_s(x) = Σ_y ((A(x,y) - B(x,y)) * embedTrit(s(y)))
```

and the graph kernel is definitionally

```text
K_G,D(s)(x) = classify_D(h_s(x)).
```

Kernel closure is exactly satisfaction of all local threshold clauses.  Under a
`MarginControl` certificate and decidable low-margin membership,

```text
KernelDefect(K,s) ⊆ LowMargin
```

and the finite counting interface yields

```text
count(KernelDefect(K,s)) ≤ count(LowMargin).
```

The final claim `count(LowMargin) ≪ count(X)` remains a supplied empirical or
application theorem, never a consequence of thresholding alone.

## Geometry and coarse-graining

Exploded graph geometry is now represented by signed components, exact graph
distances, shells, neutral islands and source affiliations.  Fine/coarse maps
carry a separate commutation defect:

```text
q(K_fine(s)) != K_coarse(q(s))
```

when the square fails.  Locality preservation, locality destruction,
commutation and all-positive collapse are separate certificates.  No theorem
claims that destroying locality always forces collapse.

## l1 and ReLU boundary

The mechanised theorem excludes separable coordinate-wise proximal maps and
scalar threshold/ReLU rules whenever a non-coordinate witness exists.  It does
not exclude graph-coupled convex objectives whose proximal map itself depends
on adjacency.

## SAT and biological boundary

A violated kernel clause is not automatically a minimal inconsistent core.
Minimality and restricted unsatisfiability require a `DefectCoreCertificate`.
Likewise, neutral or defect geometry does not automatically imply buffering,
developmental conflict, homeostatic control or disease sensitivity.  A
`SupportedBiologicalClaim` must carry empirical evidence.
