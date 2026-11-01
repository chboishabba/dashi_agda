# PNF spectral covariance geometry

This module formalises the automatic numerical layer discussed for PNF, SSP,
and Monster-adjacent symbolic carriers.

## Coordinate discipline

A token, word, concept, or predicate may receive a stable natural-number code.
The code is an identifier and sparse-matrix column index; it is not the
concept's meaning and is not an activation score.

Continuous values are separately typed by role:

- activation score;
- covariance weight;
- spectral weight.

The separation prevents integer atom IDs from being interpreted as semantic
magnitudes.

## Automatic pipeline

The intended computation is:

```text
PNF atoms / predicates
  -> explicit activation surface X
  -> centred covariance surface C
  -> anonymous spectral decomposition
  -> random-matrix null-band classification
  -> eigenvalue shrinkage / retention
  -> cleaned covariance reconstruction
```

Eigenmodes are anonymous ordinal coordinates.  No manual naming or narrative
interpretation is required by the type.  The eigenvectors are temporary
basis-change coordinates used to filter and reconstruct the covariance
operator.

## Structural views

The same explicit predicate basis supports:

- sparse predicate graphs;
- adjacency, degree, and Laplacian operators;
- temporal transport kernels;
- motif participation and compression receipts;
- meet/join refinement lattices.

These are views of typed PNF structure, not replacements for it.

## Vector-database boundary

Dense embeddings are admitted only as retrieval hints.  They are not:

- the PNF coordinate basis;
- covariance evidence;
- structural promotion receipts.

Embedding storage is therefore optional peripheral infrastructure.  The
primary numerical geometry is derived from explicit PNF activations and their
receipt-governed interactions.

## Current proof boundary

`PNFSpectralGeometry.agda` provides the carrier and obligation surfaces.  A
concrete backend must still instantiate:

- the scalar structure;
- finite-sample centring and covariance arithmetic;
- a spectral decomposition algorithm and exact reconstruction proof;
- a chosen random-matrix null model and its band receipt;
- a shrinkage rule and filtered reconstruction proof.

No empirical mode is promoted merely because its eigenvalue exceeds a null
band; that result remains a candidate structural signal until the surrounding
PNF receipt and stability gates are supplied.
