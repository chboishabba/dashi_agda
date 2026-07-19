# NS pair-incidence kernel Schur bridge

## Purpose

This tranche replaces an unnamed “concrete rectangular kernel” obligation with an exact finite construction.

For enumerated source modes, target modes, and contributing mode pairs, the transfer entry is defined by the finite fold

\[
K(r,c)=\sum_{p\in\mathcal P}\operatorname{contribution}(p,r,c).
\]

The weighted row and column sums are then computed directly from this kernel.

## Constructive content

`FiniteWeightedKernelSums.agda` defines:

- finite row and column carriers;
- exact weighted row and column sums;
- proof-relevant pointwise row and column inequalities;
- identity matching for kernels, enumerations, and weights.

`NSPairIncidenceKernel.agda` defines the pair-incidence fold and requires a pointwise identity theorem before it can represent the concrete Biot–Savart transfer kernel.

`NSPairIncidenceSchurBridge.agda` transports exact finite sum certificates into the existing weighted Schur operator theorem through an explicit analytic realization map.

## Productive chain

```text
pair contributions
  -> exact rectangular kernel entries
  -> exact weighted row/column sums
  -> weighted Schur certificate
  -> concrete K01/K10 certificate
  -> C10 * (R0 * C01)
  -> conditional NS frame gap
```

## Remaining frontier

The following remain open:

1. instantiate the pair carrier with the actual Fourier/Biot–Savart mode interactions;
2. prove the concrete transfer entry equals the pair-incidence fold pointwise;
3. prove uniform weighted row and column inequalities over the admissible shell family;
4. prove the low-shell resolvent bound;
5. close the strict product budget below the high-shell diagonal gap.

Coarse shell-angle receipts remain non-promoting unless an explicit representation theorem identifies their kernel, enumerations, and weights with these concrete objects.
