# Selected-kernel theorem and evidence closure

This tranche follows the generic theorem-depth interfaces with concrete inhabitants.

## 1. Selected strict descent

The selected step is the repository's existing finite shift-pressure perturbation kernel:

```text
startPerturbation -> nextPerturbation -> zeroPerturbation -> zeroPerturbation
```

Its existing finite norm is:

```text
start = 2
next  = 1
zero  = 0
```

`DASHI.Physics.Closure.SelectedShiftStrictDescent` proves strict descent at each nonfixed state and supplies exact one-step and two-step endpoint receipts. This result concerns the implemented three-state finite shift sector. It is not a global contraction theorem for every DASHI kernel or carrier.

## 2. Vanishing and summable scale defects

`DASHI.Physics.Closure.SelectedShiftScaleDefects` places the selected shift step at every level of a constant carrier tower with identity projection and lift. The two naturality paths are definitionally equal:

```text
P (K x) = K (P x)
```

Therefore every commutation error is zero, every finite partial error sum is zero, and the defect family is exactly vanishing and summable.

The supplied zero pseudometric measures only the already-proved naturality defect. It is not promoted as a state-separating physical metric.

## 3. Verified finite-precision coder

`DASHI.Codec.VerifiedFiniteTritCoder` supplies a concrete two-bit balanced-ternary code:

```text
neg -> 00
zer -> 01
pos -> 10
11  -> invalid/reserved
```

The module proves:

- encode/decode roundtrip for all three trits;
- malformed reserved-word rejection;
- encoder injectivity;
- exhaustive roundtrip for all 27 ordered trit triples;
- fixed six-bit width for the uncompressed triple baseline.

This closes finite machine-word correctness. It does not prove rANS arithmetic, entropy optimality, or compression superiority.

## 4. Executable flagship benchmark receipt

`scripts/run_triadic_flagship_benchmark.py` executes a deterministic held-out ternary residual-plane benchmark.

The candidate pipeline uses:

- temporal modulo-three residuals;
- coarse group prediction plus exact residuals;
- blockwise sign-inversion quotienting;
- previous-symbol context buckets;
- support/sign bitstreams compressed with Python zlib.

The baseline uses fixed two-bit trit packing followed by the same zlib backend. Both paths are decoded and compared exactly with the held-out source.

The workflow measures:

- encoded bytes and bits per symbol;
- exact symbol-error rate;
- median encode/decode runtime;
- peak traced memory;
- all four required ablations;
- side-information-inclusive payload size.

The resulting JSON is validated by `validate_multiscale_flagship_receipt.py` and uploaded as a workflow artifact. It is a real measured synthetic microbenchmark, not evidence of real-world video or universal codec superiority.

## 5. Selected discrete-to-continuum theorem

`DASHI.Physics.ConstantZeroModeContinuumTheorem` inhabits the discrete-to-continuum interface for the stationary spatially constant zero-momentum wave sector.

At every spatial and temporal resolution there is one represented constant state. The discrete kernel, embedding, and continuum zero-mode evolution are identical, so local consistency, stability, generator identification, and convergence hold definitionally.

This theorem closes one selected sector only. It does not cover:

- nonconstant spatial fields;
- nonzero momentum;
- numerical dispersion;
- a nontrivial Laplacian;
- convergence of the general observer-conditioned or sparse-wave solver.

## Remaining frontier

After this tranche, the next nondegenerate leaves are:

1. strict descent or invariant-region control for a larger operational kernel;
2. a state-separating analytic metric with nonzero but summable scale defects;
3. verified finite-precision rANS or arithmetic coding;
4. real-world video/audio/fluid datasets and external baselines;
5. a nonconstant wave mode with quantitative consistency, stability, and dispersion convergence.
