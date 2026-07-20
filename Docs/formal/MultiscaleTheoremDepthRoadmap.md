# Multiscale theorem-depth roadmap

This tranche implements the highest-value next sequence after the multiscale residual/MDL cross-pollination work. It deliberately prioritises theorem depth and evidence governance over adding more application domains.

## 1. Canonical repository spine

`DASHI.Core.CanonicalSpineRegistry` records the canonical owners for:

- balanced ternary;
- dependent support/sign factorisation;
- multiscale carrier, residual, kernel, symmetry, and MDL accounting;
- 369 prefix ultrametric geometry;
- MDL/Lyapunov contracts;
- basin-local descent;
- approximate naturality;
- reversible/observational splitting;
- coding targets;
- discrete-continuum targets.

The registry marks parallel definitions as disallowed. It does not pretend to statically inspect every module or prove a repository-wide compile. Those remain CI and consolidation tasks.

## 2. Concrete ternary C/P/R instance

`DASHI.Core.TritCPRMultiscaleInstance` instantiates the generic multiscale core with a nested ternary tower:

```text
TritTower 0       = Trit
TritTower (j + 1) = Trit × TritTower j
```

At each successor level:

- `P` forgets the new leading trit;
- `L` inserts neutral `0`;
- `R` records the forgotten leading trit;
- reconstruction pairs the residual with the coarse state.

Therefore:

```text
join (split x) = x
```

is proved for the concrete tower. The module also supplies rankwise sign inversion, its involution theorem, an identity kernel tower, and an explicit symmetry action.

This closes the abstract-to-concrete seam for one canonical nested ternary hierarchy. It does not claim that every older operational C/P/R implementation has already been proved extensionally equal to this owner.

## 3. Basin-local descent

`DASHI.Core.BasinFiniteDescent` replaces an unjustified global contraction claim with a local theorem interface:

```text
inside Basin x:
  cost (step x) < cost x
  or Fixed x
```

It also requires basin preservation and soundness of fixed states. A finite descent receipt contains an explicit endpoint, fixed-point proof, and endpoint cost bound.

A natural-number countdown system provides a concrete inhabited example. This shows that the contract is constructive and usable; it is not evidence that every DASHI kernel satisfies it.

The next application theorem is to instantiate this interface for the actual selected DASHI kernel and an admissible basin.

## 4. Approximate multiscale commutation

`DASHI.Core.ApproximateMultiscaleNaturality` adds a scale-indexed metric and the quantitative law

```text
d(P (K_{j+1} x), K_j (P x)) <= epsilon_j(x).
```

Exact kernel naturality embeds into this structure with zero error. A two-leg accumulation theorem proves that adjacent error bounds add by the metric triangle inequality.

A `ControlledErrorFamily` then names the remaining analytic obligations:

- a scale-only global bound;
- pointwise domination;
- vanishing error;
- summability.

The last two remain proposition slots because they require a chosen analytic number system and limit theory.

## 5. MDL, source coding, and rate-distortion

`DASHI.MDL.MultiscaleCodingTargets` supplies an exact adapter from a selected multiscale level into the existing canonical `MDLFunctional` owner. This removes a parallel-MDL seam.

It then separates exact reconstruction from stronger coding claims:

- source distribution/weights;
- uniquely decodable code;
- Kraft admissibility;
- entropy lower and expected-length upper bounds;
- finite-precision coder correctness;
- distortion budget;
- matched-quality candidate/baseline comparison;
- side-information accounting.

Every `ResidualCodec` already inhabits the exact decoder theorem. Shannon and rate-distortion results remain open until their probability and coding witnesses are supplied.

## 6. Reversible versus dissipative kernels

`DASHI.Core.ReversibleDissipativeKernelSplit` defines:

- reversible evolution with a two-sided inverse;
- idempotent observation/selection;
- a full step factorised as observation after evolution.

It proves reversible evolution is injective and supplies an identity example. The boundary explicitly rejects automatic identification of:

- contraction with unitarity;
- observation with global information preservation;
- MDL descent with Hamiltonian evolution.

This is the formal home for a future decomposition such as `K = M o U`.

## 7. Discrete-to-continuum and physics targets

`DASHI.Physics.DiscreteContinuumKernelTargets` records the exact proof package required for a physical continuum result:

- spatial and temporal discretisation family;
- embedding into continuum states;
- boundary conditions;
- physical units map;
- local consistency;
- stability;
- compactness/completeness;
- generator identification;
- convergence.

Separate targets cover:

- first-order wave equations and energy/dispersion control;
- quantitative MDL/action asymptotics and minimiser convergence;
- intrinsic derivation of dimension, signature, causal cone, connection, curvature, and source coupling.

These are theorem-facing contracts. Generic continuum convergence, automatic metric selection, and automatic MDL/action equivalence remain false.

## 8. Flagship empirical gate

`scripts/validate_multiscale_flagship_receipt.py` validates a JSON receipt for exactly one chosen flagship:

- triadic video codec;
- observer-conditioned wave transport;
- sparse vorticity.

The receipt must include:

- exact roundtrip;
- held-out evaluation;
- a declared baseline;
- matched quality metrics;
- runtime and peak memory;
- side-information accounting;
- no test leakage;
- four ablations: multiscale prediction, ultrametric context, symmetry quotient, and temporal/transport residual.

The gate rejects universal-superiority claims and blocks Shannon or continuum promotion unless their corresponding theorem flags are supplied.

The validator does not run the experiment. It makes the experiment auditable and fail-closed.

## 9. Focused regression surface

`DASHI.Core.MultiscaleTheoremDepthRegression` imports the tranche and checks:

- concrete ternary projection and residual values;
- exact split/join reconstruction;
- rankwise inversion involution;
- the countdown fixed point;
- reversible/dissipative claim boundaries;
- physics non-promotion boundaries;
- canonical-owner registration.

## Remaining theorem leaves

The major remaining work is now narrower:

1. Prove an extensional adapter from historical operational C/P/R implementations to the canonical nested ternary owner.
2. Instantiate basin-local strict descent or a finite descent certificate for the actual selected DASHI kernel.
3. Supply a meaningful metric and prove vanishing or summable multiscale commutation defects.
4. Implement and verify the real finite-precision entropy coder against a declared source model.
5. Run one flagship benchmark and produce a passing receipt.
6. Choose one discrete physical kernel and inhabit consistency, stability, generator-identification, and convergence fields.
7. Relate MDL to physical action only through a quantitative asymptotic theorem.
8. Run the focused Agda modules and then the repository-wide `DASHI/Everything.agda` check.

The architecture has therefore moved from a broad shared vocabulary to a concrete ternary instance, local convergence contract, quantitative scale-error interface, canonical MDL adapter, explicit dynamics split, and executable evidence gate. The unresolved work is now substantive theorem inhabitation and measurement.
