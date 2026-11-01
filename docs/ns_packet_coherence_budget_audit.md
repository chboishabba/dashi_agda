# NS packet coherence-budget audit

This lane follows the physical transfer and residence audits with a geometric
hypothesis search.  It does not wait for an external proof: it computes the
candidate quantities needed to discover, refine, or falsify a depletion-budget
argument while Agda proves the exact reductions that are already available.

## Candidate proof currency

The instantaneous universal `Gamma < 1` target has been replaced by a bounded
coherence budget.  In parabolic time

```text
tau = nu 2^(2K) t
```

we search for

```text
d A_K / d tau + kappa 1_{Gamma_K >= lambda} <= R_K.
```

The current candidate is

```text
A_K = packet-enstrophy-weighted (xi_K dot e_1,K)^2,
```

where `xi_K` is the target-shell vorticity direction and `e_1,K` is the top
strain eigenvector.  It is automatically bounded between zero and one.

If the positive remainder has a finite integral, integrating this inequality
bounds dangerous parabolic residence.  The exact algebraic composition is
proved in

```text
DASHI/Physics/Closure/NSCoherenceBudgetResidenceReduction.agda
```

rather than represented by a status Boolean.

## Computed physical quantities

`scripts/ns_packet_coherence_budget_audit.py` consumes the checkpoint JSON from
`scripts/ns_shell_angle_residence_audit.py` and the referenced `raw_hat` states.
For each checkpoint it computes:

- the dealiased full velocity gradient;
- the target-shell velocity gradient, vorticity, and strain tensor;
- ordered strain eigenvalues `lambda1 >= lambda2 >= lambda3`;
- alignment weights `alpha_i = (xi dot e_i)^2`;
- the exact numerical identity
  `xi dot S xi = sum_i lambda_i alpha_i`;
- the positive middle-eigenvalue stretching channel;
- the pressure Hessian from
  `Delta p = -partial_i u_j partial_j u_i`;
- the trace-free pressure-Hessian mixing term `e2 dot Hess(p)_tf e1`;
- the corresponding regularized eigenframe-rotation proxy
  `(e2 dot Hess(p)_tf e1)/(lambda1-lambda2)`;
- the inviscid vorticity-direction turnover proxy
  `|S xi - (xi dot S xi) xi|`;
- a rotationally invariant quasi-2D defect
  `sigma_min(grad u_K)^2 / |grad u_K|_F^2`;
- the three middle-eigenvalue branches:
  1. `lambda2 <= 0`;
  2. `lambda2 > 0` with small `alpha2`;
  3. `lambda2 > 0` with substantial `alpha2`.

The branch trichotomy and its completion by turnover, loss of packet tightness,
or viscous absorption are formalized in

```text
DASHI/Physics/Closure/NSMiddleEigenvalueDangerFork.agda
```

The exact finite shell/angular near-versus-tail partition is proved in

```text
DASHI/Physics/Closure/NSShellAngularTransferPartition.agda
```

so signed class aggregation can be connected to a future analytic tail bound
without changing the partition logic.

## Candidate remainder search

For adjacent saved checkpoints the script forms a finite-difference estimate of
`dA_K/dtau`.  It then sweeps `lambda` and `kappa` against a configurable candidate
remainder made from:

```text
positive pressure-eigenframe rotation
+ shell/angular tail mass
+ branch-III middle-channel mass.
```

The coefficients are explicit command-line discovery parameters.  Passing this
finite test is not theorem authority; failing it is useful evidence against the
candidate budget or its chosen coefficients.

## Example

First run the full shell/angular residence audit.  Then run:

```bash
python scripts/ns_packet_coherence_budget_audit.py \
  --residence-json /tmp/ns-shell-angle-residence.json \
  --output-json /tmp/ns-packet-coherence-budget.json \
  --gamma-thresholds 0.5,0.9,1.0 \
  --kappa-candidates 0.01,0.05,0.1,0.25 \
  --middle-alpha-threshold 0.2 \
  --pretty
```

For a genuine cutoff-uniformity experiment, repeat the underlying trajectory at
several Galerkin cutoffs and combine the checkpoints.  The output reports a
cutoff envelope but leaves `cutoff_uniform_authority = false`.

## Mathematical frontier exposed by this implementation

The remaining analytic work is now split cleanly:

1. instantiate the exact shell/angular class decomposition for the physical
   Fourier packet;
2. prove a cutoff-uniform tail estimate;
3. derive the localized evolution identity for `A_K`, including packet
   commutators and viscous terms;
4. prove an integrated absorption estimate for the positive pressure-Hessian,
   commutator, and cutoff remainders;
5. prove that dangerous `Gamma_K` forces a positive amount of local depletion;
6. pass the resulting residence estimate through profile extraction and the
   continuum limit.

The implementation actively searches steps 3--5.  It does not assert that the
finite-difference proxy is the exact material derivative or that the regularized
pressure-eigenframe term has a uniform sign.
