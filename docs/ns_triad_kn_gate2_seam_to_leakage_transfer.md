# NS triad Gate 2 seam-to-leakage transfer

Date: 2026-07-02

## Status

Gate 1 and Gate 2 are distinct.

- Gate 1 is the seam-local signed domination / helical-coupling theorem.
- Gate 2 is the transport step from that seam certificate to the exact
  normalized leakage operator used by the downstream cascade lane.

This note is fail-closed. It does not claim that the transfer is already
proved.

The current EP4 surface is only a seam-local closure model. In particular,
the local choice `outside-seam-pollution = 0` is not yet the full outside-seam
no-pollution theorem for the exact leakage operator.

## Exact downstream object

The exact downstream leakage object is the normalized Gram operator

`K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)`

from [docs/ns_triad_kn_KN_exact_algebraic_definition.md](ns_triad_kn_KN_exact_algebraic_definition.md).

The current leakage lane already uses that object, not a separate proxy:

- [docs/ns_triad_kn_cross_shell_leakage_bound.md](ns_triad_kn_cross_shell_leakage_bound.md)
- [docs/ns_triad_kn_gram_coercivity_target.md](ns_triad_kn_gram_coercivity_target.md)

So Gate 2 is not “invent the leakage operator.” It is “prove that the seam
Schur/helical certificate controls this exact `K_N(A)` lane with uniform
margin.”

## Upstream Gate 1 carrier

On the seam block `C = {shells N-1, N}`, Gate 1 works with the Schur/signed
carrier

`S_C = L_good - L_bad`

and equivalently the signed domination form

`Q_N = 2 L_good - 3 L_bad`.

The live uniform target is:

`3 L_bad <= 2 L_good` on `1_C^perp`

or equivalently

`rho_N = sup_(x ⟂ 1_C) x^T L_bad x / x^T L_good x <= rho_* < 1`.

Numerically, the helical relative-bound route now supports this carrier at
`N = 6, 8, 10, 12, 14, 16`, but only as a finite-shell certificate.

## Gate 2 statement

Gate 2 must prove that the upstream seam certificate is the same domination
mechanism needed by the exact leakage operator.

The target shape is:

`Gate 1 seam PSD / domination`
`=> exact K_N(A) cross-shell leakage contraction`

with no hidden loss that destroys the strict margin below `1`.

Concretely, the transfer has to justify a statement of the form

`L_cross,N <= rho_* D_good,N`

or whichever exact normalized leakage inequality the downstream cascade route
consumes, on the same admissible-profile class used to define `K_N(A)`.

## Four open transfer obligations

### G2-A. Normalization agreement

Show that the seam/helical operator is the same normalized object that feeds
the `K_N(A)` leakage lane, or is uniformly comparable to it.

Safe target:

`Q_N^leakage <= C_norm Q_N^seam`

with uniform `C_norm`, ideally `C_norm = 1`.

The exact carrier/normalization split for this first comparison step is written
separately in
[docs/ns_triad_kn_gate2a_normalized_carrier_agreement.md](ns_triad_kn_gate2a_normalized_carrier_agreement.md).

Current state: open.

The first live sublemma inside G2-A is now installed as a concrete audit
surface rather than only prose. For dense seam shells, the Schur audit can now
compare

`Schur(L_abs)` versus `L_good`

and

`Schur(L_neg)` versus `L_bad`

on `1_C^perp`, recording both exact-identity defects and observed two-sided
quadratic-form bounds. That surface lives in
`scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py` behind

`--audit-gate2a-schur-sign-split-comparison`.

So the next Gate 2-A proof target is now exact and local:

1. decide whether naive restriction identities fail,
2. if they fail, extract uniform two-sided comparison constants,
3. then show those constants preserve the strict `< 1` Gate 1 margin.

That first margin ledger has now also been tried in its bluntest form on
`N = 6, 8, 10`: combine the observed seam `rho_N` with the worst-case
comparison quotient `C_neg^+ / c_abs^-`. The resulting upper bounds land
around `17.7`, `17.7`, and `20.5`, so the coarse transport route fails badly.

That is important because it narrows the remaining theorem shape:

- the comparison theorem itself is still live,
- but Gate 2 will not close through a naive worst-case quotient ledger.

The live next ansatz is therefore a structured transport:

- extremizer-aware,
- quotient-aware,
- or otherwise finer than the raw `C_neg^+ / c_abs^-` route.

### G2-B. Schur transport

Show that the Schur elimination of shell `1` is the exact reduction used by
the leakage mechanism, not just an audit artefact.

Safe target:

`M >= 0  <=>  S_C >= 0`

for the same carrier and normalization that enter the downstream `K_N(A)`
bound.

Current state: locally true on the seam audit block, but not yet transported as
the exact leakage theorem.

### G2-C. Margin preservation

Show that the Gate 1 margin survives the transfer constants:

`rho_transfer <= F(rho_*, C_norm, C_schur, C_weights) < 1`.

This is the real danger in Gate 2. A numerically comfortable seam bound is not
useful if the transport multiplies it by a constant that crosses `1`.

Current state: open.

The current sharpened reading is:

`coarse margin preservation route ruled out on tested dense shells`

but

`structured margin preservation route still open`.

The strongest current structured candidate is an extremizer-aware transport on
the Gate 1 near-extremizer family rather than a global worst-case operator
bound. Numerically, the directional transported ratio is observed near `0.168`
on `N = 6, 8, 10`, which is far below `1` and dramatically smaller than the
coarse worst-case transport ledger.

### G2-D. No missing outside-seam pollution

Show that modes or interactions omitted from the seam certificate do not
reintroduce an uncontrolled bad term in the actual leakage operator.

Safe target:

`outside-seam contribution <= absorbed good term`

uniformly in `N`.

Current state: open.

## What is already available

These upstream/downstream pieces are already fixed:

1. The exact normalized Gram object `K_N(A)` is canonicalized.
2. The sampled cross-shell leakage lane is already phrased in that exact
   object.
3. The denominator separation `B_cross = 0` is structurally proved for the
   forced-tail leakage rows.
4. The seam Schur/helical certificate is numerically stable across
   `N = 6, 8, 10, 12, 14, 16`.

So Gate 2 is a transport theorem between two already identified objects. It is
not a search problem and not a compute bottleneck.

## Current receipt boundary

Use the following state:

```text
normalizedGramToHelicalSchurAgreementRecorded = true
seamCarrierMatchesLeakageLaneRecorded = true
gate2TransferSurfaceWritten = true

gate2aCertificateAvailable = true                                   # Gate 2-A proof plan installed
gate2aConcreteSeamLocalClosureModel = true                          # local EP4 model installed
gate2aSeamLocalMarginProofCarried = true                            # seam-local <= 1/4 proof carried
normalizedGramToHelicalSchurExtremizerAgreementStated = true        # Extremizer agreement theorem stated
normalizedGramToHelicalSchurExtremizerAgreementNumericallySupported = true  # θ_N ≈ 1/6 supports it
leakageTransferMarginNumericallySupported = true                    # θ_N ≈ 1/6 supports margin

normalizedGramToHelicalSchurAgreementProved = false
schurCertificateTransfersToLeakageOperator = false
leakageTransferMarginPositive = false
outsideSeamNoPollutionProved = false
gate2ConditionalTheoremProved = false

gate2ExactKNAOperatorTransferProved = false
outsideSeamNoPollutionAnalyticallyProved = false
gate2ExactTransferConditionalTheoremProved = false
```

The boundary is:

- local seam principal/defect budget: installed
- local seam outside-pollution zero budget: carried on the seam-local model
- exact seam-to-leakage transfer theorem on the true `K_N(A)` carrier: open

## Current route split

The clean state is now:

1. Gate 1:
   prove uniformly that the seam signed/helical certificate closes.
2. Gate 2:
   prove that the exact `K_N(A)` leakage lane is controlled by that same seam
   certificate with strict margin preserved.
3. Gate 3:
   convert the transported leakage contraction into the actual
   cascade/residue/stretching inequality.

So after Gate 1, the next live theorem is not PDE regularity and not any
external promotion surface. It is the exact seam-to-leakage transport theorem.

## Immediate roadmap

The implemented order was:

1. Fix the defect-ledger arithmetic/import surface.
2. Prove the cross/pure/combined near-extremizer defect estimates.
3. Realize cone-width scaling and the quarter-margin ledger on the NS seam.
4. Consume those into the cone-budget receipt and quotient-aware transport proof.
5. Close EP4 with outside-seam pollution fixed to `0#`.
6. Transfer the exact local leakage inequality into the seam-to-leakage receipt.

## Live Boolean Map

The main closure booleans are now:

- `crossEstimateProved = true`
- `pureEstimateProved = true`
- `combinedEstimateProved = true`
- `crossDefectLinearInConeWidthProved = true`
- `pureDefectQuadraticInConeWidthProved = true`
- `quarterMarginCompatibilityProved = true`
- `combinedDefectBudgetProved = true`
- `principalTermBounded = true`
- `crossDefectBounded = true`
- `pureDefectBounded = true`
- `defectBudgetSubcritical = true`
- `defectTermsUniformlyBounded = true`
- `quotientAwareTransportProved = true`
- `ep4DirectionalMarginUniformlyClosed = true`
- `ep4OutsideSeamPollutionAbsorbed = true`
- `ep4ProofConstructed = true`
