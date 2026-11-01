# Navier-Stokes Analytic State

Updated: `2026-09-13`

Status: Paper 1 now follows the modern same-object/direct-companion proof spine.
The live analytic producer is the cutoff-uniform commutator-only spacetime
budget R568.  The current local proof-search frontier is the same-output
between-partner/P3 separation problem feeding R211.  The June A1-A9
ESS/Abel-defect route remains retained below as a historical/alternative route.

## Canonical live chain

```text
literal periodic Galerkin NS
  -> signed/helical commutator geometry
  -> same-output physical residual / P3 separation
  -> literal R406/direct companion
  -> R568 CommutatorOnlySpacetimeBudget568
  -> R572 direct leaf-A compiler
  -> R503 DirectOffDiagonalBudget / R415 consumer
  -> critical-barrier consumer
```

The exact status distinctions are:

```text
C_direct / integrated direct companion       constructed
R568 commutator-only spacetime producer      open
R572 compiler                                constructed given its listed receipts
R503 R500->R415 compiler surface             constructed
R503 direct off-diagonal analytic payment    open until supplied by a producer
P3 same-output separation producer           open
Clay/global-regularity promotion              false
```

`C_direct` is therefore not the missing object.  R568 is the live producer.
R572 and R503 are downstream compiler/consumer surfaces and do not themselves
supply the missing PDE estimate.

## Same-output residual / P3 frontier

The historical Gram/block chain now gives an exact named residual rather than a
generic "Gram problem":

```text
R179/R180   polarization + signed Gram ledger
R181        partner-first compression
R201        law of total Gram / covariance
R205        literal localized comparable partner cells
R206        localized compressed Gram frontier
R207        fixed-output carrier
R208        outer Fourier L2 carrier
R209        outputwise same-mode debt telescope
R211        quantitative residual-payment socket
R214        constant-band localization no-go
```

For fixed-output compressed cells `B_alpha`, the complete-graph identity is

```math
\mathrm{Debt}
=
(n-1)\sum_\alpha \|B_\alpha\|^2
-
\sum_{\alpha<\beta}\|B_\alpha-B_\beta\|^2.
```

The useful producer polarity is therefore a lower bound on physical pairwise
separation.  A single-cell low-output estimate does not by itself pay arbitrary
inter-partner covariance.

The immediate proof search is:

```text
literal compressed partner difference
  -> exact raw-curl/BAC-CAB expansion
  -> physical magnitude/radial + direction/helicity separation
  -> quantitative same-output pair-separation lower bound
  -> R211 ComparableSameOutputResidualPayment
```

PR #890's R205-compressed-cell to R574/R446 difference/PSD weld is a useful
same-object adapter at this level.  It remains a construction experiment until
the physical pair-separation theorem and certification close.

## Modern signed/helical and direct-companion ancestry

Proof-critical donors include:

- R120/R123: pure signed commutator / paired-Bony weld;
- R126-R132: HH radial-gap / square-gap / Plucker geometry;
- R166-R178: homogeneity-correct quadratic companion, raw-curl weld,
  radial/angular dual defect, low-output mass;
- R179-R181: exact signed Gram and partner compression;
- R186-R193: literal physical partner blocks, swap, and dynamic owner chain;
- R194-R200: cyclic/raw-curl/radius-gap continuation and homogeneity correction;
- R294: swap-invariant weighted mixed commutator;
- R545/R567: spectator factorization and live forcing full-square normal form;
- R414/R500/R503/R507: literal R406/direct-companion same-object lineage;
- R568: live cutoff-uniform commutator-only spacetime producer;
- R572: compiler from a paid R568 budget to the existing direct consumer.

Positive/fallback routes such as R575/R576/R577 remain valid reduction
machinery but are not automatically preferred over cancellation-preserving
producers.

## Certification posture

Use three separate status axes:

```text
MathematicalStatus
StatementStatus
CertificationStatus
```

`CertificationStatus` must separately record:

```text
validation root exists?
workflow targets it?
observed commit-specific Agda success receipt?
```

The focused NS workflow explicitly targets selected R101-R132 roots, R185,
R193, R200-R202, and—after the Paper-1 migration—the canonical
`DASHI/Papers/NavierStokes/TheoremInterfaceValidation.agda` root.

A workflow target without an observed successful run is not promoted to
kernel-certified status.  Historical PR #627 is an explicit example: its
workflow wiring is useful evidence, but no successful Agda receipt for that
exact head has been recovered here.

## Historical/alternative A1-A9 route

The earlier Paper-1 route is retained, not covered up.

The original `2026-06-09` manuscript organized the problem around the tail
identity

```text
d/dt E_{>K} = -D_{>K} + F_{>K}
```

and a danger-shell ratio `theta(K,t)`.  Its primary unresolved coordinates were
the coupled A1/A3 Abel-weighted compactness/stationarity package and the A4
physical-angular-richness to Fourier-output-richness transfer.

The exact historical candidate ladders included:

```text
A1.1 bounded Abel-weighted defect mass
A1.2 weak-* tightness / precompactness
A1.3 quantitative shell-tail control
A3.1 localized energy ODE
A3.2 Seregin/ESS compactness-rate intake
A3.3 quantitative stationarity target
A3.4 Abel-weighted multiscale closure
A4.1-A4.5 direction/Jacobian/coarea/strip-hitting/uniformity transfer
A5-A9 downstream depletion/monotonicity/CKN-BKM consumers
```

Those objects remain historical theorem/provenance surfaces.  They were
superseded as the **primary manuscript route** because later source archaeology
found a shorter literal R406/direct-companion chain terminating in the single
R568 spacetime producer.  They are still useful as diagnostics, alternative
reductions, and historical evidence of what was tried and why it was later
demoted.

No statement in this document retroactively declares the A1-A9 route proved or
fraudulent.  Its old open coordinates stay open historical facts unless their
authoritative owners change independently.

## Remaining NS burden

Priority order:

1. P3: prove quantitative same-output physical anti-alignment/separation for
   the literal compressed partner cells.
2. Use that to construct the existing R211 same-output residual payment rather
   than a new residual API.
3. Test the shortest same-object transplant from that paid historical residual
   into the modern signed/full-square route.
4. Prove the R568 cutoff-uniform commutator-only spacetime budget.
5. Consume the result through the already-constructed R572/R503 chain.

Broad archaeology is no longer itself a proof task.  Search should proceed
forward from named unpaid fields, while failed/superseded routes remain visible
as historical provenance.

## Publication posture

Publishable claim: Paper 1 is a conditional reduction manuscript whose modern
proof spine and remaining producer fields are explicit.  It distinguishes
constructed same-object/compiler machinery from open analytic payments and
preserves the June A1-A9 attempt as historical/alternative provenance.

Forbidden claim: unconditional regularity, Clay resolution, or kernel
certification without the corresponding mathematical and commit-specific
receipts.

## Historical/diagnostic multi-scale order framework

The older finite sparse-network/coherence diagnostics remain useful as
obstruction guidance.  Microscopic delocalization, temporal turnover, and
coarse geometric concentration can coexist; none alone proves regularity.
Their retained role is to motivate searches for dynamically persistent
nonlinear depletion or anti-alignment, not to substitute diagnostic coherence
for the P3 or R568 theorem.
