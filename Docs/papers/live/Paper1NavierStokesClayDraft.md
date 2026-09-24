# Paper 1 Draft: Periodic Navier–Stokes Signed-Commutator Reduction and Direct-Companion Frontier

Author: Johl Brown  
Original Paper-1 draft date: `2026-06-09`  
Modern proof-spine migration: `2026-09-13`  
A/B/C/D nomenclature correction: `2026-09-15 09:32 AEST (UTC+10)`  
Clay max-cut reconciliation: `2026-09-23 AEST (UTC+10)`  
Status: live analytic manuscript draft; conditional; non-promoting

## Abstract

This manuscript records the current proof-critical **periodic** Navier–Stokes
reduction in DASHI. The programme now freezes the Clay alternatives as four
separate lanes:

```text
Lane A = unforced whole-space R^3 regularity
Lane B = unforced periodic T^3 regularity
Lane C = forced whole-space breakdown
Lane D = forced periodic breakdown
```

The active manuscript construction is **Lane B**. The current canonical
Clay-facing cut is no longer a list of intermediate producer lemmas.  It is the
seven-coordinate max-cut recorded by
`NSTriadKNPeriodicClayEligibilityMaxCutRound642Exact`:

1. the cutoff-uniform signed R568 payment;
2. the physical phase-sensitive critical-production estimate;
3. the literal physical critical-slice realization;
4. the common-initial-datum realization and cutoff-uniform initial ceiling;
5. strictly positive retained viscosity;
6. ordinary scalar FTC/integration/order receipts; and
7. the periodic Sobolev--Rellich--Simon--weak-* completion package.

Only the first two are classified as genuinely new nonlinear estimates.  The
R571 centered/Taylor, second-moment/six-three, Gram/P3, Bony/Schur, radial/
Pluecker, and self/external channel decompositions remain theorem-bearing proof
strategies and provenance, but they are not independent Clay obligations.

The downstream weighted compiler is already source-written: a paid R568 budget,
together with the standard temporal/order receipts, is consumed by R572 to
build the pre-existing R503 direct-off-diagonal/R415 budget surface.  R639 now
installs the literal finite critical observables on the R414 slice with viscous
coefficient `2*nu` and derives the critical-energy inequality from the exact
energy identity, while R640 binds its initial coordinate to the common R240
initial datum modulo one live-trajectory-to-canonical-R34 coherence receipt and the actual uniform
initial ceiling.  The present paper is consequently a conditional reduction
manuscript, not an unconditional Clay/global-regularity claim.

Lane A remains an independent unforced whole-space obligation. Periodic B proof
progress does not imply whole-space A proof progress, and A does not imply B,
unless an explicit transfer theorem is constructed. Lanes C/D are
forced-breakdown BIDI verification/provenance lanes and do not settle either
unforced alternative.

The June `A1-A9` route and the later same-output Gram/P3 route are retained as
historical/alternative strategies. They were serious theorem-bearing attempts,
not strawmen. The P3 route is no longer the primary periodic producer because
the exact amplitude telescope exposed a many-to-one observable map: distinct
same-output incidences can carry equal velocity arguments and hence equal
compressed slot kernels, so incidence geometry alone cannot force the uniform
lower separation demanded by the generic P3 payment.

## 1. Four-lane claim boundary and live Lane-B cutset

The principal live periodic analytic interface is

```text
DASHI/Physics/Closure/NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact.agda
  CommutatorOnlySpacetimeBudget568
```

The historical identifier `LeafA` in owner names is not programme Lane A.
Programme Lane B is the periodic route described in this paper.

For a literal physical periodic NS Galerkin trajectory `T` and supported cutoff
trajectory `R`, R568 asks for a cutoff-independent bound on four times the
spacetime integral of the global signed forcing/commutator full square.
Schematically,

```math
4\int_0^T \mathrm{globalForcingFull}(N,t)\,dt \le B(T)
```

uniformly in the cutoff `N`.

> **Theorem 1.1 (periodic direct-companion reduction, conditional).** Assume the
> standard temporal/order receipts isolated by the direct leaf-A compiler and
> assume an inhabitant of `CommutatorOnlySpacetimeBudget568` on the literal
> periodic Galerkin trajectory. Then the existing R572 compiler constructs the
> pre-existing R503 `DirectOffDiagonalBudget`, which feeds the existing signed
> R415/critical-barrier consumer chain. The theorem does not assert that the
> R568 producer itself is proved.

The current Clay-eligible max-cut is:

```text
NEW / NONSTANDARD
C1  R568 cutoff-uniform signed weighted payment                     OPEN
C2  physical phase-sensitive critical-production estimate           OPEN

SAME-OBJECT / PHYSICAL
C3  literal critical coordinates installed on R414                  COMPILER CLOSED
    exact critical-energy identity                                  CLOSED GIVEN STANDARD CALCULUS
C4  common-initial-datum same-object compiler                       CLOSED
    live trajectory -> canonical R34 mode-list/modeListed attachment                               OPEN RECEIPT
    cutoff-uniform initial critical ceiling                         OPEN
C5  positive retained viscosity 0 < 2*nu-a                          OPEN
    optional a<=nu sufficient compiler                              CLOSED / NOT MANDATORY

STANDARD COMPLETION
C6  scalar FTC + rational integration linearity/order receipts       OPEN
C7  periodic Sobolev/Rellich/Simon/weak-* physical instantiation    OPEN
```

The genuinely new nonlinear theorem count is therefore two: C1 and C2.
Historical PDF-style B1--B4 producer lemmas and the old B7 direct
`R406 = covariance` equality are **not** part of this terminal cut.  The latter
is in fact the wrong same-object statement for the live nonseparable
Cauchy/resolvent R406 carrier.

This distinction is load-bearing. `C_direct` is not the missing object. R572 is
not a new PDE estimate. R503 is not evidence that R568 has been paid, and an
optional producer decomposition does not become a separate Clay obligation
merely because it is mathematically interesting.

## 2. Literal periodic finite-dimensional carrier

Lane B is formulated first on the exact finite periodic Galerkin carrier.
Fourier modes live on the repository's integer lattice; physical triad incidence
fixes literal resonances and output fibres; Leray projection and helical
projectors are represented in the same finite carrier; and the trajectory
owners retain the literal projected dynamics required by R406 and the later
direct-companion chain.

The helical infrastructure uses the periodic curl symbol

```math
\widehat{\operatorname{curl}u}(k)=i\,k\times\widehat u(k)
```

and the exact eigenvalue convention

```math
\lambda_+(k)=|k|,\qquad \lambda_-(k)=-|k|.
```

The finite algebra, incidence identities, swap laws, and same-object vector
identities should be read as internal theorem-bearing structure where their
owners provide proofs. Standard continuum/Haar/Bochner, limiting, or imported
analytic authority remains separately classified and is not smuggled into the
finite carrier by notation.

These periodic facts are B-specific until an explicit whole-space transfer or
separate R3 realization is constructed. They are not silently credited to Lane
A.

## 3. Optional Lane-B signed commutator / centered-Taylor producer route

This is a theorem-bearing strategy for proving C1/C2, not an independent
Clay-max-cut requirement.  The cancellation-first route preserves sign and
phase before positive majorization. R571 expands the raw inner physical interaction into four exact
helicity channels

```math
M_{\sigma\tau}
=
(\lambda_\tau(q)-\lambda_\sigma(p))
P_k(u_p^\sigma\times u_q^\tau),
```

with no estimate in the identity itself. R573/R574 attach those channels to the
modern weighted/raw directional carrier and pay the single-channel low-output
magnitude estimate. R575 shows that the four positive channel majorants collapse
to raw modal mass without an extra factor four at the majorant level.

The current highest-alpha periodic route branches **before** generic positive
recombination. On the homochiral radial-near sector, the target is to construct
the literal kernel-displacement data

```math
(y,-y,L,R_+,R_-,g_+,g_-)
```

on the same R571 carrier, then reuse the already theorem-bearing early-August
chain:

```text
paired second-order identity
  -> derivative-variation-aware second-moment bound
  -> six-three scale arithmetic
  -> R89 two-derivative payment
  -> signed inner-fibre/full-square transport
  -> R568.
```

The Fourier-leg swap `a<->b` is not identified with kernel displacement
`y<->-y` without the typed Fourier/increment realization. Likewise the R571
helical gap is not simply declared to be a physical Taylor displacement. Those
same-object seams must remain explicit.

The positive R576/R577 four-channel/Gram routes remain valid fallbacks. They are
not automatically the primary producer because they deliberately discard some
signed cancellation structure.

Important donors include:

- the July signed multiplier-difference commutator lane;
- the official torus character / weighted-increment representation;
- early-August centered first/second-moment identities;
- six-three scale arithmetic;
- R127/R128 radial/square-gap and Pluecker geometry;
- R172-R178 raw-curl dual-defect and low-output estimates.

Those are retained as ancestry and reusable mathematics, not rewritten as if
they were discovered only by the later R57x normal form.

## 4. Historical same-output Gram/covariance route

The block route identified a genuine residual and remains theorem-bearing
historical/provenance infrastructure:

```text
R179/R180   exact polarization and signed Gram ledger
R181        partner-first compression
R201        law of total Gram / covariance
R205        literal localized comparable partner cells
R206        localized compressed Gram frontier
R207        same-output carrier
R208        outer Fourier L2 carrier
R209        outputwise Gram telescope
R211        quantitative residual-payment consumer socket
R214        constant-band localization no-go / negative control
PR #890     compressed difference/PSD and complete-graph P3 exploration
```

After partner compression, the exact obstruction is the same-output
between-partner debt. R207 correctly removes cross-output covariance because
distinct Fourier outputs are combined in the outer Fourier `L^2` sum. R209
telescopes the remaining same-output debt over outputs, and R211 states the
backward-facing payment socket

```math
D_{CC}\le R_{CC}
\quad\Longrightarrow\quad
Q_{CC}\le M_{CC}+R_{CC}.
```

R214 is a negative control: even zero-width shell localization is compatible
with strictly positive aligned Gram debt. It refutes "constant shell width alone
pays covariance"; it does not refute every signed-resolvent, Schur,
Cotlar-Stein, or physically richer producer.

## 5. Why the P3 lower-separation attempt is no longer primary

For fixed-output compressed cells `B_alpha`, the exact complete-graph identity
has the useful form

```math
\mathrm{Debt}
=
(n-1)\sum_\alpha\|B_\alpha\|^2
-
\sum_{\alpha<\beta}\|B_\alpha-B_\beta\|^2.
```

This made a lower pair-separation theorem a plausible route to positive Gram
debt payment. PR #890 constructed substantial same-object plumbing around that
idea, including the literal compressed-cell difference and PSD carrier.

The route was not abandoned silently. Its exact amplitude telescope exposed a
many-to-one observable map. The repository now proves that, at fixed output,
equal velocity arguments give equal slot kernels independently of the supplying
incidence geometry. A separate geometry owner exhibits the relevant incidence
multiplicity structure, while the stronger concrete finite-Galerkin collision
witness remains separately fail-closed.

Therefore a generic theorem of the form

```math
incidence separation alone
  -> uniform positive lower bound on ||B_alpha-B_beta||^2
```

is not an admissible primary producer. The Gram route remains useful for:

- exact covariance accounting;
- residual-payment interfaces;
- negative controls against shell-localization-only arguments;
- future signed/resolvent producers with additional physical state information.

It is historical/alternative, not erased.

## 6. Weighted/nested commutator and full-square normal form

The modern weighted route preserves the signed commutator before applying
positive envelopes. R294 proves the swap-invariant weighted mixed-commutator
collapse. R545 then performs the spectator factorization, and R567 reduces the
live normal form to one forcing full square after the exact transpose and
amplitude identifications. R568 names the resulting cutoff-uniform spacetime
producer.

```text
weighted signed commutator
  -> fixed spectator fold
  -> complete ordered/full-square carrier
  -> one forcing full square
  -> R568 cutoff-uniform spacetime producer
```

The nested Schur route and R575/R576/R577 positive reductions remain useful
fallback compilers/donors. Their existence does not turn the direct signed
producer into a solved theorem.

## 7. Direct companion and literal R406 same-object lineage

Representative owners include

```text
NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact.agda
NSTriadKNDirectResolventIntegratedCompanionRound500Exact.agda
NSTriadKNDirectResolventSignedCrossToR415Round503Exact.agda
NSTriadKNRound104ToLiteralR406CriticalSliceRound507Exact.agda
```

The direct route proves that the literal R406 remainder integral is the same
quantity consumed by the direct companion, with the exact factor four carried
through the compiler:

```math
F_N^{R104}
\equiv
\int_0^T R406(N,t)\,dt
\equiv
4\,C_{\rm direct}^{\rm integrated}(N,T).
```

The precise lesson is

```text
C_direct constructed != C_direct uniformly paid.
```

The construction/same-object weld is not the analytic R568 estimate.

## 8. Terminal periodic compiler chain

Once the Lane-B live producer is paid, the downstream route is explicit:

```text
CommutatorOnlySpacetimeBudget568
  -> NSTriadKNDirectLeafACompilerRound572Exact
  -> R503.DirectOffDiagonalBudget
  -> existing R415 / critical-barrier consumer
```

R572 is a compiler. Its source requires the R568 commutator budget and standard
temporal/order receipts, then constructs the pre-existing R503 budget. It
introduces no replacement R406 observable and no parallel leaf-A consumer.

The nested Schur/R577 branch is retained as a fallback compiler route. It is not
promoted over the direct route merely because it has a different interface.

## 9. MathematicalStatus, StatementStatus, and CertificationStatus

The paper uses three independent coordinates.

- **MathematicalStatus**: what theorem/identity/conditional implication is
  actually source-written.
- **StatementStatus**: whether the manuscript/interface states the current
  theorem boundary accurately.
- **CertificationStatus**: whether a validation root exists, whether a workflow
  targets it, and whether an observed commit-specific proof-checker success
  receipt has actually been recovered.

A configured workflow is not itself a kernel receipt.

| owner / tranche | role | MathematicalStatus | StatementStatus | CertificationStatus |
| --- | --- | --- | --- | --- |
| canonical four-alternative owner | A/B/C/D source/formulation split | typed lane/source statuses and C/D->A/B firewall | current | source-written; external source receipt is not an independent DASHI rerun |
| R101-R132 selected frontiers | early physical/commutator milestones | theorem-bearing selected roots | historical support | validation roots/workflow targets exist for many selected milestones; commit-specific receipts vary |
| R185 | three-class Gram reduction | constructed reduction; terminal payment open | retained predecessor | validation root/workflow target recorded; head-specific receipt not assumed here |
| R193 | complete dynamic/external-cell frontier | constructed source chain; terminal promotion false | retained predecessor | cumulative validation root/workflow target recorded; head-specific receipt not assumed here |
| R200-R202 | homogeneity-correct quartic frontier / Gram residual API | constructed reduction interfaces; residual payment open | historical modern-predecessor support | focused workflow targets recorded; historical PR-head Agda success receipt not assumed here |
| R207/R209/R211 + #890 | same-output debt/P3 infrastructure | exact debt/difference algebra; generic incidence-only separation route not primary | historical/alternative | source-written components; stronger physical collision/no-go remains separately fail-closed |
| R214 | constant-band no-go | negative control proved | historical/current negative control | source-written; no extra promotion inferred |
| R500 | integrated direct companion | same-object weld closed modulo explicit integration authority | current Lane-B spine | certification tracked independently |
| R503 | direct companion -> R415 compiler | compiler constructed; direct budget itself still open | current Lane-B spine | certification tracked independently |
| R568 | live commutator-only spacetime leaf | interface constructed; producer payment open | **live Lane-B analytic cutset** | no producer receipt until an inhabitant is actually proved |
| R572 | direct leaf-A compiler | constructed given listed receipts | current Lane-B compiler | source/workflow status does not constitute R568 proof |

This table is intentionally conservative. Later validation work may upgrade a
`CertificationStatus` without changing the underlying mathematical theorem.
Conversely, citation or prose cannot upgrade either mathematics or
certification.

## 10. Lanes A, C, and D

### Lane A — unforced whole-space

Lane A is not a corollary of this periodic manuscript. Its immediate programme
job is to freeze its own current producer/compiler/terminal-consumer cut. Any
reuse of the periodic route requires an explicit R3 transport or a genuinely
carrier-independent theorem.

### Lanes C/D — forced breakdown verification/provenance

The repository carries a typed source reconstruction of released forced
breakdown results. C/D work is BIDI verification: source lineage, exact
hypotheses, dependency closure, same-object carrier integration, and independent
checker receipts where available. These lanes do not establish or refute
unforced A/B merely by sharing the Navier–Stokes equations.

External mathematical discovery credit remains external. DASHI credit is
restricted to its reconstruction, verification, transport, and provenance
work. Prize/publication/acceptance status is a separate external-governance
coordinate.

## Historical/alternative A1-A9 route

### Historical context

The original live Paper-1 draft was dated `2026-06-09` and titled
*Navier-Stokes Blowup Reduction Through Tail Flux Control*. It organized the
argument as the `A1-A9` ESS/Abel-defect/tail-flux route. Its governing seam was

```text
d/dt E_{>K}(t) = -D_{>K}(t) + F_{>K}(t),
theta(K,t) = |F_{>K}(t)| / D_{>K}(t).
```

It treated blowup exclusion as a dynamically selected high-tail domination
problem.

The live June frontiers were the coupled `A1/A3` quantitative
localization/stationarity package and the independent `A4` physical-to-Fourier
support-richness transfer. Candidate rates and constant tables were recorded as
targets, not silently promoted theorem inputs.

### Why it is no longer the primary Paper-1 organization

The route was not discarded because it was fraudulent or useless. It was
superseded as the primary manuscript spine because later construction
archaeology produced a shorter same-object route from the literal R406 remainder
through the direct companion to a single live R568 spacetime budget, followed
by the already-existing R572/R503 compiler chain.

The A1-A9 programme remains valuable as historical provenance, diagnostics,
alternative reductions, and a record of what the ESS/Abel/support-richness
assumptions would have needed to pay. The Round62 Com/Schur interface is
retained for the same reason.

### Historical claim firewall

Nothing in this migration retroactively declares an earlier route proved or
failed more strongly than its own source state supported. Later external or
internal results receive their own mathematical credit; earlier DASHI objects
receive only the ancestry/priority statement supported by dated source.
Citation does not import proof or certification.

## Current roadmap

The active manuscript proof-search order is now:

```text
Lane B P1: R571 literal centered/Taylor realization
  -> Lane B P2: old paired second-moment + six-three transplant
  -> Lane B P3: signed inner-fibre/full-square propagation to R568
  -> R572 compiler
  -> R503/R415 critical-barrier consumer
```

In parallel:

```text
Lane A: freeze independent whole-space terminal cut, then named-field search
Lane C/D: released-proof BIDI verification/provenance, non-discovery
certification: tracked orthogonally
```

Broad archaeology is no longer a proof step. Historical/certification audits
should proceed from named unpaid fields, while failed and superseded routes stay
visible as provenance.
