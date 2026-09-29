# Paper 1 Draft: Periodic Navier–Stokes Signed-Commutator Reduction and Shared Analytic Frontier

Author: Johl Brown  
Original Paper-1 draft date: `2026-06-09`  
Modern proof-spine migration: `2026-09-13`  
A/B/C/D nomenclature correction: `2026-09-15 09:32 AEST (UTC+10)`  
Clay max-cut reconciliation: `2026-09-23 AEST (UTC+10)`  
Status: live analytic manuscript draft; conditional; non-promoting

## Abstract

This manuscript records the current proof-critical **periodic** Navier–Stokes
reduction in DASHI. The programme freezes the Clay alternatives as four separate
lanes:

```text
Lane A = unforced whole-space R^3 regularity
Lane B = unforced periodic T^3 regularity
Lane C = forced whole-space breakdown
Lane D = forced periodic breakdown
```

The active manuscript construction is **Lane B**. The current preferred
Clay-facing analytic frontier is the R752 dyadic-difference two-leaf cut. Its
nonstandard PDE inputs are:

1. **W1**, a cutoff-uniform signed payment
   \[
   W_N(T)+Q_{+-,N}(T)\le B(T);
   \]
2. **W2**, nonnegativity of the integrated R751 dyadic-difference residual,
   \[
   0\le \int_0^T G_{N,\delta}(t)\,dt,
   \qquad \delta_N>0,
   \]
   where
   \[
   G_{N,\delta}(t)
   =
   \sum_\beta\!\left[
     3R^{\rm nested}_N(\beta,t)
     -P^{\rm dyad\text{-}diff}_N(\beta,t)
   \right]
   +3(2\nu-\delta_N)d_N(t).
   \]

R733 identifies the coherent mixed endpoint with the canonical \(Q_{+-}\)
observable. R737--R742 then differentiate the augmented observable
\(\mathscr A_N=X_N-12Q_{+-}\), substitute the R684 input-Laplacian form, and
show that the weighted/input-Laplacian term cancels exactly from the local W2
inequality. Thus the derivative calculation does **not** manufacture a new
coercive term: it exposes W2 as one signed physical packet-versus-combined
comparison. R741 gives a stronger pointwise producer form; R742 preserves the
original integrated theorem without that strengthening.

R744--R751 then put both nonlinear pieces on the same complete physical triad
carrier.  The production term must first be paired with its swap mate before
the exact three-leg energy cancellation applies.  After pairing, R748 reduces
it to exactly two differences of the **actual dyadic critical weights**,
not the historical radial \\(|k|\\) coefficients. R750 proves these production
difference channels vanish identically on same-shell nonzero triads. R751
integrates this literal local carrier, and R747/R746 prove its nonnegativity is
exactly equivalent to R742's packet-versus-combined spacetime inequality.

Once W1 and W2 are supplied, the existing exact compiler gives the uniform
critical barrier and the standard periodic compactness/continuation layer can
be invoked at its typed source boundary. The present paper is therefore a
conditional reduction manuscript, not an unconditional Clay/global-regularity
claim.

The R568/R572/R503 direct-companion chain, the R726 literal-R406 transport,
and the older centered/Taylor, second-moment, Gram/P3, Bony/Schur, radial,
Pluecker, and self/external decompositions remain theorem-bearing alternate
coordinates or producer strategies. They are not the current terminal analytic
cut.

Lane A remains an independent unforced whole-space obligation. Periodic B proof
progress does not imply whole-space A proof progress, and A does not imply B,
unless an explicit transfer theorem is constructed. Lanes C/D are
forced-breakdown BIDI verification/provenance lanes and do not settle either
unforced alternative.

## 1. Four-lane claim boundary and live Lane-B cutset

The current preferred periodic-B interface is R752:

```text
W1  cutoff-uniform signed weighted work + terminal Q_+- payment     OPEN

W2  integral R751 dyadic-difference residual >= 0                  OPEN
    residual = 3*nested orbit
               - swap-paired two-dyadic-difference production
               + 3*(2nu-delta_N)*critical dissipation
    with delta_N > 0
```

The exact coordinate dictionary is now:

\[
E_{M,N}(t)=Q_{+-,N}(t),
\]

\[
W_N(T)+Q_{+-,N}(T)
=
\mathcal C_N(T)+Q_{+-,N}(0),
\]

and

\[
\mathscr A_N(t)=X_N(t)-12Q_{+-,N}(t).
\]

R734 gives the equivalent augmented-weighted W2 form

\[
[\mathscr A_N]_T-[\mathscr A_N]_0+\delta_ND_N(T)
\le 12W_N(T).
\]

R737 differentiates this literal observable on the R408 trajectory. R738
substitutes the exact R684 input-Laplacian normal form. R739 then collects the
pointwise identity

\[
\dot{\mathscr A}_N
=
P_N-2\nu d_N-12C_N+12W_N.
\]

Consequently the \(12W_N\) term cancels exactly against the W2 right-hand side.
R740 proves

\[
\dot{\mathscr A}_N+\delta_Nd_N\le 12W_N
\iff
P_N\le(2\nu-\delta_N)d_N+12C_N.
\]

Under the standard R648 reality/divergence-free/nonlinear-conservation packet
structure, R741 identifies the latter with the stronger pointwise statement

\[
\mathrm{PacketStrictSurplus}_{N,\delta}(t)
\le
\mathrm{CombinedResidue}_N(t).
\]

R742 performs the same reduction at the original spacetime level, without
requiring that pointwise strengthening:

\[
\boxed{
\int_0^T\mathrm{PacketStrictSurplus}_{N,\delta}(t)\,dt
\le
\int_0^T\mathrm{CombinedResidue}_N(t)\,dt.
}
\]

Therefore the derivative attack has resolved the representation question but
has **not** closed W2. It shows precisely what W2 is.

R744--R751 sharpen that exact representation further. R744 places literal
critical production on the same complete zero-masked physical triad
enumeration used by the combined/nested orbit. R748 shows that local three-leg
energy cancellation is lawful only after swap-pairing the oriented production
cell. The paired production orbit then has the exact two-difference form

\[
P^{\rm dyad\text{-}diff}(\beta)
=
(\widetilde\lambda_k-\widetilde\lambda_q)\,
P^{\rm pair}_k(\beta)
+
(\widetilde\lambda_p-\widetilde\lambda_q)\,
P^{\rm pair}_p(\beta),
\]

where \(\widetilde\lambda\) is the zero-safe **actual dyadic critical
weight**. R749 therefore puts the W2 nonlinear gap on one local cell,

\[
G^{\rm nl}_N(\beta)
=
3R^{\rm nested}_N(\beta)
-
P^{\rm dyad\text{-}diff}_N(\beta).
\]

R750 proves the production correction vanishes whenever all three nonzero legs
lie in one dyadic shell. R751 adds the retained viscous credit and integrates
the same local carrier. R747/R746 identify

\[
\boxed{
\mathrm{W2}
\iff
0\le \int_0^T G_{N,\delta}(t)\,dt .
}
\]

This is the preferred W2 analytic surface. The R742 packet-versus-combined
inequality remains an exact alternate coordinate, not a separate theorem.

W1 remains

\[
\boxed{
W_N(T)+Q_{+-,N}(T)\le B(T)
}
\]

uniformly in cutoff. The old barrier-dependent estimate
\(Q_{+-}\lesssim \|u\|_{H^{1/2}}^2\|u\|_{H^1}^2\) cannot be used to produce W1
without circularity, because W1+W2 are being used to construct the uniform
\(H^{1/2}\) barrier.

The R723/R730 direct-combined cut is an exact alternate terminal presentation.
R726 plus strict-margin literal-R406 production remain a sufficient
factorization of R730, not mandatory independent leaves.

### Historical/alternate direct-companion route

The repository also retains

```text
CommutatorOnlySpacetimeBudget568
  -> R572
  -> R503.DirectOffDiagonalBudget
  -> R415 / critical-barrier consumer
```

as a valid adjacent producer/compiler lane. It is not definitionally the
R691/R723 currency: R687 only identifies the pair-rate-lifted R568 quantity
with the R691 commutator, and the unlifted-to-lifted quantitative implication
remains open. Accordingly this chain is no longer described as the principal
live periodic analytic interface.

Historical PDF-style B1--B4 producer lemmas and the old B7 direct
`R406 = covariance` equality are not part of the current terminal cut.

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

## 8. Current terminal compiler and alternate direct-companion chain

The current terminal compiler is:

```text
W1: weighted + terminal Q_+- cutoff-uniform payment
W2: integrated R751 dyadic-difference residual >= 0
  -> R747 / R746 / R742 / R734 / R730 exact coordinate compilers
  -> uniform critical barrier
  -> standard periodic compactness / continuation source boundary
```

R741 additionally exposes the stronger pointwise producer

\[
\mathrm{PacketStrictSurplus}_{N,\delta}(t)
\le
\mathrm{CombinedResidue}_N(t),
\]

but the pointwise form is not mandatory: R742 preserves exact equivalence with
the original integrated W2 leaf.

The older direct-companion chain is retained as an **alternate** route:

```text
CommutatorOnlySpacetimeBudget568
  -> NSTriadKNDirectLeafACompilerRound572Exact
  -> R503.DirectOffDiagonalBudget
  -> R415 / critical-barrier consumer
```

R572 is still a valid compiler, but R568 is not the canonical current analytic
leaf. The nested Schur/R577 branch is likewise retained as a fallback producer
route rather than promoted over the R752 frontier.

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
| R503 | direct companion -> R415 compiler | compiler constructed; direct budget itself still open | alternate Lane-B producer/compiler spine | certification tracked independently |
| R568 | commutator-only spacetime leaf | interface constructed; producer payment open | historical/alternate Lane-B producer lane | no producer receipt until an inhabitant is actually proved |
| R572 | direct leaf-A compiler | constructed given listed receipts | alternate Lane-B compiler | source/workflow status does not constitute R568 proof |
| R733-R736 | Q_+- endpoint weld and shared-weighted two-leaf recut | exact coordinate reductions; W1/W2 payments open | current Lane-B frontier precursor | source-written; head-specific kernel receipt not claimed here |
| R737-R743 | augmented derivative, cancellation, packet/combined W2 normal form | derivative and same-object reductions closed; packet/combined payment open | current frontier precursor | source-written/static-audited; no fresh kernel receipt claimed |
| R744-R752 | complete physical carrier, swap pairing, two actual dyadic differences, same-shell vanishing, integrated residual | exact carrier reductions closed; W1 and residual nonnegativity open | **current Lane-B analytic frontier** | source-written/static-audited; no fresh kernel receipt claimed |

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

The active periodic-B proof-search order is now:

```text
W1
  prove cutoff-uniform signed
  W_N(T) + Q_+-,N(T) <= B(T)

W2
  prove, with delta_N > 0,
  0 <= integral G_N,delta(t) dt

  where the literal local nonlinear carrier is
    G_nl(beta)
      = 3 * NestedOrbit(beta)
        - PairedDyadicTwoDifference(beta)

  and
    PairedDyadicTwoDifference(beta)
      = (lambda~_k - lambda~_q) PairPower_k(beta)
        + (lambda~_p - lambda~_q) PairPower_p(beta)

  plus the retained viscous credit
    3 * (2 nu - delta_N) * d_N(t)

W1 + W2
  -> R747/R746/R742/R734/R730 exact compilers
  -> uniform critical barrier
  -> standard periodic compactness / continuation
```

R750 gives one exact support simplification before estimation: on same-shell
nonzero triads the two dyadic production differences vanish identically, so
the local nonlinear cell reduces to (3R^{\rm nested}). This is **not** being
promoted to an exhaustive shell partition; the repository's full absolute
geometry partition remains separately open.

The R737--R740 derivative experiment remains a completed no-shortcut result:
the R684 input-Laplacian (W_N) term cancels exactly from local W2. Likewise,
the finite critical-norm equivalence machinery does not justify replacing
signed dyadic coefficient differences by physical mode-norm differences.
The next analytic work must therefore act on the literal R751 signed residual
or prove a lawful further cancellation on that same carrier.

Alternate/historical producer work remains available but is not the primary
queue:

```text
R571 centered/Taylor
  -> second-moment / six-three / nested signed machinery
  -> R568
  -> R572
  -> R503/R415
```

In parallel:

```text
Lane A: independent whole-space terminal cut and named-field search
Lane C/D: released-proof BIDI verification/provenance, non-discovery
certification: tracked orthogonally
```

Broad archaeology is no longer a proof step. Historical/certification audits
should proceed from named unpaid fields, while failed and superseded routes stay
visible as provenance.
