# Paper 1 Draft: Periodic Navier–Stokes Signed-Commutator Reduction and Shared Analytic Frontier

Author: Johl Brown
Date: `2026-06-09`
Version: `draft 1`
Status: live analytic manuscript draft; Clay-facing; non-promoting

## Abstract

This manuscript audits a **conditional**, physically sourced regularity
reduction for the unforced periodic Navier–Stokes problem (Clay alternative B).
It preserves the literal finite Fourier/Galerkin nonlinear carrier, the
signed commutator and critical-energy algebra, and the W1 plus signed-residual
W2 *compiler* of the R733–R752 family. The critical November 2026 correction
is that the **unrestricted universal positive W2 auxiliary premise is
mathematically false** on smooth real divergence-free finite-Galerkin data:
the earlier R734/R735 augmentation has an N=2 counterexample, and a separate
original R820/R823/R825 complete-rate premise fails on a real-time
3–4–5-mode witness. Exact conditional algebra is not a positive physical
inequality. The identity of the more narrowly phrased R751/R752 residual with
either falsified premise must be proved before any transfer of the no-go; its
unqualified all-data positivity is not a valid default hypothesis.

The research question is therefore which *different*, non-circular
signed/coercive payment—possibly with an explicit remainder or a proved
restriction covering the intended data class—can replace the falsified
universal premise **while preserving W1**, cutoff-uniform control,
continuation, and the official initial-data quantifiers. Historical A1–A9
ESS/Abel/tail-flux, R568/R572/R503 and R752 signed-difference constructions
remain attributed, useful donors, not completed global regularity.
This manuscript is a proof-boundary and candidate-reduction paper;
no local Agda/Lean kernel replay, Clay resolution or peer-review
acceptance is inferred from source-written contracts or SymPy tests.

## 1. Introduction and main theorem

This manuscript records the current proof-critical **periodic** Navier–Stokes
reduction in DASHI. The programme freezes the Clay alternatives as four separate
lanes:

```text
Lane A = unforced whole-space R^3 regularity
Lane B = unforced periodic T^3 regularity
Lane C = forced whole-space breakdown
Lane D = forced periodic breakdown
```

The active manuscript construction is **Lane B**, but the prior R752
dyadic-difference **two-leaf representation** is now a **conditional compiler
subject to the physical no-go audit below**, not a claimed available
unrestricted universal estimate. Its historical sufficient premises were:

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

The implication *if W1 and a suitable genuine W2 are supplied, then the
stated compiler yields a critical barrier* remains conditional mathematics.
The unqualified all-data positivity of the older physical R734/R735 W2 and
R820/R823/R825 complete signed-payment families has since been falsified.
We do **not** assert that the R751/R752 residual is definitionally equal to
either of those false quantities; that identity is an explicit source-audit
gate. Merely relabelling the rejected payment as R751, or restricting data
without proving coverage, cannot close Lane B. A new genuine PDE inequality,
with source-valid all-data scope, is needed for the continuation consumer.

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

## 1.1 November 2026 source-first status correction — physical no-go and usable welds

This dated correction supersedes the historical wording below whenever it
calls a universal nonnegative signed W2 premise merely "open". The controlling
source is
`Docs/roadmaps/ClayRecoveredProducersW2NoGoR856SourceMaxCut20261115.md`,
together with
`Docs/roadmaps/ClayB1R820R825UnrestrictedSignedPaymentNoGo20261115.md`
and `Docs/papers/live/NSR828Rational345FourierWitness.md`.

**Two distinct falsified auxiliary proposals.** First, the original
R734/R735 augmented weighted W2 has an actual six-mode, unforced,
real divergence-free **N=2 finite-Galerkin** counterexample.
Second, for the radius-four (728 nonzero lattice modes)
real finite Galerkin 3–4–5 initial state, the original
R850/R853/R823 source-normalized rate satisfies
```text
C(0) = -557627/125,   P(0) = 0,    d(0) = 15834,
r(0) = 6 (12 C(0) - P(0) + d(0)) = -28273644/125 < 0.
```
The classical real finite-dimensional ODE, the source-coherent
continuity argument, and the original R854 conservative time interval
give strictly negative signed-rate integral on a positive interval.
Hence the **unrestricted every-terminal nonnegative** R820/R821/R823/R825
complete rate/reserve input is not a viable universal premise.
These are counterexamples to specific **auxiliary inequalities**;
they do **not** show breakdown of any Navier–Stokes solution,
nor refute the Clay regularity alternative.

**Critical dependency distinction.** R744–R752's exact
two-dyadic-difference algebra and R747/R746/R742 integrated
*equivalences* are retained; they only yield
`W2_752 ↔ NonnegativeIntegral(G_751)`. The proposition
`NonnegativeIntegral(G_751)` must NOT be promoted from that
equivalence. To infer the stronger R820/823 falsification *for
R752 itself*, first establish the exact same-original-real-Galerkin
identity of the two signed observables, including weight,
normalization, zero-mode, and real-time integration. If this fails,
the new G751 sign estimate remains independently **unproved**,
not automatically refuted.

**Replace rather than re-label the lost positive payment.** The
next analytic producer must pay an estimate whose signed negative
part, defect/remainder and cutoff dependence are explicit,
or justify a state restriction with a theorem covering all
initial data required by the chosen Clay alternative.
R92/R102 signed-helicity/dyadic-defect decompositions,
R568's signed commutator route and the exact same-shell
R750 cancellation are potential source donors, not
the estimate or a continuation theorem by themselves.
The independent cutoff-uniform W1 payment is also unpaid.

**Four-lane and authority firewall.** A (unforced whole-space)
is neither a corollary of B nor a premise silently imported into it.
C/D are forced breakdown/source-reconstruction alternatives, with
independent external authorship, mathematical adjudication,
and trusted kernel/source-alignment gates. C/D source presence
is not A/B regularity and is not a DASHI discovery claim.
The current controlling A/B/C/D proof status is
`Docs/roadmaps/NSProofControl20260915.md` (updated on this
manuscript branch), not a paper round count. A local SymPy
rational/identity audit is distinct from an Agda or Lean kernel
receipt.

## 1. Four-lane claim boundary and live Lane-B cutset

The **historical conditional** periodic-B R752 interface was:

```text
W1  cutoff-uniform signed weighted work + terminal Q_+- payment     OPEN

W2  integral R751 dyadic-difference residual >= 0                  CONDITIONAL SOURCE;
    unrestricted universal positive-payment route NOT AVAILABLE after
    R734/R735 and R820/R823/R825 source-correct physical counterexamples
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

This is the selected **exact coordinate identity** for the R752
*conditional* W2 proposal, not an established source-uniform positive
inequality. R742's packet-versus-combined form remains an alternate
coordinate, not a second theorem. The physical scope of both must be
tested against the R734/R735 and R820/R823/R825 counterexamples and
the actual complete real Fourier source before being considered
an admissible universal premise.

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

## 8. Conditional R752 compiler, falsification firewall, and alternate direct-companion chain

The preserved conditional terminal compiler is:

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

R572 remains a valid conditional compiler; R568 is not yet a proved
source-uniform signed physical producer. The nested Schur/R577 route also
remains a fallback. After the November no-go, no one of these
candidate producers may be called the universally *paid* Lane-B
analytic leaf merely because its downstream compiler exists.

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
| R733-R736 | Q_+- endpoint weld and shared-weighted two-leaf recut | exact coordinate reductions; **unrestricted R734/R735 positive W2 refuted on physical N=2 data** | retained conditional compiler and no-go owner | source-written plus independent local SymPy; no new kernel receipt |
| R737-R743 | augmented derivative, cancellation, packet/combined W2 normal form | derivative and same-object reductions; conditional signed-payment source must be counterexample-audited | conditional alternative representation, not a positive W2 proof | source-written/static-audited; no new kernel receipt |
| R744-R752 | complete physical carrier, swap pairing, two actual dyadic differences, same-shell vanishing, integrated residual | exact carrier reductions; **physical universality of the selected residual remains unproved**, and identification with falsified R734/R820 inputs requires proof | candidate alternative only after source/no-go check | source-written/static-audited; no new kernel receipt |

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

In particular, the current repo state now carries a concrete candidate package
for `A1.1-A3.4` with explicit constants and rates. Those values are recorded
in Appendix B as a candidate constant table rather than as theorem input. They
are a named target for the `A1/A3` acceptance question and are not silently
promoted here to theorem status.

Accordingly, the remaining burden in this manuscript should not be described as
missing theorem-shape grammar. The theorem package is explicit. What remains is
the fail-closed promotion question: whether the candidate `CKN + ESS + LRT +
A1/A3 + A4 + A5-A9` packet is accepted in the exact normed and constant-level
form consumed by the reduction.

At theorem resolution, the live `A1/A3` checklist is:
`A1.1` bounded Abel-weighted defect mass,
`A1.2` weak-* compactness,
`A1.3` shell-tail control,
`A3.1` an energy ODE for `W_r = U_r - U_infinity`,
`A3.2` a quantitative Seregin/ESS rate intake,
`A3.3` a rate `delta_r -> 0`,
and `A3.4` a multiscale Abel-summation closure with no hidden exponent loss.
The live `A4` checklist is:
direction-map regularity,
Jacobian lower bound,
coarea propagation,
strip-hitting richness,
and a uniform constant across the Type-I rescaling family.

For the abstract closure grammar governing how this reduction fits into the
larger corpus, see Paper 8, *Closure Grammar, Jordan-von Neumann Recovery, and
Controlled Consumers*. Paper 1 does not rely on Paper 8 for its analytic proof
steps, but it does inherit the same claim-boundary discipline.

**Formal status box.** This is a candidate analytic reduction manuscript. The
external inputs are load-bearing and named explicitly: `LerayHopf` supplies the
weak-solution and energy-inequality framework, `CoifmanMeyer` supplies the
paraproduct bookkeeping used to isolate near-diagonal shell interactions,
`CKN` supplies the epsilon-regularity closure surface, and `BKM` supplies the
continuation criterion. The proposed `A4` intake is `LeiRenTian2025`, consumed
only as a candidate geometric route from physical angular richness toward the
Fourier output-support richness required downstream. The internal DASHI
receipts track theorem-interface anchors and terminal false guards. The
diagnostic surfaces identify exactly where `A1/A3` and `A4` still need
accepted quantitative constants. No global regularity theorem or Clay
resolution is asserted.

The historical theta or danger-shell diagnostics remain relevant as obstruction
guidance, but they appear here only as appendix-level context for why the tail
route is natural.

## 2. Analytic setup and blowup reduction

Fix a Leray-Hopf solution `u` on `R^3 x [0,T)` and a Littlewood-Paley
decomposition `u = sum_j Delta_j u`. For a shell cutoff `K`, define the tail
energy and dissipation

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

If `|F_{>K}| <= (1-eta) D_{>K}` with `eta>0`, then the tail energy decays and
the chosen shell lies on the dissipative side of the seam. The analytic problem
is therefore to make this domination statement non-circular at a shell selected
from the dynamics rather than from hindsight.

Assume toward contradiction that `T<infinity` is a first singular time. The
standard CKN/BKM reduction says it is enough to preclude a critical
concentration scenario in which energy, vorticity, or enstrophy remain
compatible with Leray control at coarse scales while a high shell or short
parabolic cylinder carries the defect. This paper packages that contradiction
route into assertions `A1` through `A9`. Assertions `A1-A3` identify the
dangerous shell geometry and stationarity package; `A4-A6` trap the defect
near sufficiently rich supports; `A7-A8` turn that geometry into depletion and
monotonicity; `A9` feeds the resulting gain into the continuation criterion.

The numbering is now used consistently: `A1` denotes ESS shell localization,
`A2` denotes Abel defect-measure construction, and `A3` denotes the
near-diagonal stationarity bootstrap. The live ladder therefore runs
`A1-A9`, with `A1/A3` naming the coupled localization-stationarity frontier.

## 3. A1-A3: ESS, shells, Abel defect measure, near-diagonal stationarity

The first stage is an ESS reduction: replace a diffuse blowup scenario by one
that is concentrated on an essentially singular sequence of shells and times.
The selected shell `K_*(t)` is not defined by a moving theorem-proof shortcut.
It is a danger-shell locator tied to the maximal stress of the tail-flux to
dissipation ratio, subject to the proviso that low-shell artefacts do not count
as dissipative-tail witnesses.

Assertion `A1` is the shell localization principle. It says that any candidate
blowup sequence admits a subsequence for which the dominant defect is seen at a
bounded-width shell window around `K_*`. This is the manuscript version of the
runtime insight that the obstruction must be high-high and near-seam rather
than low-high.

Assertion `A2` introduces the Abel defect measure. Instead of pretending that
the nonlinear remainder is already absorbed, we record it as a signed defect
object whose near-diagonal part is the only component allowed to survive into
the later contradiction argument. Assertion `A3` is the near-diagonal
stationarity bootstrap: after passing to the ESS subsequence, the shell
interactions feeding the defect do not drift arbitrarily far from `K_*`; they
remain trapped in a thin cone around the diagonal `|j-k| <= c_0`.

This is the point at which Coifman-Meyer style paraproduct bookkeeping enters:
it identifies which commutator or bilinear pieces are truly dangerous and which
are perturbative once the shell window is fixed. The point is not yet a closed
estimate. The point is a reduction of the entire nonlinear obstruction to a
small class of near-diagonal defect interactions.

> **Proposition 3.1 (output of `A1-A3`).** After passing to the ESS subsequence
> and fixing the danger shell `K_*`, the blowup obstruction is reduced to a
> bounded-width shell window carrying an Abel defect measure whose surviving
> interactions are near-diagonal and stationary in the sense required for the
> support-geometry argument of Sections 4-6.

In sum, `A1-A3` yield a controlled shell window and defect measure from which
Sections 4-6 will extract support geometry.

What is not claimed here is that the ESS package already closes. The unresolved
mathematics is the quantitative part of the `A1/A3` package: enough compactness
to produce a true Abel defect object and enough stationarity to make its
near-diagonal component usable in the later support argument.

More precisely, the remaining burden is not just "some fixed-point argument."
The manuscript needs a quantitative rate package whose natural norm is stable
under the Abel-weighted multiscale summation used later in `A6-A8`. Candidate
Gronwall or dyadic-improvement maps are informative only if they really close
on that normed space and really consume the imported `CKN` / `Type-I` /
Seregin exponents without hidden losses.

In particular, the current candidate imported verification task is not merely
"some epsilon-regularity." It is an exact Seregin/ESS-style rate in the norm
used by the Abel bootstrap. Until that intake is fixed in the required form,
the manuscript treats even attractive candidate rates as diagnostic guidance
rather than promoted theorem inputs.

For submission purposes the external intake is therefore stated in the
following fail-closed form. By the Seregin/ESS Type-I compactness theorem
(`Seregin2012`, building on `ESS2003`), every Type-I blowup rescaling sequence
with the critical `L^{3,\infty}` control admits a subsequence converging in
`L^2_loc` to an ancient `L^{3,\infty}` solution `W_infinity`, with the same
critical bound up to the constants of the theorem. This paper consumes that
statement only as the compactness part of `A3.2`. The stronger
Abel-bootstrap assertion needed here is the normed and quantitative target

```text
delta_r = || W_r - W_infinity ||_Abel = O(r^(1/12)),
```

after passage to the relevant subsequence. The displayed rate is a named
`A3.3` target and is not derived from Seregin/ESS in this draft. The
downstream `A3.4` Abel summation must still prove that this target survives the
multiscale Abel-weighted norm without hidden exponent loss.

**Route compatibility note.** This paper develops the tail-flux /
Abel-defect route `A1-A9`. A separate microlocal route through pressure
commutator estimates near the stretching surface `Sigma` is recorded in the
Sprint164 boundary surfaces. The two routes are independent reduction
strategies. They would become equivalent only after proving a bridge from
Abel-defect stationarity near `K_*` to microlocal alignment near `Sigma`, or
the converse. No such bridge is claimed here; this manuscript keeps the
tail-flux/Abel route and the Sprint164 microlocal route separate.

## 4. A4-A6: support geometry, richness, defect-from-critical coercivity

The next stage replaces shell bookkeeping alone by physical-space support
geometry. Assertion `A4` selects parabolic cylinders or annular supports on
which the defect mass is nontrivial but quantitatively localized. Assertion
`A5` is a richness statement: the support cannot degenerate to a set too thin
to interact with the dissipation mechanism. Assertion `A6` then converts this
richness into defect-from-critical coercivity: the near-diagonal nonlinear
production may remain positive, but after Abel averaging, transport control,
and commutator bookkeeping it must lose a fixed fraction of the critical
tail-flux budget. This is weaker and safer than a pointwise negative stretching
claim; it asks only that the localized defect cannot retain full critical
strength once the `A4-A5` support geometry is imposed.

The manuscript needs this section because shell domination alone cannot exclude
edge inflow or critical near-diagonal recirculation. The support geometry
creates a second ledger, independent of the Littlewood-Paley identity, that
tracks how much defect can leak into or out of the danger region and how much
of the remaining near-diagonal defect must be spent against the coercive
reserve. The intended conclusion is that after fixing radii `r_4 < r_6` and
smallness thresholds `eps_4`, `eps_6`, one has enough slack to replace the raw
flux term by an effective interior flux plus a leakage/coercivity error that is
strictly smaller than the dissipation reserve carried forward to `A7-A8`.

> **Proposition 4.1 (constants compatibility, first pass).**
Choose radii and thresholds so that

```text
Lane A: independent whole-space terminal cut and named-field search
Lane C/D: released-proof BIDI verification/provenance, non-discovery
certification: tracked orthogonally
```

and require the leakage error at scale `r_6` to be at most `eps_6 D_{>K_*}`
while the richness lower bound at scale `r_4` contributes at least
`4 eps_6 D_{>K_*}`. Then the support-geometric gain leaves a factor of `3`
slack before depletion is used. The exact numeric values are not canonical, but
the inequalities are jointly satisfiable because the support radii are ordered
strictly and the smallness parameters are nested rather than competing at the
same scale.

In sum, `A4-A6` convert near-diagonal defect control into a leakage-aware,
defect-from-critical coercivity statement with explicit room left for the later
depletion and closure steps.

The theorem-sized obstruction in this section is the quantitative `A4`
transfer itself. The manuscript needs a uniform physical-to-Fourier output
richness constant across the Type-I rescaling family; without that, the
constants ladder of Propositions 4.1 and 5.1 has no honest geometric source.

The current candidate route runs through the geometric obstruction suggested by
`LeiRenTian2025`, then direction-map regularity, coarea, and Whitney/Jacobian
control. The specific theorem needed here is not merely qualitative vorticity
direction non-concentration. It is a quantitative, Type-I-uniform transfer from
physical angular richness to Fourier output-support richness in the exact norm
used by `A5-A6`. What remains mathematically live is the passage from those
local ingredients to that uniform lower bound.

The sharpened candidate package is likewise explicit: a direction-map
regularity bound, a Jacobian lower bound, a coarea lower bound, strip-hitting
richness, and a uniform constant across the rescaling family. This paper uses
that package only as a named target until the constants are accepted in the
exact theorem form required downstream.

The downstream route is now equally explicit at theorem grammar level. The
current repo records a candidate `A5-A9` package with the following shape:
`A5` kappa-bias vanishing from asymptotic stationarity and A4 richness,
`A6` defect-from-critical coercivity through pointwise-to-Abel transfer,
leakage accounting, transport control, and commutator budgets,
`A7` a Gronwall depletion threshold,
`A8` a scale-monotonicity recursion,
and `A9` the CKN/BKM contradiction.
This sharpens the manuscript’s dependency story. It does not change the live
frontier: the paper still treats `A1/A3` and `A4` as the actual theorem walls.

## 5. A7-A8: depletion and scale monotonicity

Assertion `A7` is the depletion step. Once the defect has been localized and
the leakage reduced, the remaining nonlinear production must weaken as the flow
enters the rich support region. Analytically this means the stretching or
cascade term gains a multiplicative factor strictly below the naively critical
value. The paper does not need to identify a unique depletion mechanism at this
stage; it needs a theorem-sized statement that the localized defect cannot
retain full critical strength across the ESS subsequence.

Assertion `A8` is scale monotonicity. The required monotonic quantity can be a
frequency-envelope budget, a rescaled defect mass, or a CKN-style density. The
essential feature is monotone improvement from the `A4-A7` input scales toward
the final continuation scale. This prevents the argument from winning at one
radius only to lose the gain after rescaling.

> **Proposition 5.1 (constants compatibility, full ladder).**
Sections 4-6 use the same ordered radii

```text
r_4 < r_6 < r_7 < r_8 < r_9
```

and the same nested smallness ladder

```text
eps_9 << eps_8 << eps_7 << eps_6 << eps_4.
```

To make the ladder explicit, it is enough to impose the following compatible
budget:

1. `A4` richness yields at least `8 eps_6` of normalized slack.
2. `A6` leakage consumes at most `2 eps_6`.
3. `A7` depletion consumes at most `eps_7`, with `eps_7 <= eps_6`.
4. `A8` monotonicity loses at most `eps_8`, with `eps_8 <= eps_7/2`.
5. `A9` closure requires a final reserve `eps_9`, with `eps_9 <= eps_8/2`.

Under these inequalities the retained reserve is at least

```text
8 eps_6 - 2 eps_6 - eps_7 - eps_8 - eps_9 >= 3 eps_6 > 0,
```

so the radii and smallness constraints are jointly satisfiable with explicit
slack. This is the constants-compatibility point the draft must carry in prose:
the later closure assumptions do not overconsume the gains created earlier.

In sum, `A7-A8` preserve a positive quantitative reserve rather than a
qualitative hope, so the continuation step can consume a real budget.

The same information can be read as the constants table consumed by the final
closure:

| Stage | Input scale or parameter | Budget role |
| --- | --- | --- |
| `A4` support richness | `r_4`, `eps_4` | creates at least `8 eps_6` of normalized reserve |
| `A6` defect-from-critical coercivity | `r_6`, `eps_6` | consumes at most `2 eps_6` through leakage, transport, and commutators |
| `A7` depletion | `r_7`, `eps_7 <= eps_6` | consumes at most `eps_7` in the Gronwall step |
| `A8` scale monotonicity | `r_8`, `eps_8 <= eps_7/2` | consumes at most `eps_8` while moving to the closure scale |
| `A9` CKN/BKM closure | `r_9`, `eps_9 <= eps_8/2` | requires a final positive reserve |

## 6. A9: CKN/BKM closure and contradiction

Assertion `A9` converts the retained reserve into a continuation theorem. Once
the defect budget remains strictly below dissipation at the final radius, the
localized quantities entering either a CKN epsilon-regularity statement or a
BKM continuation criterion become subcritical. The contradiction is then
standard in form: a first singular time cannot exist if every ESS blowup
subsequence yields a strictly improving high-tail budget.

What remains open is precisely what the current diagnostics already indicate:
the nontrivial issue is not low-high transfer but the genuinely near-diagonal
high-high obstruction. This draft therefore presents Paper 1 as an analytic
reduction manuscript with a sharp frontier, not as a proof of global
regularity.

In sum, `A9` closes the reduction theorem by converting the retained reserve
into the CKN/BKM contradiction promised in Theorem 1.1.

## Appendix A. Historical obstruction context

The older theta and danger-shell diagnostics remain useful as historical
evidence that the obstruction sits at the high-high seam. They are not used
here as proof certificates. Their role is to justify why the present paper
prioritizes ESS localization, Abel-defect bookkeeping, and leakage-aware
closure rather than a tail-only numerical threshold.

## Appendix B. Candidate constant table

The following values are diagnostic targets for the `A1/A3` acceptance
question. They satisfy the ladder shape of Proposition 5.1, but they are not
promoted as theorem inputs until the associated compactness, Seregin/ESS rate,
and Abel-summation estimates are accepted in the exact norm consumed by the
reduction.

| Candidate item | Candidate value or role | Promotion boundary |
| --- | --- | --- |
| ESS/Seregin intake | `epsilon = 1/6` | candidate rate intake only; not an accepted theorem input here |
| Stationarity rate | `delta_r = O(r^(1/12))` | target rate for `A3.3`; must survive the Abel-weighted norm |
| Abel summation | explicit multiscale constants | must close `A3.4` without hidden exponent loss |
| Constants ladder | compatible with `eps_9 << eps_8 << eps_7 << eps_6 << eps_4` | diagnostic compatibility with Proposition 5.1, not a proof of `A1/A3` |

## Appendix C. Formal-support appendix

The paper-facing theorem-variable manifest is generated by
`scripts/generate_paper_proof_manifest.py` and recorded at
`Docs/papers/generated/core_papers_theorem_var_manifest.md`. For Paper 1 it
indexes the normalized theorem interface
`DASHI/Papers/NavierStokes/TheoremInterface.agda`, including the `A6`, `A7`,
`A8`, `A9`, final-status, and terminal false guard surfaces. The manifest is a
formal-support index for the manuscript interfaces; it does not promote the
analytic `A1/A3` and `A4` frontiers to accepted PDE theorems.

## Appendix D. Claim boundary table

| Proved in this paper | Assumed externally with citation | Explicitly left open |
| --- | --- | --- |
| The reduction theorem `A1-A9` is organized as a single analytic route from tail-flux domination to continuation closure. | Leray-Hopf existence theory (`LerayHopf`) supplies the solution framework. | Any unconditional proof that all `A1-A9` hypotheses hold for every 3D Navier-Stokes solution. |
| Proposition 3.1 reduces the obstruction to a near-diagonal Abel-defect shell window. | Coifman-Meyer paraproduct technology (`CoifmanMeyer`) supplies the standard bilinear bookkeeping surface. | Quantitative Abel-defect-measure construction and the coupled `A1/A3` stationarity bootstrap in the exact norm consumed later. |
| Proposition 4.1 proves compatibility of the support radii and leakage/coercivity thresholds once `A4-A6` are granted. | The candidate physical-to-Fourier richness route is routed through `LeiRenTian2025` only if upgraded to the exact quantitative theorem consumed here. | The uniform `A4` Lei-Ren-Tian output-support transfer constant across Type-I rescalings. |
| Proposition 5.1 proves the full constants ladder is jointly satisfiable with explicit slack. | CKN epsilon regularity (`CKN`) and the Beale-Kato-Majda continuation criterion (`BKM`) are used for the final continuation contradiction. | Any global smoothness theorem for 3D Navier-Stokes or any claim of Clay resolution. |
