# Navier–Stokes proof-control record — 15 September 2026

Status: active proof-search control document; non-promoting.

This document replaces neither the historical roadmaps nor their source
owners. It records the current division of labour and active search priority
so that work is not sent back through the entire historical round graph merely
because that graph remains valuable donor material.

Timestamped nomenclature correction: `2026-09-15 09:32 AEST (UTC+10)`.

## Objective and operating rule

The objective is to solve the unforced DASHI Navier–Stokes programme with
actual proof receipts while independently verifying and integrating the released
forced-breakdown sources. The complete Agda, Lean, archived, and published
corpus is active proof material and searchable donor space. Historical routes
are maps, not mandatory premises: a worker may bypass, strengthen, or replace
one only by recording the exact endpoint, hypotheses, consumer, provenance,
and relation to the displaced route.

No statement may be promoted from source provenance, a Boolean ledger, a
conditional compiler surface, or a similarly named theorem.

## Four distinct proof lanes

The lane names are fixed as follows:

```text
A — unforced whole-space R^3 regularity
B — unforced periodic T^3 regularity
C — forced whole-space R^3 breakdown
D — forced periodic T^3 breakdown
```

The transfer firewalls are load-bearing:

```text
periodic B proof progress does not imply whole-space A proof progress;
whole-space A proof progress does not imply periodic B proof progress;
released forced C/D results do not settle either unforced A or unforced B.
```

A theorem may cross one of these boundaries only through an explicit typed
same-object/transport theorem with its hypotheses and authority recorded.

### A — unforced whole-space R^3 regularity

A is an independent regularity obligation. The current programme must first
freeze the most advanced whole-space producer/compiler/terminal-consumer cut
before resuming named-field proof search. No periodic B theorem is credited to
A without an explicit transfer theorem.

Current control status:

```text
whole-space terminal cut frozen             no
periodic-to-whole-space transfer constructed no
A proof search                               independent / named-field only after cut freeze
```

This lane may reuse general commutator, Taylor, harmonic-analysis, or geometric
donors only where their actual theorem statement is carrier-independent or a
separate whole-space realization is constructed.

### B — unforced periodic T^3 regularity

B is the current active construction lane. The principal route is the literal
periodic signed/helical route:

```text
R571 exact signed helical multiplier-difference carrier
  -> literal centered/Taylor y,-y realization while sign/phase is intact
  -> old paired second-order identity
  -> finite second-moment payment
  -> six-three scale arithmetic
  -> signed inner-fibre payment
  -> R545/R567 full-square transport
  -> R568 CommutatorOnlySpacetimeBudget568
  -> R572 compiler
  -> R503/R415 critical-barrier consumer
```

The immediate mathematical priority is therefore the centered/Taylor
realization and its old second-moment/six-three transplant, not generic positive
Gram scalarization. The positive R576/R577 routes remain valid fallbacks.

Exact status:

```text
C_direct constructed                         yes
R571 signed carrier                          constructed
R571 radial A1/A2 geometry                   constructed (Lean receipt 5fb665d1)
paired second-moment real-carrier transport  constructed given G1/G2
state-side G1/G2 envelopes                   open
R568 commutator-only spacetime producer      open
R572 compiler                                constructed given its receipts
R503 R500->R415 compiler surface             constructed
periodic/global regularity promotion         false
```

### 2026-09-15 Aristotle Lean receipt — exact scope

The dedicated NS worker receipt was based on `dashi_lean4` source commit
`63fa6af1d45680e9d618e9e2c59d49ed5873ce56`; its active Lean intake is
recorded separately in that repository.
It supplies Lean theorems for the **geometric** B-carrier Gate-A constants,
not an endpoint payment:

```text
0 ≤ ||k+y|| - 2||k|| + ||k-y|| ≤ ||y||² / ||k||
```

Thus the periodic nonzero-mode realization has radial constants `A1 = 1` and
`A2 = 1` independently of the Galerkin cutoff.  It also supplies the exact
real paired-second-moment transport conditional on the state-side `G1`/`G2`
envelopes, and a helical-vertex antiparallel cancellation/output-gain theorem
for the heterochiral rows.  These are active Lean proof material, not merely
an archive observation.

The following boundaries remain explicit:

```text
G1/G2 state-side envelopes                    open
R574-style c_A dissipation identification     open
pair-resolvent c_B / bounded Gram factor      open
TOE network-forcing M1                        open
R568 and its A1ChannelObligation              open
independent phase-production leaf             open
periodic regularity                           false
whole-space A / B-to-A transport              untouched
```

The source-local TOE proposition labels `A1`/`A2` are distinct from the
B-carrier radial constants named `A1`/`A2`; no conclusion was relabelled or
transported across that collision.  The worker also supplies only a Lean
mirror/crosswalk of `DASHI.Core.ProofDebtRouterExact`, preserving that Agda
owner as canonical.

### Historical/provenance B attempt — same-output Gram / P3

The R179/R181/R201/R205/R207/R209/R211 line and merged PR #890 are retained
append-only as theorem-bearing history. They established, among other things:

```text
partner-first compression;
same-output between-partner Gram debt as the exact residual;
PSD compressed-cell difference carrier;
complete-graph pair-difference/Gram-debt algebra;
R214 constant-band localization no-go;
R211 as the correct quantitative residual-payment consumer socket.
```

This route is no longer the primary B producer search. The reason is recorded,
not hidden: the exact amplitude telescope exposed a many-to-one observable map.
Distinct same-output incidences can carry equal velocity arguments and hence
equal compressed slot kernels, so incidence geometry alone cannot supply the
uniform lower pair-separation required to pay positive Gram debt. The route is
therefore retained as historical/provenance infrastructure and as a negative
control against future proposals; its theorem-bearing algebra remains reusable.

This abandonment does **not** assert that all signed Gram/resolvent approaches
are impossible. It records only why the generic P3 lower-separation route is no
longer the primary producer.

### C — forced whole-space breakdown

The repository's current source observation records a released forced
whole-space breakdown root. Work here is BIDI verification, source lineage,
dependency closure, exact hypothesis matching, and same-object carrier
integration. It is not a discovery route for A or B.

Preserve source observations append-only. A newer source snapshot refines a
prior observation; it does not erase the earlier one.

### D — forced periodic breakdown

The repository's current source observation records a released forced periodic
breakdown root. Work here is likewise BIDI verification, source lineage,
dependency closure, exact hypothesis matching, and same-object carrier
integration. It is not evidence that unforced periodic B is proved or refuted.

## Priority order

```text
P0  freeze historical/provenance ledger for A/B/C/D
P1  B: construct literal R571 centered/Taylor realization
P2  B: drive old second-moment + six-three machinery on that exact carrier
P3  B: propagate toward R568 until the first real analytic obstruction
P3p A: in parallel, freeze A's independent producer/compiler/terminal cut
P4  A: thereafter search only forward from named unpaid fields
parallel C/D: BIDI verification + exact provenance integration, non-discovery
orthogonal: certification receipts and observed commit-specific checker status
```

Operating rule:

```text
never restart broad archaeology as a proof step;
search forward from a named unpaid field;
retain failed and superseded routes as historical/provenance evidence.
```

## What is donor material, not mandatory rework

Do not spend the first B proof-search pass rediscovering Fourier
representation, signed commutator algebra, Waleffe geometry, primitive R574
control, fibre/global aggregation, resolvent symmetry, spectator rows,
transpose/full-square collapse, the `C_direct` identification, or the
R145-to-R584 archaeology. Search and reuse them where their actual consumer
factors through the existing periodic carrier.

The same rule applies to A: reuse only through an explicit whole-space or
carrier-independent theorem, never by label similarity.

## Required delivery discipline

For every new result or proposed replacement, report:

1. lane A/B/C/D;
2. exact theorem endpoint and consumer;
3. source/Agda/Lean lineage and any same-object map;
4. hypotheses and axiom/authority receipt;
5. whether it pays the active lane, a transfer theorem, C/D verification, or
   only infrastructure;
6. MathematicalStatus, StatementStatus, and CertificationStatus separately;
7. the remaining unpaid seam.

Completion means actual proof receipts for the named payment(s) and their
consumer composition, not another inventory. No C/D result may be treated as
an A/B result merely because all concern Navier–Stokes.
