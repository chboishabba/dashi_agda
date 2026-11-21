# GRH P0 — original EveryCharacter → native terminals; reuse existing Mellin (2026-11-21)

## This is P0, not a CM/Monster/P1 spillover

The mathematical target is the external original **all-Dirichlet-character GRH**
in the author-published Lean v4.33.1 + Mathlib v4.33.1 source. It is stronger
than ordinary zeta RH. The available checked result is *Dirichlet L-functions
only*: it is **not** automorphic/elliptic Hecke GRH, nor BSD, nor a proof of
the Yang–Mills mass gap. The source author is **Levent Alpöge**, working
with Claude; independent verification attribution below is separate.

Existing Lean PR #113 exact ORIGINAL source consumers:
- `proofs/alpoge-lean433/RHGRHP0DirectionalSourceCut.lean`, source-original
  `every_character_of_original_galois_row : UpperTheory.EveryCharacter`
  by the original Gal.Int/RowSrc -> LiteratureTheorems route;
- `dirichlet_right_half_of_original_galois_row`:
  `DirichletLNonvanishingRightOfHalf`;
- `dirichlet_strip_of_original_galois_row`:
  `DirichletLZerosOnLine`;
- `primitive_strip_of_original_galois_row`:
  `PrimitiveDirichletLZerosOnLine`;
- `rh_of_original_galois_row`: Mathlib `RiemannHypothesis`;
- `MillenniumExternal/AlpogeRHBoundaryExact.lean`:
  original Mathlib `RiemannHypothesis ↔ Millennium.ClayRiemannHypothesis`
  (different root toolchain; requires trusted proof admission).
**Do not reimplement or rename `UpperTheory.EveryCharacter` or invent a
new character family.** The Lean #113 sources are independent adapter
proof candidates, not kernel-accepted in the local root.

Existing Agda #1533:
- `DASHI/Analysis/AlpogeGRHGeometricTransportExact.agda`:
  external *ordinary RH* source/zero/line proof-relevant transport;
- `DASHI/Analysis/AlpogeRHOriginalClayEndpointBidiExact.agda`:
  the ORIGINAL Clay-facing `RiemannHypothesisWitness` forward receiver,
  reverse `originalClayWitnessToAnalyticRH` consuming the literal
  `W.everyNontrivialZeroOnCriticalLine witness` projection, and a same
  selected-strip equality reverse endpoint. These are **RH-only**
  same-object welds and must NEVER be promoted to all-character GRH.
- `DASHI/Analysis/RHGRHDirichletConductorP0SourceCutExact.agda`
  distinguishes genuine primitive Dirichlet conductor from CM order
  conductor and modular level. Quadratic `chi_-3`, cubic finite Jacobi
  and algebraic elliptic CM Hecke `Psi` remain three different things.

## Important correction: the repository already has Mellin

Agda `DASHI/Mathematics/Automorphic/MellinSplitFunctionalEquationExact.agda`
**already proves** the algebraic split/functional-equation theorem
`mellinSplitFunctionalEquation`, given the original lower/upper analytic
change-of-variable equations. The actual analytic integral/complex
convergence is a source-realization requirement.

BSD conductor-32 already consumes it directly:
`EllipticCMLevel32FrickeMellinExact.mellinCentralLowerEqualsUpper`
and `mellinCentralValueIsTwiceTail`. So the **Mellin split compiler is
not a missing K4 producer**. The source still owes genuine same-E32 eta/
elliptic L-function analytic Mellin identification, distinct from GRH.

RH's deeper existing Mellin stack is also ORIGINAL:
- `DASHI/Analysis/RiemannG2GammaMellinImplementationRecoveryExact.agda`
  has the original selected Gamma/Mellin test implementation carrier;
- `DASHI/Analysis/RiemannG2MellinTestActionTransportExact.agda`
  transports to original Weil Test;
- `DASHI/Analysis/RiemannG2GammaMellinProofRelevantActionCompilerExact.agda`
  already proves `toProofRelevantCanonicalTestModulation`, with actual
  admissibility, spectral and transform-shift proof fields.

These sources are reusable **only with actual proof-relevant agreement
with the original nontrivial zeros of the specific Dirichlet L(s,chi)**.
They do NOT have that per-character analytic bridge today. Do not
construct a new abstract Mellin compiler or confuse a Gamma/Mellin
Weil action with proof of `EveryCharacter`.

## Exact original fork source check (no paraphrase of theorem quantifiers)

The *user's pinned original proof fork* was fetched directly at
`chboishabba/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
Git blobs match Lean #113 `fork_pin.json`:
- `src/Main.lean` blob `dbd5db70bc11b35f18fa5751216ab335321e7bfc`.
- `src/Statements.lean` blob `1cd1bce93344065936b2b392b23306254e0785ef`.

Original `src/Main.lean` (13 lines!) has exactly the five terminals:
`riemannHypothesis : RiemannHypothesis`,
`riemannZeta_eq_zero_re : RiemannZetaZerosOnLine`,
`LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`,
`LFunction_eq_zero_re : DirichletLZerosOnLine`, and
`LFunction_eq_zero_re_of_isPrimitive :
PrimitiveDirichletLZerosOnLine`.
They consume original `rhOfAll`, `allChi`, `claimAll.2.1`,
and `critAll` from the original imported `Supplements.Kernels.MainTheoremsAll`.

Original `src/Statements.lean` explicitly quantifies
`(N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)`
in each general Dirichlet proposition. Right-half nonvanishing
assumes `1/2 < s.re` and excludes the trivial-character pole case
via `(χ ≠ 1 ∨ s ≠ 1)`. The strip claim assumes `0<s.re<1`
and zero of exactly `DirichletCharacter.LFunction χ s`.
The primitive-specific claim additionally assumes `χ.IsPrimitive`.
This explicitly shows the theorem addresses **all nonzero moduli /
all characters** for the general statements, not just conductor 3,
the trivial zeta character, or one chosen CM example.

The new Lean #113 `all_original_grh_and_rh_endpoints_from_galois_row`
is an exact single-source consumer of all five target types. It
must still be compiled on its own v4.33.1 adapter context; its source
is NOT the original author's proof, which already has the full
independently reported external checks.

## External mathematical and kernel source status (as of 21 Nov 2026)

Original author note: https://alpo.ge/remark.pdf
Andrew Sutherland (MIT) independent verification:
https://math.mit.edu/~drew/grh/
Published Lean mirror / exact challenge:
https://github.com/Deicyde/riemann-hypothesis
Further independent build (Aapo Lipponen, LUMI):
https://github.com/aapolipponen/rh-lean-check-lumi

MIT report timestamp **20 Nov 2026 22:05 UTC**. It reports:
- Original **175,187 / 175,187 modules** compiled in Lean v4.33.1 and
  Mathlib v4.33.1, zero compilation errors.
- `#print axioms` for five original `Main.lean` headline theorems:
  only `propext`, `Classical.choice`, `Quot.sound`.
- Full per-module `leanchecker` kernel replay passed; independent
  `nanoda`, `con-leche` and `lean4lean` checks accepted.
  `con-leche --compare` matched the five original challenge statements.
- At the snapshot, the `lake comparator` full run and default/paranoid
  *export replay* were still running, not reported as passed.
- `RiemannHypothesis` is Mathlib's zeta nontrivial-zero statement;
  the extra GRH theorem scope is **Dirichlet L-functions only**.
- Archive SHA-256:
  `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
  `Main.olean` SHA-256:
  `9146dfb4148e24d2252e04c50742f3e49dd126dfcc5006d10bf5f873ddf796ad`.

LUMI independent 20 Nov compilation reports same `Main.olean` hash,
but *its own* axiom/dependency audit was marked running at its then
current status; MIT's independent successful checks are separate.

These externally reported kernel results meaningfully strengthen the
**external formal claim**, without supplying an in-repo trusted import
or original same-object Agda interpretation. None was run in this
session. Preserve external authorship and edition/version exactness.

## Source-to-consumer weld-forward: ONLY the remaining obligations

**P0.A** Materialize and hash-check the external original archive/oleans
in a permission-appropriate, isolated local environment, matching the
specific five statements and `UpperTheory.EveryCharacter`. Do not
copy the original author source into DASHI without permission.

**P0.B** Run locally compatible Lean v4.33.1 on the original
`RHGRHP0DirectionalSourceCut` with exact original source dependency
graph and `#print axioms`. The adapter has not been kernel checked here.
This must retain all-character scope, including primitive/nonprimitive
Dirichlet conditions as stated, not silently specialize to zeta.

**P0.C** Weld the verified original theorem into the separate root
Lean/Mathlib Clay target with a trusted statement-identical proof
admission. Version mismatch (external 4.33.1 versus root 4.35 rc/
Mathlib pin) is not resolved by importing a name or a `Set` flag.

**P0.D** For Agda, identify the literal completed Dirichlet L(s,chi)
analytic function, each genuine character and its conductor, its
nontrivial-zero predicate and real-part critical-line statement.
Show same-character bidirectional predicate transport for **ALL**
original Dirichlet characters, not just the zeta trivial character.
Only then promote all-character GRH in the target semantics. The
RH-only `ExternalRHGeometricTransport` is insufficient.

**P0.E** Keep RH, Dirichlet GRH, CM elliptic Hecke analytic identity,
selected BSD, YM and higher-rank universal problems logically distinct.
Consequences such as least primes or algorithms must use the exact
scope/quantifiers and original theorem rather than a headline claim.

**Acceptance categories:** external independent verification REPORTED
and source-linked; in-repo proof candidate SOURCE-WRITTEN; local
Lean/Agda kernel NOT RUN; same-object cross-kernel admission OPEN.
Round numbers, R445/F19, Monster/369 and numbered GRH research lanes
are iterations/donors, never independent proofs of the P0 target.
