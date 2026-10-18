# Tekum / Schlögl–Fey paper-completion max-cut design

Date: 2026-10-03
Branch: `research/tekum-balanced-ternary-20261002`
PR: #1083

## Purpose

Close as much of the two original-paper formalisation debt as possible without inventing semantics, hardware structure, or source claims not supported by the papers or existing repository machinery.

The implementation priority is the Hunhold/Tekum mathematical core. The p-adic and SSP/FRACTRAN material remains DASHI cross-pollination. The Schlögl–Fey lane is source-maximal: formalise the actual circuit only if the source exposes enough structure to do so faithfully.

## Current paid substrate

PR #1083 already contains or reuses:

- canonical `DASHI.Algebra.Trit` carrier;
- least-significant-first balanced-ternary positional evaluator;
- A003462 maximum-magnitude owner;
- exact `Trit ≃ Fin 3` and vector roundtrips;
- complete duplicate-free `(Fin 3)^n` enumeration and exact cardinality `3^n`;
- Tekum anchor interface and anchor-negation compiler;
- exact 15-regime codec, exponent-count rule, and bias table;
- structural NaR / zero / infinity classification;
- exact ordinary Tekum semantics in canonical repository `ℚ`;
- BF16/Tekum structural coordinate-role bridge;
- exact `Vec Trit n ≃ TriadicPAdicCodec.Kernel n`;
- executable p-adic `CylinderSystem` instance plus orientation firewall;
- involutive reversal / dual chart and conjugated truncation-composition law;
- ternary-27 stored-program execution through `TinyRadixNeutralRegisterMachine`;
- binary-coded ternary codec, signed-digit-adder semantic contract, SSP/FRACTRAN presentation, and FPGA empirical attribution receipt.

## Design principle

There will be one mathematical spine for Hunhold:

```text
balanced positional integer bijection
    -> concrete fixed-width int_n arithmetic
    -> concrete anchor/parser/inverse
    -> exact source-word -> ℚ decode
    -> Prop. 2 uniqueness
    -> Prop. 3 negation
    -> Prop. 4 monotonicity
    -> Prop. 5 nearest rounding
    -> no-double-rounding corollary
```

No downstream theorem may replace an upstream missing theorem with cardinality, enumeration, a Boolean receipt, or an abstract witness interface.

## 1. Balanced positional integer bijection

### Goal

Construct the exact same-object theorem

\[
I_n : T^n \simeq \{-A_n,\ldots,A_n\},\qquad A_n=(3^n-1)/2.
\]

### Required results

1. Reuse the existing `BalancedTernaryIntegerExact.eval` positional reading rather than adding a second evaluator.
2. Prove the evaluator range is bounded by the existing A003462 magnitude owner.
3. Prove injectivity of the positional evaluator.
4. Construct a centered integer decoder / reconstruction map on the reachable interval.
5. Prove both roundtrips.
6. Expose the interval cardinality as a consequence / consistency check, not as the proof of injectivity.

### Preferred proof route

Use the radix-3 recurrence

\[
I_{n+1}(t_0::t)=t_0+3I_n(t)
\]

and separation of the three residue classes modulo 3. If two evaluations are equal, their least-significant trits must agree modulo 3; cancel that digit and divide the remaining equality by 3, then apply induction.

The inverse should recover the unique balanced remainder in `{-1,0,+1}` modulo 3 and recurse on the quotient. The proof must use a repository-compatible integer representation and avoid machine `Int` or unchecked partial division.

### Expected owners

Prefer extending / adding focused owners under `DASHI/Algebra/` rather than bloating the existing files. Likely split:

- `BalancedTernaryPositionalInjectiveExact.agda`
- `BalancedTernaryCenteredReconstructionExact.agda`
- `BalancedTernaryCenteredBijectionExact.agda`

Exact names may be adjusted to existing repository conventions.

## 2. Concrete fixed-width Hunhold `int_n`

### Goal

Instantiate the current abstract `FixedWidthBalancedArithmetic n` with the actual finite balanced-ternary word carrier.

### Required operations

- word negation;
- positional integer decode;
- centered reconstruction / inverse;
- fixed-width wrapping addition;
- fixed-width wrapping subtraction;
- modulus / absolute-value operation required by Hunhold's anchor definition;
- all-ones word;
- proof `modulus (negate x) = modulus x`;
- exact source anchor `anc_n(t)=|t|-11...1` on the concrete word type.

Wrapping must be specified through the finite centered interval / `3^n` residue class, not through host-language overflow.

## 3. Source-word parser and exact rational decode

### Goal

Remove the remaining semantic gap between a source Tekum word and the already-existing canonical `ℚ` ordinary decoder.

### Required chain

```text
Tekum word
  -> special classification OR ordinary anchor
  -> exact regime
  -> dependent exponent/fraction split
  -> exact balanced integer exponent / fraction numerator
  -> OrdinaryTekum
  -> ExactTriadic
  -> ℚ
```

The parser must preserve the paper's digit ordering and field-length dependence. All field reconstruction / split-join properties required downstream should be theorem-owned rather than encoded as unchecked metadata.

## 4. Hunhold Proposition 2 — no redundant encoding

### Goal

Prove the source theorem on the same rational decoder:

\[
T_n(t)=T_n(u)\Longrightarrow t=u.
\]

### Proof structure

1. Separate special values from ordinary values.
2. For ordinary values, use the exact exponent/fraction representation.
3. Prove the fraction lies strictly inside the paper's interval, so each exponent occupies a disjoint open magnitude interval:

\[
\tfrac12 3^e < |T| < \tfrac32 3^e.
\]

4. Conclude equal nonzero ordinary values have the same sign and exponent.
5. Cancel the common power of three and prove equal significands have equal fraction integer codes.
6. Use balanced positional injectivity and anchor/parser roundtrips to recover the exact word.

The implementation should prefer exact rational inequalities over an ambient real-number theorem.

## 5. Hunhold Proposition 3 — negation

### Goal

Close the source-word theorem

\[
T_n(-t)=-T_n(t).
\]

### Existing ingredients

- trit involution;
- positional evaluator sign inversion;
- anchor negation invariance;
- external sign flip;
- exact triadic sign flip;
- denominator invariance.

### Remaining weld

Prove that parsing a negated source word preserves anchor fields and flips only the external ordinary sign, then transport this through the canonical `ℚ` decoder. Treat NaR, zero, and infinity according to the paper's exact special-value convention rather than assuming ordinary additive-group semantics for all specials.

## 6. Hunhold Proposition 4 — monotonicity / ordered-code theorem

### Goal

Prove

\[
I_n(t)<I_n(u)\Longrightarrow T_n(t)<T_n(u)
\]

under the paper's total order including special values.

### Structure

- prove the finite word order induced by centered balanced integer code agrees with the regime/sign structure;
- discharge negative / zero / positive / infinity / NaR boundaries explicitly;
- for ordinary same-sign values, reduce order to exponent then fraction order;
- reuse positional injectivity / reconstruction and exact rational order;
- avoid adding a second comparator whose semantics are not derived from the integer code.

If the paper's special ordering cannot be represented directly by `ℚ`, introduce a small ordered `TekumValue` wrapper whose ordinary branch delegates to canonical `ℚ` and whose special constructors encode exactly the source ordering.

## 7. Hunhold Proposition 5 — truncation is nearest rounding

### Goal

Upgrade the already-paid structural truncation law to the actual numerical theorem.

For the source precision reduction map `R_{n->m}`, prove the truncated anchor decodes to a closest representable lower-precision Tekum value under exact rational absolute distance.

### Required definitions

- finite lower-precision candidate set;
- exact rational distance for ordinary candidates, with source-consistent special handling;
- nearest / argmin predicate that permits ties only where the paper permits them;
- source precision reduction map reconstructed through the concrete anchor inverse.

### Preferred proof route

Exploit balanced-ternary cell geometry rather than brute-force enumeration. Truncating low anchor trits should identify the containing coarse cell; prove its representative is within half the lower-precision spacing and every other representable lower-precision candidate is at least as far.

Finite enumeration may be used as a regression oracle for small widths, but not as the general proof.

## 8. No-double-rounding theorem

Once Proposition 5 is closed, combine it with the existing structural identity

\[
R_{m\to k}\circ R_{n\to m}=R_{n\to k}
\]

to state the full numerical no-double-rounding result on the same decoder. This theorem should be a corollary, not a separate numerical implementation.

## 9. General wheel parity theorem

Close the current calibration-only surface with the general theorem

\[
4\mid(3^n-5)\iff n\text{ is even}.
\]

Preferred proof: parity of `n` controls `3^n mod 4` by the two-state cycle `1,3`; then subtract 1 modulo 4 after accounting for `5 ≡ 1 mod 4`. Reuse existing modular arithmetic machinery if available.

## 10. DASHI p-adic dual-chart completion

This lane is explicitly **not required by Hunhold**.

### Goal

Connect the finite reversal-conjugated Tekum projection to the executable `TriadicPAdicCylinderExact.refineKernel` operation.

### Required theorem shape

After choosing the exact finite chart/reversal orientation,

\[
D\circ P_{Tekum}\circ D
\]

must be proved equal to the appropriate finite cylinder refinement / repeated refinement, with dimension indices made explicit.

### Boundary

This proves a finite representation naturality theorem only. It must not assert that Tekum's real-number value is a p-adic value or that the two metrics/orders coincide.

## 11. Schlögl–Fey source-maximal circuit lane

### Goal

Formalise the actual circuit/network only to the extent exposed by the source.

### Source extraction checklist

Look for:

- signed-digit encoding used internally;
- per-digit truth tables / equations;
- carry or transfer signals;
- number of stages;
- LUT mapping assumptions;
- carry-chain primitive usage;
- recurrence / locality between neighbouring digits;
- resource formulas;
- timing / critical-path argument.

### If sufficient construction is present

Build:

```text
formal digit cell
 -> local correctness theorem
 -> n-digit network
 -> word-level semantic correctness
 -> explicit depth bound independent of n
 -> resource-count theorem matching the source model
```

### If insufficient construction is present

Do not reverse-engineer or invent the circuit. Strengthen only the attributed source receipt with page/equation/table provenance and leave the gate/network theorem open.

## 12. Testing and verification

Every new theorem tranche must be fail-closed.

### Static regression

Extend `scripts/check_tekum_balanced_ternary_static.py` with every new canonical owner and load-bearing theorem name. Continue rejecting:

- `{!!}`;
- `postulate`;
- termination escapes;
- placeholder markers.

### Small executable regressions

Add concrete widths (at least 1–4 where source conventions allow) for:

- centered integer roundtrips;
- all positional values are unique;
- reconstruction;
- anchor roundtrip;
- rational decoding;
- negation;
- ordered-code monotonicity;
- nearest-rounding comparisons;
- staged versus direct precision reduction.

These are regressions, not substitutes for the general proofs.

### Kernel / CI

Run the strongest available focused Agda gate on the exact PR head. If no executable Agda/CI gate is available, report that fact explicitly and do not claim kernel certification.

## 13. Attribution and authority boundaries

- Hunhold source mathematics must remain attributed to Hunhold.
- Schlögl–Fey circuit and empirical claims must remain attributed to Schlögl and Fey.
- New cross-pollination theorems connecting Tekum to p-adic cylinders, SSP/FRACTRAN, BF16 structural roles, repository ternary storage, or register-machine execution are DASHI constructions.
- Cardinality does not imply positional injectivity.
- Representation equivalence does not imply numerical identity.
- Finite p-adic chart naturality does not imply equality of real and p-adic semantics.
- Empirical FPGA timing does not imply a kernel-checked circuit-depth theorem.

## 14. Completion criterion

The Hunhold paper reproduction is considered mathematically closed when the repository has source-word-level machine-checked owners for:

1. balanced positional integer bijection / reconstruction;
2. concrete anchor arithmetic and parsing;
3. exact ordinary/special decode;
4. Proposition 2 uniqueness;
5. Proposition 3 negation;
6. Proposition 4 monotonicity;
7. Proposition 5 nearest rounding;
8. the resulting no-double-rounding corollary;
9. the general even-width wheel parity theorem.

The Schlögl–Fey reproduction is considered circuit-level closed only if the published construction is sufficiently explicit to derive a formal network and prove both correctness and the stated width-independent depth property. Otherwise the correct terminal state is a source-complete empirical receipt plus an explicit source-gated circuit residual.
