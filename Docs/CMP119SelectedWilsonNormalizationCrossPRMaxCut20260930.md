# Cross-PR selected Wilson/CMP119 normalization max-cut (2026-09-30)

## Source authority, attribution and scope

1. Kenneth G. Wilson, *Confinement of Quarks*, Phys. Rev. D **10** (1974), 2445–2459, DOI **10.1103/PhysRevD.10.2445** — origin of the Wilson plaquette action.
2. Tadeusz Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories. I*, Commun. Math. Phys. **109** (1987), 249–301, DOI **10.1007/BF01215223** — four-dimensional **small-field** coupling recursion, not a full nonperturbative existence proof.
3. Tadeusz Bałaban, *Convergent Renormalization Expansions for Lattice Gauge Theories*, Commun. Math. Phys. **119** (1988), 243–285, DOI **10.1007/BF01217741** — complete effective-density sector form; the published abstract's convergent-expansion conclusion is for **superrenormalizable models**.
4. R. Dashen and D. J. Gross, *Relationship between lattice and continuum definitions of the gauge-theory coupling*, Phys. Rev. D **23** (1981), 2340–2348, DOI **10.1103/PhysRevD.23.2340** — coupling convention and matching context.

Those are the original authors' claims. The normalization probes, rational sector subtraction and max-cut independence tests in this repository are **DASHI results**, not results attributed to the original papers or experimental confirmations. Provenance is **source revision + specific locator + selected basis + evidence → claim → consumer**, never an identifier alone.

## What is already in the two live Agda Yang–Mills branches

Compared Agda YM PR #1049 at `772fe7473d365b735d9ebca098be1d7151605087` and GRQFT PR #1050 at `2561aea7857487e97a07e1638faf98ed4a471b2c` before this tranche:

- `DASHI/Physics/YangMills/SUNWilsonAction.agda` implements the literal SU(N) plaquette expression, using certified matrix trace authority.
- `BalabanClayT4SUNWilsonActionConventionExact.agda` identifies the **repository's chosen** positive Wilson cost and inverse-square coefficient. The checked file blob is the same on both PR heads.
- `CMP119AntigravityWilsonPlaquetteBasisOrientationExact.agda` proves finite-symbolic +/− basis changes and the standard SU(2) bare factor-of-four conversion.
- `CMP119AntigravitySUNLiteralProbeWilsonNormalizationExact.agda` derives the coefficient from an actual nonzero SU(N) plaquette probe, **conditional** on identifying the selected CMP119 exponent with that literal action at the probe.
- `CMP119LiteralWilsonProjectorSignAuditExact.agda` retains the E/R/B/vacuum projector corrections. A two-coordinate symbolic coefficient carrier is **not** an evaluation of SU(2) matrices.
- The abstract CMP119 Eq.(2.23) action algebra contains an independent coefficient field. Its assembly identity alone does **not** establish the published trace/coupling normalization.

## New execution test: multi-probe signed Wilson normalization

`scripts/grqft_selected_wilson_normalization_audit.py` verifies *supplied* exact-rational, same-cutoff, same-source rows with a positive SU(2) cost

```text
W+(U) = Σp [1 - ReTr(U_p)/2]
u*g² = 1
c = (selected log-density exponent - (E+R+B+vacuum)) / W+(U)
c = -u (repository-unit convention), OR c = -4u (standard bare SU(2) convention)
```

for **at least two distinct nonzero Wilson probes**. It rejects inconsistent per-configuration coefficients, invalid normalized SU(2) trace ranges, missing sector decompositions, wrong positive/negative action convention, and factor-of-four mismatches. The output carries a SHA-256 of the input bytes and explicitly records that it does not prove physical source selection.

The inputs are *not* generated from a known physical CMP119 configuration table; a passing toy receipt is not source confirmation.

Usage:

```sh
python3 scripts/grqft_selected_wilson_normalization_audit.py selected-cmp119-wilson-probes.json --out wilson-probe-audit.json
python3 -m unittest discover -s scripts -p 'test_grqft_selected_wilson_normalization_audit.py' -v
```

The preexisting independent ten-symmetric-slot stress script `grqft_selected_finite_stress_exact_audit.py` must use a **separately established same-measure selected action**. It does not itself construct Lorentzian timelike stress or the continuum tensor.

## Physical acceptance tests (not currently discharged)

1. **Published source → input rows**: extract the exact CMP119 Sect.2 exponent/trace definition including Wilson basis and `g_k` convention; implement the actual SU(2) matrix evaluation at the selected cutoff and validate every E/R/B/vacuum sector *independently*. The two-probe audit tests an input, not this step.
2. **Selected finite-mode shell / epsilon**: compute the literal Ward/ghost/Haar determinant contributions and verified rational Brillouin interval enclosures, identify the exact physical finite `ell_k` and `epsilon_k`, then establish strict positivity from source-derived bounds. Generic P3G receipt packages do not discharge their own fields.
3. **Finite measure and stress**: derive the same selected density `ρ`, insertion `O`, and every metric derivative `DS, DO` from that action; check ten-slot connected numerators; prove Euclidean-to-Lorentzian `T00` and counterterms, conservation and convergence before referring to gravity.
4. **Gravity sign check**: `A_L = Θ_L + 2ρ_L`. For ordinary nonnegative weak-coupling YM E/B terms, `A_YM >= 0`. A repulsive result must prove a genuinely derived extra sector satisfying `A_extra < -A_YM`; an independently chosen warped target tensor or negative Euclidean trace does not suffice.
5. **Clay YM**: selected measure plus Wilson normalization cannot discharge uniform RG estimates, tightness on a common cylinder carrier, complex OS positivity or the mass gap. Lean YM PR #15 at `ef59a7b3e9211fc7b303a1f5018ed3e298074cd1` contains generic continuum/OS implications conditional on physical measure hypotheses.

## Boundary and verification

This document is an attribution/proof-dependency ledger and a companion to the two Python audits. No original Bałaban PDF equation has been independently extracted into an approved selected action representation in this tranche. The new Python tests were run on locally constructed toy inputs; **Agda kernel certification and physical source acceptance remain outstanding**.
