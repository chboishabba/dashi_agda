# YM P0 — original CMP102 shifted A/B finite Cauchy endpoint weld
23 November 2026 · master-based PR #1536 · first source-written all-degree finite coefficient consumer. Original research CMP109 PR #1444 remains a distinct divergent branch.

## The same original source, not a substitute carrier

Let E(k)=expTerm(1,2k), O(k)=expTerm(1,2k+1), and A(k)=1/(2k+2)!, B(k)=1/(2k+3)!, using the **actual** Bishop exponential, Bałaban source factorial and original finite Cauchy summation constructors. In Agda:
`aCoefficient` is precisely the formula of #1444 `BalabanCMP109BishopRootFreeSeriesExact.aCoefficient`; `bCoefficient` likewise. Those definitions do not exist as imported symbols on this master-based branch; this is an identical underlying source formula, NOT a claim to have merged or kernel-checked the cross-branch definition identity. The existing prior #1536 `YMClayCMP102MasterPositiveABCoefficientSourceWeldExact` provides the actual shifted source equalities `E(suc k) ≃ A(k)`, `O(suc k) ≃ B(k)`, and the signed positive-even/negative-odd Cauchy row cancellation.

For all n≥0 define
- `Epart(0)=2A(0)`, `Epart(suc n)=2A(suc n)+C_n(A,A)`;
- `Opart(0)=1`, `Opart(1)=2B(0)`, `Opart(n+2)=2B(n+1)+C_n(B,B)`,
where `C_n` denotes `Row.cauchyCoefficient`, i.e. the ORIGINAL Fin(suc n) sum. Thus these formulas exactly reproduce the #1444 native `evenPart` and `oddPart` constructors on the same rationals/factorials.

## Actual finite Cauchy index identities, with endpoints kept

The original stdlib Fin `sum-init-last`, source `FinP.toℕ≤pred[n]`, and `NP.∸-suc` prove the **general source Cauchy last split**

`C_(n+1)(f,g) = C_n(f, shift(g)) + f(n+1)g(0)`.

Composing the existing original `Row.cauchyCoefficientSuccessor` gives

`C_(n+2)(f,f) = f(0)f(n+2) + C_n(shift(f),shift(f)) + f(n+2)f(0)`.

At f(0)=1 this gives `2f(n+2)+C_n(shift(f),shift(f))`. The degree-one branch is `2f(1)). Apply to E and O and the source shifted A/B factorial witnesses. The odd degree-zero case is the separate singleton `C_0(O,O)=O(0)²=1`. The negative sign is proved with the ORIGINAL `BishopSum.sum-cong-≋` and `*-distribˡ-sum`, not assumed from a finite numeric check.

### New source-written Agda declarations (not kernel accepted)

Module `DASHI/Physics/YangMills/YMClayCMP102OriginalEndpointCauchyShiftExact.agda`:
- `cauchySplitLast` and `cauchyTwoEndpoints`: original bounded Fin/signed source row index transport.
- `cauchyDegreeOneUnit`, `cauchyDegreeTwoPlusUnit`: original coefficient-zero=1 endpoint calculus.
- `evenInteriorOriginal`, `oddInteriorOriginal`: existing original Cauchy congruence applied to the shifted A/B expressions.
- `originalEvenRowIsNativeAPart` and `originalOddRowIsNativeBPart`: **both entire original positive-row equations** for ALL n, including n=0/1.
- `cauchyNegatedRight`: sign pulled through the native finite Cauchy row.
- `originalSignedEvenRowIsNativeAPart`, `originalSignedOddRowIsNegativeNativeBPart`: both original signed row-to-native A/B witnesses, not merely conditional signatures.
- `shiftedNativeBracketCoefficientZero`: **all-degree source-written bracket coefficient cancellation** using the existing original master signed row theorem.

The proof bodies contain no postulates or explicit missing row arguments. **But no Agda 2.9/stdlib pinned elaboration was run**. The entire imported graph including the `--safe` usage of original parity and non-safe finite Cauchy modules must pass an actual kernel check before calling these proved.

## Actual independent reference and negative controls

`scripts/check_ym_cmp102_endpoint_cauchy_20261123.py`, executed locally under Python `fractions.Fraction`, 17,281 / 17,281 exact checks for n=0..127. Categories: 128 A shifts, 128 B shifts, 128 even edges, 1 odd singleton, 1 odd n=1, 126 odd n≥2 edges, 8,128 even interior pairs, 8,001 odd interior pairs, 128 signed odd row identities, 128 complete even rows, 128 complete odd rows, 128 zero bracket results, and 128 omitted-even-endpoint negative controls. Exact executed file `git hash-object` = `d53a6f588e0ed9780a53be0be25641d146747389`, identical to uploaded GitHub blob. This is a **finite reference, not Agda acceptance or analytic convergence**.

## Next mathematical gates — no more generic parity helpers

1. P0.V: pinned Agda kernel typecheck and --safe/stdlib transitive import audit on exact #1536 module + original donors. Resolve real elaboration defects; no `machineChecked` flag substitution.
2. P0.CMP102 analytic: original SAME represented series `A(X), B(X)` for |X|≤1/4 and its finite Cauchy multiplication/continuity to infer `G(X)=1-2A-XA²+2XB+X²B²=0` from the all-degree bracket. Keep a literal source proof of convergence at the original radius without tightening it.
3. P0.CMP102 geometry: native Bishop quaternion pointwise unit norm and SU2 chord operator norm = normalized trace deficit, source CMP98 nonlinear averaging/Q and CMP102 original mixed-scale plaquette/minimizer domain.
4. Physical Clay P0 independent and dominant: original full 4D SU(N) Wilson/Haar/F19 global two marks → same original beta(a) CMP119/122 constrained T with ΩΛS/FP/Jacobian/R/E-R-B-V → source-evaluated absolute CMP116/W3 rooted two-support charges and cutoff/volume-independent positive SI decay → SAME noncollapsed interacting OS Hilbert H and spectral gap. The finite factorial identity does NOT pay any of these physical analytic inputs. Retain E1/D1/D2/N1/G1 OPEN.

Mathematical provenance: Cauchy, Newton; Bishop and Bridges; Murray/Csimma pinned Agda Bishop backend; original Bałaban CMP98/102/109/116/119/122; Wilson/Haar/OS and original DASHI contributor ownership. Do not promote a Clay result.
