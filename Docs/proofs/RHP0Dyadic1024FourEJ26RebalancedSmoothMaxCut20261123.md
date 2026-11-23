# RH P0 — 4·256 = original dyadic q=16 cell 1024; 4E_j/26 collapse and exact rebalanced smoother (23 Nov 2026)

**P0 governing target:** original selected four-window W(t), original Zeta23 Weil prime/zero/Gamma/pole same-object expression, original t/16 physical scaling and independent signed strict terminal. This tranche advances **E0/E2 quantitative smooth-aperture admission**, NOT E3 strict RH sign. Original [DASHI PR #1533](https://github.com/chboishabba/dashi_agda/pull/1533) is draft on master and [Lean frozen source PR #116](https://github.com/chboishabba/dashi_lean4/pull/116) is draft on main. No Lean or Agda kernel or GitHub CI run. RH and GRH remain unproved.

## A. Source-reconciled geometric flags: equality, derivation, separation

The original RH q-tail owner is `DASHI/Analysis/RHQuartic163840DyadicTailHXIntertwinerExact.agda`, importing the original 15-bit capacity and odd-residue action owner with **no Monster 3B or RH-source group-action promotion**. Its actual continuous q-tail chart uses `q>8`, `v=(8/q)^5`, `v=(k+theta)/32768`, `k=0..32767`, real residual `theta∈[0,1)`. At **q=16**, v=1/32 and the original exact source boundary is **k=32768/32=1024**; the other 31,744 cells remain. Its measured tail integral is `1/(5·32768)=1/163840`.

In the PREVIOUS flat-top port (a=3/128,b=1/128, fixed symmetrical supports near ±log p, p=2/3), the first box halfwidth was **1/256**. The interval indicator at +log p has two distributional derivative jumps; at −log p another two. The FOUR jump boundaries give `||b_p''||1≤4·(1/(1/256))=4·256=1024`. Thus **1024 equals the original q=16 dyadic cell index**, as requested. This is an exact cross-source *number equality with independent proven meanings*. Changing only the bump smoothing widths changes the derivative bound while keeping q=16 at original k=1024; hence no canonical conjugacy, action, analytic equality of measures, or RH theorem follows.

The source 26-slot polynomial owner is `DASHI/Analysis/RHPrimeAperturePuncturedFactorChartExact.agda`, reusing the original `9+8+9` oriented punctured cube, J=scalar+26 carrier and native 13×sign axis chart. The original annihilator has 18 real quadratics and FOUR real quartics, not 26 real quadratic factors. Its 26 *majorant* quadratic slots have weights 9×1, 9×1/4 and two each at 1/14²,1/15²,1/17²,1/18². The exact elementary symmetric polynomial

```text
E(x)=(1+x)^9(1+x/4)^9 Π_(k=14,15,17,18)(1+x/k²)^2
    = Σ_(j=0)^26 E_j x^j,
q_j(t) ≤ E_j/r^(2j), r=t/16.
```

contains the **26 weighted coefficient grades**; multiplication by 4 in the old Sobolev bound `4 E_j` is the independent four-jump **total variation bound**, NOT an extra 4×26-site cube or an F4 representation. There are also **four independently selectable source prime ports** (two primes × two endpoints), a DIFFERENT factor of four in the worst-case sum. The physical original projective factor 4 and the 1/4 in the hyperbolic height defect must not be spuriously multiplied as new port counts.

## B. Use the same existing k=1024 as a CHOSEN dyadic smoothing reserve (new construction)

To exploit the user's 4·256 observation without inventing an action, coordinate the smoothing construction with the original dyadic index **as a transparent design choice**:

```text
a=3/128, total smoothing halfwidth b=1/128,
N=52=2·26 equal initial uniform-box kernels, each halfwidth
   h = 7/(52·1024);
remaining infinitely many uniform-box halfwidths
   h_(52+n)=2^(-n)/1024, n=1,2,...

52h + Σ_(n=1)^∞ h_(52+n)
  =7/1024+1/1024=8/1024=1/128=b.
```

Let `U_h(u)=(1/(2h))1_[-h,h](u)`. Their infinite convolution `η` is a compactly supported probability measure. For any fixed m, differentiate a finite collection of at least m+2 of the smoothable box kernels and convolve the remainder: every finite derivative is a bounded integrable function; the compact measure limit is therefore `C∞`. The distributional derivative `U_h'` has total variation exactly `1/h`, and convolution with a probability measure never increases that norm. The source even flat-top

```text
b_p(u) = (1_[-a,a]*η)(u−log p) + (1_[-a,a]*η)(u+log p)
```

has support `|u∓log p|≤1/32`, equals **one on** `|u∓log p|≤1/64`, `0≤b_p≤1`, and `||b_p||1=4a=3/32`. The same original even constant-coefficient normalized order-52 annihilator `Q_t(D)=A_t(D)/A_t(0)` produces `h_{p,t}=Q_t(D)b_p`, with exact source A1/A2/M2/M4/M6/M8/pole orthogonality and `h_{p,t}(log p)=1`, all other prime-powers zero, for EVERY fixed height t≥200. No 52-jet or numerical rank assumption. The original selected W remains the same original source input.

Define the rational **inverse box halfwidth**

```text
λ=1/h=(52×1024)/7
  =(2×26)(4×256)/7 =53248/7.
```

For every m=1,...,53, differentiate m−1 distinct initial equal-width boxes and one interval indicator:

```text
||b_p^(m)||1 ≤ 4 λ^(m−1).
```

This covers **all even derivatives through order 52** needed to bound the L1 mass of the 52nd-order corrected port. There is no factorial-square penalty. Unlike the previous `1/(256n²)` smoother, this source is especially economical at large m; it is NOT uniformly better at low m, because the new second-derivative bound `4λ` exceeds old `4·256`.

For true fixed-order physical Fourier estimates involving `h^(k)`, k=0,...,8, the worst derivative of b is `m=k+52≤60`. Define for m≥1 the fully explicit DYADIC-tail norm envelope, with `n=max(0,m−1−52)`:

```text
B_m =4 λ^min(m−1,52) * 1024^n * 2^[n(n+1)/2];
B_0=3/32.

||h_(p,t)^(k)||1 ≤ Σ_(j=0)^26 E_j r^(−2j) B_(k+2j),
k=0,2,4,6,8.
```

Thus even the sixth/eighth fixed-order **aperture** Sobolev constants are completely explicit (no unspecified high derivatives), though they can be enormous and do NOT prove the full oscillatory-profile/source-zero/Gamma FarExact inequalities.

## C. The real 4E_j/26 simplification — ONE original polynomial evaluation

For k=0 we obtain exactly the improved coefficientwise mass MAJORANT

```text
H_dyadic(r)
 =3/32 +Σ_(j=1)^26 [4 E_j λ^(2j−1)]/r^(2j)
 =3/32 +(4/λ)[E((λ/r)²)−1].
```

This is the essential new geometry: all **26 coefficient grades**, with the actual original punctured-27/9+8+9 weights, plus four interval boundaries, reduce to ONE evaluation of E. The 52 independent equal-box widths match the original degree52 differential operator's total order; the independent q-tail `1024` was used as the deliberate remaining smoothing capacity. **The 1024 is not an action intertwiner.**

An all-height source choice may take the more economical of the old and new C∞ port families at a given t:
`H_best(r)=min(H_old(r),H_dyadic(r))`. At r=32768, `H_old≈0.139318`, `H_dyadic≈0.0941771`; at r=65536 the old estimate `0.0937527` is slightly better than the new `0.0938358`. This NEGATIVE CONTROL prevents false claims of universal dominance. For each fixed t, either original-compatible b_p is admissible, so this minimum can be realized as a source-family **choice** (no claim of a smooth-in-t global parametrization).

## D. Exact target gates, four-port versus l1-selected geometry

The unchanged ORIGINAL selected W has the previous source floor (true mathematical gate, not kernel receipt) for t≥19440, r≥1215:

```text
m_W≥c(r)/r⁶>1/(100r⁶),
c(r)=567/(1600·24)−(28125/(4r²))(1+25/(4r²)).
```

The original true pole and endpoint L1 source bounds give, for each source prime port i,

```text
C_i≤K H_dyadic(r)/r,
K=6484375/7134511104≈0.0009088744702.
```

The four-port hyperbolic target condition remains `Σ_i |ε_i|C_i<64m_W`, and the original two-prime arithmetic coefficient remains source-exact, linear in ε if and only if original online A1/A2 are frozen.

**Full independent four-port cube** `|ε_i|≤r^-5` is admitted whenever `4K H_dyadic(r)<64c(r)`; positive rational coefficient monotonicity makes the first sufficient integer radius **r=5534, t=88544**, vs previous **r=26871, t=429936**.

**One active source port / l1-simplex**, `Σ_i|ε_i|≤r^-5`, is admitted under `K H_dyadic(r)<64c(r)`; the first sufficient integer radius is **r=5130, t=82080**. This differs from all-four-full-amplitude capability. By elementary `l1/l∞` duality, if the original source four-port signed prime response vector v(t,W) is nonzero, the optimal signed response over this l1 budget is `r^-5 ||v||∞` and can be achieved with ONE port of the appropriate sign. Nonzero v at each fixed t is conditional on the earlier properly selected sufficiently narrow original W and its source Fourier-response nondegeneracy; **no uniform-in-t positive v floor**, because cos(tlog2),cos(tlog3) approach a joint zero arbitrarily closely.

**Flat-top L1 cap** `H_dyadic(r)≤1/4` first holds at the sufficient integer radius **r=9621, t=153936** versus old r=31830,t=509280.

For all original t≥19440, even where H is huge, the **adaptive** four-port coefficients
`ε_i=κ_i/[r⁵(1+H_dyadic(r))]` with |κ_i|≤1 satisfy `Σ|ε_i|C_i<4K/r⁶<64m_W`. But this can heavily suppress arithmetic near the start of the range: at r=1215, `H_dyadic≈9.26×10²⁰` and attenuation ≈`1.08×10⁻²¹`. Near r=9621 attenuation ≈0.800; as t→∞ it approaches `32/35`. **Do not call the low-height adaptive source a useful prime-dominance witness simply because it preserves local target positivity.**

Exact local Python `fractions.Fraction` tests prove the coefficient expansion, plateau/support identities, formula collapse, threshold endpoints/monotonicity, all fixed k≤8 dyadic derivative constants, and negative-control crossover. Full independently executed script: `scripts/check_rh_p0_dyadic_1024_rebalanced_smoother_20261123.py` (working-container full version; a compact same-mathematics script is on PR #1533). Neither local execution nor source-written typed Agda/Lean is a kernel receipt.

## E. P0 boundary

**Paid mathematically:** exact *shared numerical* 1024 with separate derivations; explicit chosen dyadic smoothing reserve, actual source 52=2×26 order, 26 geometric weighted grades, collapse of 26 `4E_j` terms, improved uniform mass/target thresholds and complete fixed-order port Sobolev norm formulas through k=8. No extra real pole factorization, false signed antipodal quotient, Monster 3B identification, or F4 action.

**Still OPEN:** E0 Mathlib source-actual `C∞` carrier inhabitation and 52-fold adjoint proof; E1 source Lean kernel/axiom verification; E2 original complete FarExact/Schwartz/sixth/eighth and post-sixth costs **of the FULL oscillatory projective profiles and actual zeta zeros/Gamma**; E3 an independent strict signed completed inequality, overcoming the \(O(r^{-6}\log t)\) absolute zero/Gamma bound and near-double prime-phase resonance. No RH/GRH proof. No GitHub CI.
