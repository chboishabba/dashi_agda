# RH P0 — original punctured-27/26J indexing and SHARP inverse-radius coefficient envelope (23 November 2026)

**Original sources and attribution:** This is a **cross-owner INDEX/MAJORANT weld**, not a new Albert product, F4 representation, zero distribution theorem, or RH proof. Original punctured balanced-trit cube:
- `DASHI/Mathematics/Symmetry/Punctured27NineSheetBridgeExact.agda`: actual `T³\{0}` with **9+8+9** oriented cells and exact two-sided partial native-cube chart; only central `z=0` nine-sheet is punctured.
- `DASHI/Wikimedia/IbrahimTernary27OriginTraceless26AlbertShapeBidiExact.agda`: `27=1+26` scalar/non-origin bijection, explicitly no Jordan multiplication.
- `DASHI/Foundations/ExceptionalAlbertFreudenthalResidualExact.agda`: Albert `J` shape `27=1+26`, `dim F4=52=2·26`. These are carrier dimensions, **not** automatic operator intertwiners.
- `DASHI/Unified/HyperfabricPunctured27Projective13OrientationExact.agda`: actual **26 oriented sites ↔ 13 axes × Bool**, signed antipodes, not a silent quotient.
- `Synthesis/RiemannSelectedPrimeSensitiveFrozenApertureExact.lean` (Lean draft PR #116) and existing `Synthesis/RiemannSelectedPrimeSensitiveTwoScale.lean` (main): original selected physical source and its independent literal prime2/3 Weil terms.
- Prior E2: `Docs/proofs/RHP0NormalizedPrimeApertureE2UniformSobolevScale20261123.md`. The present calculation tightens its coefficient budget without modifying zero/Gamma normalization or the full P0 target.

## 1. Natural variable: 256/t² is *exactly* inverse radius squared

With `r=t/16>0` (the exact ORIGINAL normalized Wilson/RH four-window physical scale), set `x=(D/r)²`. Then `256/t²=1/r²`; no new guessed length or scale is required. The original even annihilator has actual degree **52 in D** and degree **26 in D²**, so its normalized polynomial has **27 coefficients `q_0,...,q_26`** with `q_0=1`. That constant is the distinguished *conditioned* scalar coordinate, not a second non-origin slot.

The ACTUAL factorization (not just a counting analogy) has:
- **9 genuine quadratics** `(D²+r²)` (on-line first radius),
- **9 genuine quadratics** `(D²+4r²)` (on-line second radius),
- **4 real quartics**, each from one ORIGINAL pole frequency `ω=t±r,t±2r=(14,15,17,18)r`, with real parts ±1/2. Each quartic has degree 4 and positive coefficients in `D²` at high t.

There are therefore **18 real quadratic factors and four real quartics**, not 26 genuine real quadratic factors. For a bounding polynomial only, each quartic is dominated by **two virtual quadratic factors**, giving 9+8+9=26 bounding slots, with the middle eight matched to four antipodal axes of the original central punctured nine-plane. This is the precise mathematical status of the J/26 coincidence: a CHOSEN oriented coefficient-envelope chart on the existing 26 non-origin sites, NOT a canonical representation of F4 or an isomorphism between analytic factors and Jordan elements.

## 2. Exact four-frequency reduction and coefficientwise inequality

Let `δ=1/(4r²)>0` and `k∈{14,15,17,18}`. The original monic degree-four pole factor at physical frequency `k r`, after dividing by its constant coefficient, is EXACTLY

```text
F_(k,δ)(x)
 = 1 + 2(k²−δ)/(k²+δ)² * x + 1/(k²+δ)² * x².
```

This follows from
`((D−1/2)²+(kr)²)((D+1/2)²+(kr)²)=[D²+(kr)²+1/4]²−D²`,
and substituting `D²=r²x`. For t≥200, r≥12.5, `δ≤1/625<k²`, so all three coefficients are nonnegative. The exact differences from the simpler **geometric limiting quadratic square** have positive rational numerators:

```text
2/k² − 2(k²−δ)/(k²+δ)²
  = 2δ(3k²+δ)/(k²(k²+δ)²)  > 0,

1/k⁴ − 1/(k²+δ)²
  = δ(2k²+δ)/(k⁴(k²+δ)²) > 0.
```

Consequently **coefficientwise**, `0≤F_(k,δ)(x)≤(1+x/k²)²` in the nonnegative polynomial coefficient order. Since all factors have nonnegative coefficients, multiplication preserves that order.

The **sharp universal geometric 26-slot envelope** is:

```text
Q_t(D)=A_t(D)/A_t(0) = Σ_(j=0)^26 q_j(t)D^(2j),
E(x)=(1+x)^9 (1+x/4)^9
  (1+x/196)^2 (1+x/225)^2 (1+x/289)^2 (1+x/324)^2,
E_j=[x^j]E(x).

0≤q_j(t)≤E_j/r^(2j)≤binom(26,j)/r^(2j)
                =binom(26,j)*(256/t²)^j.
```

This upper bound is **coefficientwise sharp as t→∞**: δ→0 and each pole factor tends coefficientwise to `(1+x/k²)²`, so `q_j(t)r^(2j)→E_j` for every j=0,...,26. No smaller **t-uniform** coefficientwise constants than E_j work within this exact source family.

Exact independently executed Python `fractions.Fraction` verification compares all 27 coefficients of the actual normalized source against every E_j at t=200,300,1000,32768,1000000, and reconstructs E(x) EXACTLY from its 26 slot weights. These tests are illustrative; the *all-height* proof is factorwise above, not inferred from samples.

## 3. Stronger original 27=1+26 / 26=9+8+9 bookkeeping, with SIGN retained

Take the original balanced ternary cube `T³`, T={−1,0,+1}, with origin `(0,0,0)` distinguished. Its 26 other points are:

| Original z-sheet | # oriented sites | E(x) factor weights | Analytic owner |
|---|---:|---|---|
| z=−1 | 9 | 1 (×9) | first on-line radius r |
| z=0, excluding origin | 8 | 1/196 (×2), 1/225 (×2), 1/289 (×2), 1/324 (×2) | four ORIGINAL pole frequencies 14r/15r/17r/18r, two bounding slots each |
| z=+1 | 9 | 1/4 (×9) | second on-line radius 2r |

The central 8 sites form four actual antipodal `(x,y,0)↔(-x,-y,0)` pairs. Assign the four pole-frequency branches to these four antipodal pairs **by a chosen chart**, not as a native cube symmetry theorem. The outer sheets are swapped by global antipodal reversal but have DIFFERENT analytic weights 1 and 1/4; therefore the `26↔13×orientation` fibre must retain its orientation. Taking 13 unoriented classes as the only input would LOSE the two-radius distinction. Similarly, the 26 factor slots and 26 polynomial grades j=1...26 are TWO 26-element sets; neither their equality nor an equivariant identification follows from their common cardinality.

The native same-carrier typed index chart is now written in
`DASHI/Analysis/RHPrimeAperturePuncturedFactorChartExact.agda`.
It imports the original `Punctured27NineSheetBridgeExact.Punctured27Chart`, original punctured plane `PuncturedNineSheet` and exceptional J dimensional owner; assigns each original site an exact *integer DENOMINATOR* (1,4,196,225,289,324), preserves antipodal orientation and proves elementary `refl` count/denominator facts. It does NOT prove a coefficientwise rational inequality in Agda, and **Agda kernel has NOT run**.

This respects the original `J=RI⊕J0` 1+26 **shape**, but constructs no Jordan product, cubic norm, F4 action or 26-dim representation. It also does not identify the 27-coefficient vector with the 27 cube sites canonically.

## 4. Exact improvement and direct E2 consequence

The original `binom(26,j)` bound used **26 copies of the largest unit weight** and forgot the distinct geometry. The sharper E_j preserve all source positions:

```text
E_1 = 1294113017/114704100 ≈ 11.282186225252628
              vs old binom(26,1)=26   (2.3045× smaller).
E_2 ≈ 58.86254572770955 vs old binom(26,2)=325
              (5.52× smaller).
E_13 ≈ 2.9533089892702584 vs binom(26,13)=10,400,600.
E_26 = 1/4469951457296583229440000 ≈ 2.23716×10⁻25
              vs old binom(26,26)=1.
```

For the SAME fixed even C∞ flat-top prime bumps b2,b3 and the SAME physical source W, the exact fixed-order derivative bound improves uniformly to

```text
||h_(p,t)^(k)||1
  ≤ Σ_(j=0)^26 E_j*r^(−2j) ||b_p^(k+2j)||1.
```

A strictly sharper explicit sufficient threshold for `||h_p||1≤1/4` is

```text
T_b,sharp = max(32768,
    16 max_(p=2,3; j=1..26)
       (208*E_j*||b_p^(2j)||1)^(1/(2j))).
```

Indeed `||b_p||1≤1/8` and each of 26 remaining terms ≤1/208, so their sum ≤1/8. `T_b,sharp≤T_b,old` pointwise, since E_j≤binom(26,j). A *numerical value* of the original fixed bump's 52 derivative norms is STILL NOT certified, so do not invent an effective numeric height.

All previous physical E2 target and source scalings **remain valid** after this tightening: `d_W(a)≥(2393451/209715200) a⁴/r⁶`, port amplitudes `ε=κ/r⁵` are allowed eventually, and each literal prime2/3 response scales at most O(r⁻6). The four original Fourier sidebands at physical ordinate `γ−t=±r,±2r` still yield absolute zero+Gamma increment O(r⁻6 log t), NOT a strict negative signed bound.

## 5. P0 admission firewall / what this does NOT solve

**Established mathematically, checked locally:** exact source scaling `256/t²=r⁻2`; exact Fourier/pole frequencies; full 26-slot 9+8+9 bound; coefficientwise sharp all-height E_j; 27 coefficient degrees with distinguished q0 and exact support for original signs; stronger finite Sobolev/height threshold. This is a *geometric/symbolic improvement* in the ORIGINAL P0 source.

**Unpaid:** Agda kernel for new native site chart; Lean kernel for `primeAperturePuncturedShellMajorantSymbol` and normalized source; proof-carrying smooth E0 carrier inhabitation; explicit b_p derivative-norm numerical evaluation for T_b,sharp; ALL original E2 far/Schwartz/post-sixth source accepted with signed actual zeros+Gamma; and E3 **INDEPENDENT strict completed arithmetic/zero/Gamma bound** for each hypothetical off-line zeta zero, especially near-double 2/3 prime resonance and arbitrarily small horizontal displacement. The same Weil identity remains a nonnegative-gap obstruction; neither cardinality 52=2×26 nor improved Sobolev E_j produces an RH/GRH proof.

**Reproducibility:** Exact local Python `scripts/check_rh_p0_punctured27_geometric_majorant_20261123.py` in the DASHI RH PR; actual native typed chart on that branch, scalar inverse-radius and shell-envelope source in Lean draft PR #116. Both draft; no CI and no Lean/Agda kernel check.


## 6. 32768 geom-flag and 208:26 correction — adaptive polynomial, no artificial split

The ORIGINAL RH q-tail source `RHQuartic163840DyadicTailHXIntertwinerExact.agda` owns 32768=8⁵=2¹⁵ as an exact continuous dyadic cell capacity with residual θ and tail integral1/163840, not an analytic t threshold. In contrast previous t≥32768 for m_W was merely convenient. New original-source cosh bound removes it: for r=t/16≥1215, t≥19440, `m_W>1/(100r⁶)`.

The equality 208=26×8 is exact, compatible with native 26=9+8+9 punctured central8; the old **analytic** 1/208 came from allocating a chosen spare 1/8 (δ=1/32 bump support mass 1/8) among 26 polynomial degrees, not an invariant 208-dimensional action. With different δ or actual bump mass the allocation changes. It is replaced by a single sharp E-weighted positive H(r).

An explicit compact C∞ even plateau via infinite centered uniform-box convolution has all derivative norm bounds `B_m≤4·256^(m−1)((m−1)!)²`, exact mass3/32, support1/32, plateau1/64. Then `H(r)=3/32+Σ_{j=1}^{26}4E_j256^(2j−1)((2j−1)!)²/r^(2j)` majorizes ||Q_t(D)b_p||1; rational r31830 enters the sufficient H≤1/4 bound, while **r32768** is an optional original dyadic 15-bit checkpoint with H<1/7 (t524288). More usefully, adapting `ε_i=κ_i/[r⁵(1+H(r))]` pays all-strip local target positivity for EVERY t≥19440; no 208 or T_b height is needed. Exact regression and full theorem argument: [new source ledger](RHP0GeomFlag32768EqualSplit208AdaptivePrimeE2Source20261123.md). Neither this coefficient chart nor the dyadic-source cardinality gives an F4/Jordan intertwiner, a gamma/zero-action identification or the missing E3 negative sign. P0 remains OPEN; no kernel/CI.
