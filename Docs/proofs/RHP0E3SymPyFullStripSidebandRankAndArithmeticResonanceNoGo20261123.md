# RH Clay P0 E3 — SymPy-first source-native sideband rank and arithmetic resonance min-cut (23 November 2026)

**Acceptance:** local SymPy and exact rational regression PASS. Not an RH or GRH proof; not a Lean/Agda theorem/kernel check. The positive statement concerns the constructed auxiliary frozen-prime aperture, **not** the actual set of zeta zeros. The negative statements show where zero-count-only or prime-phase-only arguments fail.

**Original owners, reused:** dashi_lean4@main Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleCutset.lean and ...FourierTerminal.lean (literal strict Clay-facing cut); Synthesis/RiemannSelectedPrimeSensitiveTwoScale.lean (original literal primes); frozen source draft Lean PR #116; DASHI Docs/proofs/RHP0NormalizedPrimeApertureE2UniformSobolevScale20261123.md (four original wavepackets); Docs/proofs/RHP0Dyadic1024FourEJ26RebalancedSmoothMaxCut20261123.md (actual auxiliary smooth plateau and derivative bounds). NO new Weil formula, Albert/J0 product or Monster operator is claimed.

## 1. Exact two-sideband matrix from the ORIGINAL frozen source

Physical scale r=t/16, horizontal a=Re(rho)-1/2, ordinate omega=Im(rho)-t. With original h=Q_t(D)b_p and frozen original on-line real A1,A2, define

\[
H_a(\xi)=\int_{\mathbb R}h(u)\cosh(au)\cos(\xi u)\,du.
\]

The exact source frozen prime-port response, including its original factor 4 and one cosine product-to-sum, is

\[
K(a,\omega)=2P_{\rm pole}\varepsilon
\{A_1[H_a(\omega+2r)+H_a(\omega-2r)]
-A_2[H_a(\omega+r)+H_a(\omega-r)]\}.
\]

At the two physical **test offsets** omega=r,2r (NOT a claim of actual zeta zeros there), the original source responds as

\[
\binom{K(a,r)}{K(a,2r)}
=2P_{\rm pole}\varepsilon
\begin{pmatrix}
H_a(3r)+H_a(r)&-H_a(2r)-H_a(0)\\
H_a(4r)+H_a(0)&-H_a(3r)-H_a(r)
\end{pmatrix}
\binom{A_1}{A_2}.
\]

The exact determinant is

\[
\Delta=[H_a(0)+H_a(2r)] [H_a(0)+H_a(4r)]
-[H_a(r)+H_a(3r)]^2.
\]

At a=0, original Q_t(D) has nine factors each at D=±ir and D=±2ir. The Fourier rule applied to h gives H_0(r)=H_0(2r)=0 EXACTLY, while H_0(0)=M=3/32 because Q_t(0)=1. Thus Delta=M(M+H_0(4r))-H_0(3r)^2. Symbolic product-to-sum, the 2x2 determinant and original polynomial notches independently checked in SymPy.

## 2. New effective full-horizontal-strip determinant bound

Use the previous *genuine source* coefficientwise majorant E(z)=(1+z)^9(1+z/4)^9 product over k=14,15,17,18 of (1+z/k^2)^2, with exact nonnegative coefficients E_j, j=0..26.

For the previously constructed even C-infinity flat-top b_p of support |u|≤5/4, mass M=3/32, primary smoothing inverse width lambda=52*1024/7 and infinite dyadic residual, retain the complete existing derivative bounds:

- B_0=M.
- For m≥1: B_m=4 lambda^min(m-1,52) 1024^n 2^[n(n+1)/2], n=max(0,m-1-52).
- C_k(r)=sum(j=0..26) E_j B_(k+2j)/r^(2j) for k=0,1,2,3.
- ||h^(k)||_1 ≤ C_k(r) and ||h-b_p||_1 ≤ eta(r):=C_0(r)-M.

Since cosh(|a|5/4)≤cosh(5/8)<2 for EVERY |a|≤1/2, we have H_a(0) between M−2eta and 2M+2eta. Three integrations by parts give |H_a(nr)|≤delta(r)/n^3 for n≥1, with

\[
\delta(r)=
\frac2{r^3}[C_3(r)+\tfrac32 C_2(r)+\tfrac34 C_1(r)+\tfrac18 C_0(r)].
\]

All terms are explicit positive rational sums with powers of r^-2; the two sufficient conditions eta≤M/8, delta≤M/16 therefore remain valid at all larger real radii once valid at one radius. Exact Fraction tests and a neighbouring failure give:

\[
\boxed{r\ge13576 \quad(t\ge217216):
\quad\eta(r)\le M/8,\quad\delta(r)\le M/16.}
\]

The conjunction **fails** at integer r=13575, so 13576 is the exact smallest integer radius for THESE sufficient inequalities, not the optimum possible analytic rank bound.

Set s=H_a(r)+H_a(3r), c=H_a(0)+H_a(4r), d=H_a(0)+H_a(2r). Then |s|≤M/8 and 11M/16≤c,d≤37M/16. Consequently, for every |a|≤1/2,

\[
\boxed{\Delta=cd-s^2\ge \tfrac{117}{256}M^2>0.}
\]

The infinity norm of the inverse observation matrix is ≤16/(3M). Thus, **for any actual nonzero original on-line response pair (A1,A2) and nonzero physical pole-port prefactor P_pole*epsilon**, we establish

\[
\boxed{
\max(|K(a,r)|,|K(a,2r)|)
\ge \tfrac38 |P_{\rm pole}\varepsilon| M
\max(|A_1|,|A_2|)
=\tfrac9{256}|P_{\rm pole}\varepsilon|\max(|A_1|,|A_2|).
}
\]

This establishes spectral *detectability* of one of two sidebands for the constructed frozen-prime aperture throughout the physical strip, NOT actual zeta zero occupancy nor the signed strict E3 terminal.

## 3. Rigorous insufficiency of unit-ordinate upper counts alone

The earlier E2 bound for added absolute zero+Gamma is O(r^-6 log t) using unit-width Riemann-von Mangoldt upper counts. To see why the LOG cannot simply be dropped by *using only those counts*, consider an explicit **non-zeta test ensemble**: a=0, model A1=1/r,A2=0, model P_pole=1, amplitude eps=r^-5. For a unit atom at model ordinate gamma=t+2r,

\[
|K(0,2r)|=\frac2{r^6}|M+H_0(4r)|
\ge \frac{45}{256r^6}
\quad(r\ge13576).
\]

A made-up multiset of m=floor(c log(t+3)) such atoms satisfies a unit-width O(log t) upper count and gives total absolute mass at least (45/256) m/r^6. This model may include mirrored negative-ordinate atoms with negligible far-frequency packet. **These are NOT actual zeta zeros or the actual selected W's response pair**, and they need not satisfy the prime/Gamma explicit formula. It is a mathematical countermodel ONLY to the implication "unit-shell upper count plus wavepacket Sobolev bound gives O(r^-6) without a logarithm". To remove the log for actual zeta, use extra genuine signed/arithmetical source information, not a smaller 26J coefficient.

## 4. Rigorous all-real-height two-prime phase no-floor

Let alpha=log3/log2. This is irrational: a rational equality would imply 3^q=2^p for positive integers. Irrational circle-rotation density then gives an unbounded integer sequence n with

\[
t_n=(n+\tfrac12)\pi/\log2,\quad
\cos(t_n\log2)=0,\quad|\cos(t_n\log3)|\to0.
\]

Independent SymPy at n=2437313 verifies t≈11046782.5605373, the first cosine exactly zero and the second magnitude about 4.5040909122593*10^-6. Therefore there is **no positive height-uniform lower bound** on max(|cos(t log2)|,|cos(t log3)|) for arbitrary REAL t. The real-height theorem DOES NOT show resonance on the unknown imaginary ordinate set of hypothetical off-critical zeta zeros. It refutes a prime-amplitude floor based on continuous height alone, nothing more.

## 5. Actual strict source theorem remains independent

The original signed Cutset and FourierTerminal establish, under a hypothetical off-critical target, target D≥2d and local slack S≥0. The proposed strict completed bound would require 2D+S<4d. Source-exact algebra says

\[
2D+S-4d=2(D-2d)+S\ge0.
\]

SymPy verified the equality, NOT the missing strict reverse estimate. More smoothing, splitting 32768 cells, puncturing 27, or phase-independent zero-count upper bounds do not derive the required sign.

**Concrete next P0 mathematical target:** a genuinely new signed arithmetic/zero-correlation result for the ACTUAL original zeta zeros and original W(t), strong enough to control the completed two-sideband plus Gamma/prime functional at off-critical mark heights. Respect multiplicities, reflection, all actual off-ordinate zeros and near-resonance; do not infer actual zeros at synthetic packet centres. If considering bounded detuning of the test centre to evade prime-phase resonance, first re-prove original target-pair positivity off the exact same-ordinate hypothesis; it is NOT currently part of the accepted Cutset.

**Execution:** existing source-equivalent local script scripts/check_rh_p0_e3_sideband_rank_resonance_20261123.py executed with SymPy and exact Fractions, including immediate predecessor and phase negative controls. Committed to same RH DASHI PR #1533. No Lean/Agda kernel or CI, no new original proof admission. RH and GRH remain unproved.
