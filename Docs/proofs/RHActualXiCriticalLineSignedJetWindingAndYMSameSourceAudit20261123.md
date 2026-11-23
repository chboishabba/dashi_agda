# Actual completed xi critical-line crossing — signed jet, complex winding and Yang–Mills source-type nonpromotion

23 November 2026. Reuse original \(\xi\) reflection and RH #1533/Lean Riemann source; do NOT confuse imaginary response zeros with actual zeta zeros. Independently executed Python **mpmath 1.3.0 at 85 decimal digits + exact SymPy**, committed **byte-for-byte** reproducible checker [check_rh_actual_xi_horizontal_sign_crossing_ym_nozero_20261123.py](../../scripts/check_rh_actual_xi_horizontal_sign_crossing_ym_nozero_20261123.py), Git blob \`8c2052e768cfc0b3c067e943d46a08d2bc1d9e06\`. This is numerical testing, not a computer-assisted interval proof of original zeta-zero location/simplicity and not Lean/Agda/CI.

## 1. Actual analytic source law applies for EVERY ordinate, whether zero or not

Take the actual completed xi function
\[
\xi(s)=\tfrac12 s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),\quad
f_\gamma(x)=\xi(\tfrac12+x+i\gamma).
\]
The *actual functional equation* \(\xi(s)=\xi(1-s)\) and conjugation symmetry \(\xi(\bar s)=\overline{\xi(s)}\) give at every REAL \(\gamma,x\):
\[
f_\gamma(-x)=\overline{f_\gamma(x)}.
\]
Therefore \(\operatorname{Re}f_\gamma(x)\) is EVEN and \(\operatorname{Im}f_\gamma(x)\) is ODD, and \(f'_\gamma(0)\) is pure imaginary, irrespective of whether \(f_\gamma(0)=0\). In particular \(\operatorname{Im}\xi(\tfrac12+i\gamma)=0\) identically for all real \(\gamma\); this does NOT assert \(\xi=0\) there. Equivalently, writing the real Hardy-type completed axis profile \(\Xi(\gamma)=\xi(1/2+i\gamma)\), the real-ordinate derivative obeys \(\Xi'(\gamma)=i \xi'(1/2+i\gamma)\). The xi **horizontal** first jet is \(\xi_s'(s)\); it is NOT a physical YM time generator.

## 2. Numeric actual xi test and decisive negative control

Actual high-precision mpmath \`zetazero(1)\`, \`zetazero(2)\` and gamma=20; actual xi and horizontal complex derivatives computed at 85 decimal digits. Three +/- finite differences h=10^-3,10^-6,10^-8 verify complex reflection and odd imaginary slopes; near actual numerical zeros the selected \`h * xi'(s+h)/xi(s+h)\` tends to 1 (a simple logarithmic-derivative POLE, not midpoint cancellation).

| Height \(\gamma\) | \(\xi(1/2+i\gamma)\) | Im \(\xi'(1/2+i\gamma)\) | Numerical local xi winding |
|---|---|---|---|
| 14.13472514173469... | ~5.37×10^-89 (numeric zero) | +0.00138271908921625418 | +1 |
| 21.02203963877155... | ~1.30×10^-90 (numeric zero) | -0.00001774977620510226 | +1 |
| 20 | -0.0000366554277556 (NONZERO) | -0.00005876402587077539 | 0 |

For circles \(|s-s_0|=0.0003\), 128-step numerical phase accumulation yields winding 1 at BOTH genuine numerically selected critical-line zeros, but zero winding at gamma 20; no sampled circle values vanish. Numeric Jacobian of holomorphic map \(\xi:\mathbb C\to\mathbb C\) is \(|\xi'(s_0)|^2\): ~1.911912079683×10^-6 at first zero, ~3.150545553312×10^-10 at second, ~3.453210736541×10^-9 at gamma 20. Positive Jacobian at gamma 20 also does not mean xi vanishes. A proven simple holomorphic zero has local topological degree +1 for sufficiently small contours by standard analytic theory; these particular 128-sample finite-circle receipts are *numerical checks*, not a rigorous zero-count argument.

**Key zero-observer separation:**
(a) odd imaginary component crosses zero across the line at every \(\gamma\);
(b) an actual xi zero also requires its real component to vanish;
(c) an actual SIMPLE xi zero has a nonvanishing complex derivative and local winding +1;
(d) a cancellation zero of a selected log-derivative pair is a zero of NEITHER xi nor necessarily the full xi'/xi.

This is precisely the sign, residual, winding and source-type information that a Boolean/binary observation would forget. The original four-slot quartic Fourier test response, actual xi zero and observed Fourier notch remain distinct.

## 3. Reflected off-critical pole pair: source signature is an odd JET, not a xi zero

At one original gamma, assume two reflected hypothetical zeros horizontally displaced by ±a, \(a\ne0\). Their **selected principal-pole** contribution to completed \(\xi'/\xi\) at \(w=s-(1/2+i\gamma)\) is

\[
D_a(w)=\frac1{w-a}+\frac1{w+a}
      =\frac{2w}{w^2-a^2}.
\]

SymPy exactly verifies \(D_a(0)=0\) but \(D_a'(0)=-2/a^2\ne0\); coalescing \(a\to0\) yields \(2/w\), a POLE, not a zero. The individual xi zeros sit at the two poles \(w=\pm a\), while \(D_a\)'s midpoint zero is cancellation in a SELECTED logarithmic-derivative component. Other xi zeros/entire contributions mean the FULL \(\xi'/\xi\) need not vanish at the midpoint. The actual xi analytic function has NO artificially doubled zero there.

The independent exact countermodel \(P(z)=(z^2+\gamma^2)[(z-i\gamma)^2-a^2][(z+i\gamma)^2-a^2]\), \(\gamma=2,a=1/3\), is real even, satisfies the *xi-type* functional and conjugation symmetries, has SIMPLE critical zeros with first jet \(i\cdot580/81\), AND has four offcritical zeros. This is a SYMMETRY COUNTERMODEL, not xi itself or a surrogate for its Euler product, Gamma/prime or RH actual-zero source.

## 4. Latest RH #1533 signed proof status and source no-go

Latest native seven-bit RH 128=16×2×4 and Monster3B×SSP signed \(C_2^7\) keep neutral signed multiplicity outside the binary nonzero patch; H05 six-face gluing is finite carrier geometry, not a proven 7-way real \(\xi\) symmetry. The original Riemann marked \(W(t)\) and actual zero source retain Fourier q, physical gamma, sign, multiplicity, conductor/parity/Dirichlet character for GRH, Gamma \(\mu\), \`FarExact\`, sixth profile norm/tail and strict signed post-sixth target.

Current actual source terminal identities in the RH roadmap are \(\ H-I=2D\), with offcritical reflected target budget \(D\ge 2d\) and selected slack \(S\ge0\). Hence
\[
H+S-(4d+I)=2(D-2d)+S\ge0
\]
for the hypothetical off-line pair. Obtaining the required STRICT negative terminal cannot follow by merely rearranging those same inequalities; it needs genuinely independent source information. This algebra is exact SymPy-checked in the committed regression. Do NOT state it proves RH or that an independent source estimate is already present.

## 5. Yang–Mills source correspondence: same observational geometry, different operator

The already-constructed original \(\mathrm{SU}(N)\) Wilson/F19 witness in YM #1536 gives two genuine gauge-invariant fine plaquette trace first jets \(F'_+(0)=-F'_-(0)\ne0\) over exactly the SAME original 64 coarse \(W=UV\) holonomies (original 1024 links, 1536 plaquettes). The full finite continuous Haar F19 source even gives \(\mathrm{Var}_{\mathrm{Wilson}}(F\mid W)\ge e^{-24\beta}v_N>0\), \(v_2=1/4\), \(v_N=1/(2N^2)\) for \(N\ge3\). This is a real **fine-observer/non-factorability** result, not two zero fields, and source curve \(r\) is not physical YM time or the OS reconstructed H. The fact that actual xi has 2D complex winding and Wilson F a gauge-invariant tangent is a **shared consumer pattern**, not an intertwiner between the analytic \(\xi\) operator and the YM \(T(a)=e^{-aH_{\mathrm{OS}}}\) or CMP119/122/W3. Distinct physical dimensions, objects, sign conventions and exact inputs must stay typed.

Original Yang–Mills P0 status is source-audited independently in [YM original CMP119/122/W3/same-H status ledger](https://github.com/chboishabba/dashi_agda/pull/1536), not changed by this RH computation. Local mpmath and SymPy checks do not typecheck Agda or Lean.
