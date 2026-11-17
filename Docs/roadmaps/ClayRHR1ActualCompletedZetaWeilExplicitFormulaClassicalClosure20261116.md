# RH R1 — actual completed ζ, all-term Weil explicit formula: CLASSICAL mathematical closure

16 November 2026. **R1 CLOSED as established classical analytic background only**, not native Agda/Lean construction and not a proof of RH. This note states an exact complete explicit formula on a genuine infinite-dimensional test family, with actual ζ zeros and every prime-power/gamma/pole term, not a synthetic spectrum or assumed positivity.

## Source audit and exact ownership

- \`DASHI/Analysis/RiemannZetaProgramBoundary.agda\`, blob \`c6f5bcce0a2e9661afb619fd3ffeea8dd788db1f\`: \`DirichletHalfPlaneWitness\`, \`EulerProductWitness\`, \`MeromorphicContinuationWitness\`, \`FunctionalEquationWitness\`, \`CriticalStripWitness\` are supplied record fields; only rational special values are constructed.
- \`DASHI/Analysis/DashiWeilRiemannBridge.agda\`, blob \`b5808f47141288b4f63a7e3b406c44d1a71b1887\`: \`CompletedZetaOwner\`, \`WeilExplicitFormula\`, \`WeilPositivityCriterion\`, \`DashiWeilIdentification\`, \`DashiWeilCompletion\` are supplied records; no \`MillenniumBridge\` inhabitant.
- \`DASHI/Analysis/RiemannMillenniumAssembly.agda\`, blob \`b94e8544f5e0a6f120ea961e6bdc3578148e9704\`: conditional assemblies require actual analytic/positivity producers.
- \`DASHI/Analysis/WeilPositivityCore.agda\`, blob \`9ace90b476b6f50dc7ec9dcd9c0eaf28840efabf\`: \`WeilPositiveDecomposition\` is a record with independently required positivity fields, NOT implied by an explicit formula.

## Genuine analytic carrier and actual zero set

For \(\Re s>1\), \(\zeta(s)=\sum_{n\ge1}n^{-s}=\prod_p(1-p^{-s})^{-1}\), with absolutely convergent series/product. The classical analytic continuation extends ζ meromorphically to C, with one simple pole at s=1. The actual completed function is
\[
\xi(s)=\tfrac12 s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s).
\]
Classical analytic continuation and gamma pole/zero cancellation prove ξ is entire of order one, satisfies \(\xi(s)=\xi(1-s)\) and \(\overline{\xi(\overline s)}=\xi(s)\). Its zeros, with multiplicity, are exactly the nontrivial zeros \(\rho\) of ζ in \(0<\Re\rho<1\). The **actual zero carrier** is \(Z(\xi)=\{\rho:\xi(\rho)=0\}\), NOT a surrogate spectrum, a numerical list, or an assumption \(\Re\rho=1/2\).

## Exact all-term Guinand–Weil formula on actual test space

Let \(g\in C_c^\infty(\mathbb R)\) be even and real-valued. Define
\[
h(r)=\int_{\mathbb R}g(u)e^{iru}\,du,\qquad
g(u)=\frac1{2\pi}\int_{\mathbb R}h(r)e^{-iru}\,dr.
\]
The Paley–Wiener test h is even, entire and rapidly decaying in each bounded horizontal strip; hence it meets the standard Weil explicit-formula test conditions. Write every actual nontrivial zero \(\rho=\tfrac12+i\gamma_\rho\), where \(\gamma_\rho\in\mathbb C\) **need not be real**. Let \(\Lambda(n)\) be the actual von Mangoldt function and \(\psi=\Gamma'/\Gamma\). The classical Guinand–Weil explicit formula, with the displayed Fourier convention, is
\[
\boxed{\displaystyle
\sum_{\rho:\xi(\rho)=0}h(\gamma_\rho)
=2h(i/2)
-g(0)\log\pi
+\frac1{2\pi}\int_{\mathbb R}
h(r)\psi\!\left(\tfrac14+\tfrac{ir}{2}\right)\,dr
-2\sum_{n=1}^{\infty}\frac{\Lambda(n)}{\sqrt n}\,g(\log n).
}
\]
The zero sum counts multiplicity. The formula uses all actual zeros without imposing RH. Since g has compact support, the prime-power sum is **finite** for each g; it is still the exact full arithmetic prime-power term, not a finite-prime truncation. The gamma integral converges absolutely due to rapid h decay. The zero sum converges absolutely by the classical zero-counting bound and rapid strip decay; the imaginary parts of \(\gamma_\rho\) are bounded by 1/2 because 0<Re ρ<1. The pole contributions are \(h(i/2)+h(-i/2)=2h(i/2)\), using evenness; \(-g(0)\log\pi\) and the gamma integral together are the exact archimedean contribution. The trivial ζ zeros are already absorbed by the completed ξ/gamma factor and therefore must NOT be counted again on the spectral side. This is an **all-term** identity, not an identity inferred from zero samples.

The integral may equivalently be written using \(\Re\psi(1/4+ir/2)\), since h is even and real on the real axis; the two integrals are equal by r↦−r and conjugation. No positivity follows from the formula.

**Independent classical source with exactly this Fourier normalization:** J. Brian Conrey, *The Riemann Hypothesis*, Les Houches lectures, section “Weil’s explicit formula”, https://aimath.org/~kaur/publications/58.pdf (the displayed theorem writes g(u)=(2π)⁻¹∫h(r)e⁻ⁱᵘʳdr and gives exactly the four terms above). A second independent Mellin-form source: https://empslocal.ex.ac.uk/people/staff/mrwatkin/zeta/riemann.pdf . The mathematical closure imports these **already-established** analytic theorems. It does not claim a new derivation or a native Agda proof.

## Why this closes only R1

R1's requested original completed ζ carrier and complete explicit formula exist classically with actual zero quantification and no spectral substitute. The explicit formula has prime-power, archimedean, pole and completed-zero terms, and no unlicensed sign assumption. The mathematical R1 background is therefore **classically settled**.

**R2 remains OPEN:** actual selected W A2 signed zero compensation is a new inequality not supplied by Weil's formula.

**R3 remains OPEN:** true ζ-zero fifth-correlation signed analytic producers are not supplied.

**R4 remains OPEN:** \(\forall\rho\in Z(\xi),\,\Re\rho=1/2\) does not follow from the identity. The Weil positivity criterion is an equivalence only; positivity itself must be established independently. No \`WeilPositiveDecomposition\` is constructed.

**Native R1 implementation remains OPEN:** \`CompletedZetaOwner\` and \`WeilExplicitFormula\` are supplied record fields, not inhabited with actual complex numbers, completed ζ, analytic integral and zero sum; no kernel receipts. \`native_kernel_acceptance=false\`, \`original_endpoint_proved=false\`. This is the same explicit classical-only gate protocol as H1, S1–S4. Do not claim the repository now has an unconditional \`DashiRiemannAssembly\` or \`MillenniumBridge\`.

Expanded portfolio after classical R1: **13/28 resolved, 15 OPEN; historical A–F 6/15 unchanged; original six Clay endpoints 0/6**.
