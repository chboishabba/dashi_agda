# Exact physical pressure recovery is not rank recovery (R734 N=2)

**2026-10-27.** Original source: PR #1271's real six-mode positive-helicity Galerkin datum `tests/test_ns_r734_pure_plus_physical_w2_no_go.py`, Waleffe 1992 triad physics and the classical incompressible Navier–Stokes/Leray pressure reconstruction. NO independent turbulence law or regularity theorem is asserted.

For divergence-free periodic Fourier coefficients, define the convolution without the factor `i`:
`B_k = sum_{p+q=k}(q dot u_p) u_q`.

Diverging `partial_t u+(u dot grad)u = -grad p + nu Delta u` gives `-Delta p=partial_i partial_j(u_i u_j)`. With zero-mean pressure gauge, at every nonzero mode the **actual** pressure and projected force obey
`p_k=-(k dot B_k)/|k|^2`,
`F_k=-i(B_k+k p_k)=-i(I-kk^T/|k|^2)B_k`.

The new test applies the **same sharp cube cutoff N=2** to the original source data and force. It verifies an actually nonzero pressure, conjugate-mode reality, exact agreement with pre-existing `projected_NS_nonlinearity`, divergence-free projected force and `k cross (-i k p_k)=0`. Therefore pressure disappears as an **explicit gradient** under curl in the vorticity equation, but its elliptic reconstruction still constrains the velocity dynamics.

**Information-loss discriminator:** reversing the entire real field `u -> -u` keeps quadratic `B`, `p`, `F` invariant, while the cubic velocity-weighted transfer reverses sign. Flipping only the original `k,-k` phase keeps **each** squared modal magnitude and every Zipf/Lorenz/rank-only summary unchanged, but the actual reconstructed pressure coefficients CHANGE. Thus rank-only magnitude data do not determine pressure, much less signed critical transfer. These are physical algebraic tests on the original finite source, not vortex-like pictorial analogy, and do not establish critical coercivity or a singularity.

**Receipt:** `tests/test_ns_r734_pressure_poisson_source_parity.py` has **4 locally passing exact SymPy tests** against matching source helpers. With the five finite Zipf and six 3D Fourier-shell tests, the new tranche totals **15 passing local tests across three modules**. No exact entire PR-head suite, Agda/Lean kernel typecheck, pressure-tail absorption, live fleet statistics, or full Clay solution was obtained. Original source credit remains with classical NSE/Leray, Waleffe and the existing DASHI R92/R102/R691/R734/R735 owners. The original universal R734 W2 positive-margin hypothesis remains refuted; its conditional compilers remain separately valid.
