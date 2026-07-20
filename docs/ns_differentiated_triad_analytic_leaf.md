# NS differentiated-triad analytic leaf

This tranche inserts the missing normed analytic layer between the exact Fourier Biot–Savart triad carrier and the existing finite pair-incidence/weighted-Schur machinery.

## New theorem path

`NSDifferentiatedTriadAnalyticLeaf.agda` defines the actual projected Fourier interaction

\[
P_k\left(\left(B_p a\cdot q\right)b\right),
\qquad
B_p a = |p|^{-2}(p\times a),
\]

and the explicit local majorant

\[
|p|^{-2}|p||q|\,|a|\,|b|.
\]

The differentiated triad contains both placements

\[
P_k((B_p h_p\cdot q)u_q)
+P_k((B_p u_p\cdot q)h_q),
\]

and `differentiated-product-bound` proves its norm is bounded by the sum of the two corresponding local majorants.

The final theorem `concrete-differentiated-triad-bound` composes:

1. compact-Gamma numerator reconstruction and absolute-value control;
2. coefficient monotonicity;
3. the differentiated-product bound.

It therefore yields the pointwise local estimate required by the existing finite summation theorem.

## Supporting surfaces

The module also records the exact theorem-bearing interfaces required for:

- reality-pair folding, with completeness, soundness, conjugate incidence, and a no-double-counting law;
- target-energy tangent projection, preserving divergence freedom and zero target-energy derivative while controlling the correction norm;
- near-response reconstruction for the actual compact-Gamma numerator;
- cutoff independence, structurally, because the local theorem has no cutoff parameter.

## Boundary

The module is theorem-bearing but parametrized by the concrete norm/order laws of the scalar/vector carrier. It does not postulate a global NS estimate, a uniform shell tail, BKM closure, or Clay promotion. The next instantiation step is to inhabit these laws for the repository's rational/real Fourier carrier and feed the resulting local bound into the already-proved finite incidence and Schur transport chain.
