# Balanced-Ternary Verified Assembly

This note records the implementation pattern suggested by the attached verified-theories atlas: do not wait for one monolithic analytic completion when the practical consumers can be served by independently checked finite certificates.

The route is:

1. exact finite reconstruction for bounded objects;
2. certified enclosures for numerical values;
3. finite truncations with explicit geometric tail bounds;
4. finite-depth prefix/metric decisions;
5. finite-support energy calculations;
6. bounded-depth MDL search;
7. separate uniform, Cauchy, dominated-convergence, or statistical certificates before promoting any infinite or asymptotic theorem.

This bypasses an engineering blockage, not a mathematical obligation. Arbitrarily many checked finite instances do not alone prove convergence, topology equivalence, infinite-axis summability, or asymptotic MDL consistency.

The correct smoothness split remains:

- native non-Archimedean analysis on `Z_3` / open domains in `Q_3`;
- Euclidean/fractal analysis on the Cantor-like image of the depth embedding;
- no claim that native `Z_3` is a real smooth manifold.

The corresponding Agda surface is `DASHI.Physics.Closure.BalancedTernaryVerifiedAssembly`.
