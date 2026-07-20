# Balanced-ternary continuous depth envelope

## Scope

This note records the paper-safe continuous formalisation of the repository's balanced-ternary / p-adic depth idea. The checked Agda surface is:

- `DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope`
- `DASHI.Physics.Closure.BalancedTernaryContinuousEnvelopeRegression`

It is intentionally connected to, rather than substituted for, the existing finite carrier and geometry lane:

- `DASHI.Physics.Closure.SSPPrimeLane369PAdicBridge`
- `DASHI.Physics.Closure.SSPPrimeLane369PAdicUltrametricBridge`
- `DASHI.Geometry.SSP369Ultrametric`
- `DASHI.Foundations.SSPPrimeLane369Refinement`

The pre-existing modules remain the canonical finite prime-lane and prefix-ultrametric route. The new module isolates the balanced-ternary analytic envelope used in the codec/MDL interpretation.

## Mathematical statement

Let

\[
T=\{-1,0,+1\},\qquad d=(d_0,d_1,\ldots)\in T^{\mathbb N}.
\]

A stream may be read as a balanced representative of a 3-adic integer

\[
z=\sum_{k\ge 0}d_k3^k\in\mathbb Z_3,
\]

with the usual caveat that the formal repository currently carries finite depth coordinates and prefix geometry, not an analytic construction of \(\mathbb Z_3\).

For a scalar model with \(0<\lambda<1\), define the intended Euclidean depth envelope

\[
\Phi(d)=\sum_{k\ge0}d_k\lambda^k.
\]

The sufficient separation condition

\[
\lambda<\frac13
\]

prevents a first differing digit from being cancelled by the entire remaining tail, and therefore supplies the intended faithful embedding condition.

The depth metric is

\[
d_\lambda(x,y)=\sum_{k\ge0}|x_k-y_k|\lambda^k.
\]

When the first difference is at depth \(n\), the intended analytic instance proves constants \(c_1,c_2>0\) such that

\[
c_1\lambda^n\le d_\lambda(x,y)\le c_2\lambda^n.
\]

The 3-adic distance is \(3^{-n}\). Thus the two distances express the same cylinder notion of nearness: agreement through deeper prefixes means greater proximity. This is a topology-by-prefix statement, not a claim that the continuous image is a smooth manifold.

## What is constructively checked

The Agda module checks without analytic assumptions:

1. the balanced ternary carrier and sign involution;
2. involutivity of sign reversal;
3. infinite streams as `Nat -> Trit`;
4. indexed finite prefix agreement;
5. finite truncation into typed trit prefixes;
6. equality of truncations under prefix agreement;
7. a syntax-level finite envelope \(\sum_{k<n}d_k\lambda^k\);
8. a generic finite evaluation recurrence for any supplied scalar depth-kernel model;
9. a typed first-difference witness;
10. depth-indexed MDL model classes and a minimal-effective-depth receipt.

## What remains an explicit analytic obligation

`ContinuousDepthEnvelope` requires an instance to supply:

- a scalar embedding and weighted digit metric;
- positivity and \(\lambda<1\);
- the stronger \(\lambda<1/3\) separation witness;
- convergence of finite approximants;
- cylinder continuity;
- first-difference metric bounds;
- injectivity;
- recovery of the prefix/cylinder topology from metric control.

Likewise, `WeightedSignalEnvelope` does not pretend that an infinite axis is automatically summable. Weighted \(\ell_2\) summability is an explicit receipt.

This design matches the repository's fail-closed convention: naming an intended analytic statement does not turn it into a theorem.

## Multi-axis signal interpretation

For an axis set \(\Omega\), each coordinate carries a stream \(d_{\omega,k}\), with

\[
\Phi(x)_\omega=\sum_{k\ge0}d_{\omega,k}\lambda^k.
\]

For finite \(\Omega\), ordinary finite aggregation is sufficient. For infinite \(\Omega\), an instance must establish the selected weighted \(\ell_1\) or \(\ell_2\) summability condition. Euclidean spectral or differential operators act on the embedded coordinate signal and may then be restricted back to the Cantor-type image; they do not make the original p-adic carrier a differentiable manifold.

## MDL interpretation

Depth \(n\) defines the model class that can see only the first \(n\) trits. Therefore:

- truncating depth is coarse-graining;
- activating deeper digits increases effective degrees of freedom;
- the complexity term prices that additional depth or additional active modes;
- the selected model is a receipt that fit cost plus complexity cost is minimal among candidate depths.

The robust bridge is a depth prior over nested model classes. No claim that a smooth norm by itself validates MDL is made.

## Canonical paper-safe summary

> Microstates are modeled as balanced-ternary digit streams, equivalently as a finite-prefix presentation of a 3-adic depth carrier. A Euclidean interface is specified by the depth-weighted envelope \(\Phi(d)=\sum_k d_k\lambda^k\), with \(0<\lambda<1\) and \(\lambda<1/3\) as a sufficient faithful-separation condition. First-difference depth controls the induced weighted metric and hence the same cylinder notion of nearness as the prefix ultrametric. Coarse-graining truncates depth, while MDL selects minimal effective degrees of freedom under a depth prior. Analytic convergence, injectivity, metric bounds, infinite-axis summability, and optimality remain explicit instance obligations.
