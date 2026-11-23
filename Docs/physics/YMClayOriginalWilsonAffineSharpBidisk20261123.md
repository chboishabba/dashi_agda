# YM P0 — sharp universal two-source original Wilson/F19 zero-free complex bidisk

Date: 23 November 2026. **Original source owners already on master:**
`YMClayOriginalWilsonAffineMarkedPartitionExact`,
`YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact`,
`YMClayOriginalWilsonPhysicalF19PartitionExact`, and
`Docs/physics/YMClayOriginalWilsonAffineComplexSourceUniformAnalytic20261122.md`.
No new Wilson Gibbs measure, nonlinear Bałaban T or gauge group is constructed.

## Actual positive conditional F19 source

For an original positive full SU(N) Wilson/Haar conditional fibre at fixed retained W, with original globally unique *real* fine marks F,G in [-1,1], all 64 F19 ordered bond pairs and 896 interacting spectators retained by their existing owner, set

```
K_W(s,t) = integral_original_fibre w (1+sF)(1+tG)
         = K0 + s KF + t KG + st KFG,  K0>0.
```

**New sharp mathematical conclusion (elementary original-source corollary):**

```
K_W(s,t) != 0 for all complex |s|<1 and |t|<1.
```

This replaces the prior *conservative* |s|,|t|<=9/100 complex zero-free disk; it does not supersede the prior REAL mixed-Hessian envelope. The universal open radius 1 is sharp for arbitrary positive bounded-mark probability laws, since one atom F=1 has a zero at s=-1. It need not be attained by a particular original Wilson conditional fibre.

## Exact angular-sector argument (no unjustified scalar factorization)

Fix complex |s|<1. Every original real F in [-1,1] yields
`1+sF` on the line segment between `1-s` and `1+s`.
The complex inner product of its endpoints is **strictly positive**:

```
Re((1+s) conjugate(1-s)) = 1-|s|^2 > 0.
```

Both endpoints lie in the right half-plane and subtend an angular interval of width strictly less than pi/2. All points of the connecting segment lie in that same narrow positive cone, with no zero. Repeat independently for t and G. Every product `(1+sF)(1+tG)` lies in an angular interval of width **strictly less than pi**, including correlated F,G. Rotate this entire product interval to put it strictly inside one open half-plane; its positive original Haar average then has strictly positive real part and cannot vanish.

This argument uses only original fibre positivity, bounded **real** marks and the SAME joint probability law. It neither assumes F and G independent nor exchanges noncommutative Wilson paths. The bound is uniform in cutoff, beta, volume and W whenever original K0(W)>0.

For unnormalized original Wilson deficits `J_F=1-ReTr(U_F)/N`, `J_G=1-ReTr(U_G)/N` in [0,2], the endpoint segment is between 1 and 1+2s. If |s|<1/2 then both endpoints have positive real part, the interval has angular width <pi/2, and the same result holds for |s|,|t|<1/2. A positive one-atom law J_F=2 has a boundary zero at s=-1/2, proving *universal* sharpness.

## Verification and negative controls

New executable: `scripts/check_ym_original_affine_sharp_bidisk_20261123.py`.
Exact Gaussian-rational implementation of the original four-corner positive-law polynomial with:
- all 255 nonzero four-atom integral positive weight laws on F,G in {−1,+1};
- all 45 Gaussian rational source points of grid denominator 4 with |s|<1, independently in both source coordinates;
- **516,375/516,375** exact nonzero complex polynomial evaluations;
- exact endpoint-sector identity, radius-one and deficit-radius-half boundary zero countermodels;
- deliberately no inference from zero-free source analyticity to spatial decay.

A matching independently executed local source-equivalent script passed 516,375 cases. This committed checker is SOURCE-WRITTEN; no direct byte-identical checkout replay, Agda/Lean kernel, GAP or CI acceptance is claimed.

## Exact remaining YM P0 physical cut

The two-source normalized log is holomorphic on this enlarged fixed bidisk. Local complex Cauchy estimates become available at any strictly interior radius, but **the resulting derivative bounds alone do not decrease with physical separation**. The original two globally marked F/G sites can retain nonzero covariance arbitrarily far apart under a positive correlated law. Hence this cannot pay the CMP116/CMP119 source-selected **bond-local** renormalized KP analytic J, physical absolute connecting W3 shell sum, good/large field rate, original physical beta(a), actual full constrained gauge/FP/Jacobian/R ordered T, or noncollapsed continuum E1/OS same-H mass gap.

Retain original source/Agda trust gates; retain 256 sites, 1024 bonds, 1536 plaquettes, 896 spectators, ordered F19 pair factors, physical time t, Singer chart k, RG scale, source zero-branch residuals and sign/neutral-zero distinctions. None of those is an extra mark or an extra dimension. RH signed quartic/Gamma and NS helical signed-source repairs remain *distinct source consumers*, not consequences of this complex bidisk theorem.

Historical source ownership: Wilson, Haar, Bałaban CMP116/119/122, original DASHI SU(N) Wilson/F19 source proofs and prior 22-Nov affine complex source note. The new contribution is this sharp positive two-source sector bound and its finite exact regression, not their source constructions.
