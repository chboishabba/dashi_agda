# Factorized Navier–Stokes cross-shell Schur bound

## Purpose

The generic NS/YM Schur join reduced the Wall-1 frame-gap problem to the composite correction

\[
K_{10}(I-K_{00})^{-1}K_{01}.
\]

This tranche factors that correction into three separately auditable uniform estimates:

\[
C_{01},\qquad R_0,\qquad C_{10}.
\]

They represent, respectively:

- high-to-low shell injection through `K01`;
- the low-shell resolvent `(I-K00)^-1`;
- low-to-high shell return through `K10`.

The exact composite budget is

\[
\eta = C_{10}(R_0 C_{01}).
\]

## Formal result

`ThreeStageBoundComposition.agda` proves abstractly that four inequalities

```text
stage01(x) <= C01
stageR(x)  <= R0 * stage01(x)
stage10(x) <= C10 * stageR(x)
target(x)  <= stage10(x)
```

imply

```text
target(x) <= C10 * (R0 * C01).
```

`NSFactorizedCrossShellBound.agda` instantiates the target as

```text
<x, K10 (I-K00)^-1 K01 x>
```

and converts the product estimate into the existing `NSCrossShellCorrectionBound`.

`NSFactorizedSchurFrameGap.agda` then combines it with the diagonal high-shell gap and reuses the generic Schur theorem to obtain the conditional frame gap.

## Weighted-kernel certificate layer

`WeightedKernelSchurTest.agda` adds a proof-relevant weighted Schur-test surface indexed by:

- the exact finite kernel;
- its source and target weights;
- row and column constants;
- the corresponding weighted row and column proof objects.

The resulting operator estimate uses the product of the row and column constants. A `KernelIdentityMatch` records literal agreement of the kernel and both weight functions. This prevents a certificate for a coarse projection from being silently transported to the concrete pair-incidence operator.

`NSWeightedShellTransferBridge.agda` consumes separate concrete weighted certificates for `K01` and `K10`, plus the low-shell resolvent estimate, and constructs `NSFactorizedCrossShellEvidence`. The bridge therefore joins finite weighted-kernel analysis to the already-proved factorized Schur chain.

## Exact remaining analytic obligations

The block algebra and constant composition are now discharged. The remaining NS-specific work is to prove uniform versions of:

1. a weighted `K01` certificate for the concrete pair-incidence kernel;
2. low-shell resolvent control with constant `R0`;
3. a weighted `K10` certificate for the concrete pair-incidence kernel;
4. proof that those concrete kernels represent the `K01` and `K10` operators in the shell decomposition;
5. the strict budget inequality

   \[
   C_{10}R_0C_{01} < \delta_{11}.
   \]

The existing coarse shell-angle weighted Schur audit may suggest candidate weights and constants, but it does not supply these proof terms. In particular, empirical gross transfer mass is not identified with the concrete Biot–Savart pair-incidence kernel.

## Promotion boundary

This tranche does not claim:

- a proved Biot–Savart cross-shell estimate;
- a kernel-identity theorem for the coarse audit;
- scale-uniform numerical constants;
- a positive residual gap on the full admissible shell family;
- full Navier–Stokes regularity or Clay promotion.