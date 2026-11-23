# YM W0 — geometry repair: retain shared intermediate states in CMP119 T-step path expansion (23 November 2026)

## Correction to the previous audit

The previous exact toy example was **not a counterexample** to the genuine CMP119 (2.18)--(2.22) scalar factorization. It was a counterexample only to a **different, unjustified construction**: multiply independently summed T-step masses after summing out a shared intermediate state twice. It had not proved such an error occurs in the repository.

In fact the existing CMP119 factorized functional carrier ALREADY contains the right structural slots:
- `admissibleSequences` in (2.18), able to label a path of intermediate field configurations / conditioned domains;
- `componentsAt` in (2.19), intended for genuinely disjoint components;
- `orderedStepsAt` and `oneStepValue` in (2.20)/(2.22), holding scalar values **after** fixing the common sequence/path;
- `sequenceResidual`, preserving boundary/indicator/action/localization factors not present inside individual T steps.

The missing **physical source extraction** is to show that original CMP119 sequences actually index the necessary constrained integration histories, and that the original Wilson/Haar integrand and its globally unique 1/F/G/FG marks correspond to the sourced step factors and residuals. It is not a reason to replace the existing compiler or to reject any scalar product written there.

## Independently executed exact finite repair

Reuse the positive two-state example from the prior note: A=[[2,1],[1,3]], B=[[3,2],[1,2]], F=diag(0,2), G=diag(2,0), left=(1,0), right=(1,1)^T. Let p=(a,b,c) denote the **complete path**, with the left endpoint a=0. Set

    residual(p) = left[a] right[c]
    t1(p;s) = A[a,b] (1+s F[b,b])
    t2(p;t) = B[b,c] (1+t G[c,c]).

The real operator contraction is EXACTLY the CMP119-shaped path sum

    K(s,t) = sum_{p=(a,b,c)} residual(p) * t1(p;s) * t2(p;t)
           = 13 + 6s + 14t + 4st.

There are only four contributing paths (b,c) in {0,1}². Each term is a product of two ordered scalar step values **after** its shared intermediate state b is fixed. Summing first over the two intermediate-state fibres gives

    b=0: 10 + 12t
    b=1: 3 + 6s + 2t + 4st

and both restore the correct four global coefficients (13,6,14,4) under the final sum. This construction also keeps the residual, so it does NOT need to fit endpoints into a fictitious T operation.

The previous independently contracted scalar shortcut gives 15+10s+18t+12st because it duplicates / prematurely eliminates the common boundary state. It is not the CMP119 source formula unless the source supplies a **separate** disjointness/Fubini argument that permits such a product.

A distinct finite Cartesian-product test verifies genuine factorization when the fine components are independent coordinate factors and the integrand separates; shared-state positive matrices fail that condition. Source-level disjointness must mean disjoint field/fibre domains plus correct conditioned boundary geometry, not simply disjoint labels or a commuting scalar multiplication.

Executed local SymPy 1.14 exact arithmetic in [check_ym_w0_T_path_geometry_20261123.py](../../scripts/check_ym_w0_T_path_geometry_20261123.py). All path, coefficient, conditional-fibre and disjoint-Fubini assertions passed. The committed file has a GitHub readback but exact byte-for-byte checkout execution remains pending; no Agda kernel or CI.

## Existing source owners and narrow obligation

- `BalabanCMP119Equation218FactorizedFunctionalDensityExact` already owns the sequence/component/step/residual algebra and source extraction flags conditional.
- `BalabanCMP119Equation171WeightedStepApproximationExact` already provides the **per-(sequence,component,step)** Eq. (1.71) source T mass via `sourceTAt` and `sourceStepIsEquation171Mass`, and a telescoping marked approximation budget. Crucially, `sourceStepIsEquation171Mass` is a supplied physical equality field, not an unconditional original Wilson realization.
- `BalabanCMP119FactorizedDensityApproximationExact` already propagates per-step majorants through the component and sequence products; no new scalar telescoping proof necessary.
- `BalabanClayP3FiniteConstrainedIntegralExact` has literal `blockMap`/`coarseMatches` and exact finite small/large integral partition. Its compact SU(N) Haar limit is explicitly conditional.
- `BalabanClayGate4ComponentClassAndFiniteTOperationExact` already supplies a constrained finite integral for a functional; `BalabanCMP122Equation171TOperationSemanticsExact` already owns source localized T integral meaning. The rational finite Gate4 sum cannot be silently identified with continuous SU(N) Haar.

**Next physical W0 attachment:** identify actual original source geometry of admissible domain paths (including their boundary states and any conditioning), original disjoint component fibres, actual localized ordered T maps and boundary residuals with the ORIGINAL SU(N) fine F19 four-moment measure. The source's original Eq. (1.71) operator must retain the full fine-holonomy and 896 interacting spectator dependence and the unique globally affine two marks. Then inhabit the existing `sourceStepIsEquation171Mass` and complete-density realization using a real physical SU(N) Haar/source argument; only then propagate source-supported marked W3 and a physical uniform rate.

**No promotion:** the finite matrix witness demonstrates that the presumed algebraic mismatch can be repaired through the existing path/sequence geometry. It does not prove CMP119 source indices have been identified, establish continuous Haar finite-step equality, Section-2 analytic bounds, W3 rooted-shell decay, or the interacting continuum Yang-Mills theorem. Attribution original Wilson/Haar, Bałaban CMP119/CMP122/P3 and current DASHI source owners.
