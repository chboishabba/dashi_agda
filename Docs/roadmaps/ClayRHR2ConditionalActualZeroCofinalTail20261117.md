# R2 actual-zero cofinal tail: exact conditional shell bound (2026-11-17)

**New mathematical deliverable:** an explicit closed-form bound for a fixed-t **absolute far-zero tail** under the source-compatible fourth-order kernel decay and standard zero-count shell hypotheses. This does not close the signed R2 gap.

Let t>=0, n>=1, A,C>0. Suppose for every integer k>=n:

1. The multiplicity-weighted count of **actual zeta zeros** with k<=|Im(rho)-t|<k+1 is <= A(1+t+k)log(e+t+k).
2. Each literal signed off-ordinate summand has absolute value <= C/(1+k)^4 on that shell. This is a bound to be derived for the *literal selected witness* by four integrations by parts in its compact smooth Fourier kernel, with alpha uniformly bounded by the critical strip and t fixed. It must not be silently assumed for a different test.

Then, using log(e+t+k)<=4(1+t+k) for t,k>=0 and monotonicity of f(x)=(1+t+x)^2/(1+x)^4,

sum_{|Im(rho)-t|>=n} |literalOffOrdSource(rho)|
 <= 4AC [ (1+t+n)^2/(1+n)^4 + 1/(n+1) + t/(n+1)^2 + t²/(3(n+1)^3) ].

The bracket tends to zero as n tends to infinity at each **fixed t**. The exact integral identity is
integral_n^infty (1+t+x)^2/(1+x)^4 dx = 1/(n+1)+t/(n+1)^2+t²/(3(n+1)^3).

SymPy verified the integral, negative derivative and limit in the checked script `scripts/check_rh_r2_conditional_zero_tail_20261117.py`. This is a **conditional fixed-height tail bound**, not a numerical certificate of A,C and not a uniform-in-t estimate. Actual zeros are used only via their count, with no RH assumption.

**Remaining analytic obligations:**
- Extract the selected W and instantiate an explicit source-derived C(t,W) for the complete normalized pair kernel, including base/horizontal terms and multiplicity normalization; verify 4th-derivative smoothness for the selected window and its Fourier transform. The fourth-decay bound is not yet verified for the selected W in this note.
- Instantiate an explicit valid A in the shell count, or retain a proved zero-count theorem with a bound and constants.
- Evaluate selected-W finite cone/good/far signed sums and target T_W(rho) using certified numerical intervals, not only zeta-zero approximations.
- Show the **limiting signed margin is strictly positive** (or rigorously negative) with uniform cofinal control. Absolute tail convergence alone cannot supply its sign.
- No RH, R2, or Clay closure claimed. Portfolio: 15/28 OPEN.

Original Lean sources: `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`, `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleConeDecomposition.lean`, `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleAbel.lean` in `chboishabba/dashi_lean4`, branch `agent/rh-postmerge-maxcut-20261007`.
