# Zipf–Mandelbrot / Hurwitz rank × ORIGINAL R734 pressure/phase no-go

**Date:** 2026-10-27. **Source:** active NS PR #1271, original same-selected-cutoff physical R734/R735 six-mode Galerkin source. **Status:** exact finite statistical checks and re-use of the existing physically signed obstruction, not global regularity or a new independent six-mode construction.

## 1. Exact finite normalization

For finite rank support `1,...,N`, `N>=1`, `q>=0`, `s>=0`:
`H_N(q,s)=sum_{k=1}^N (k+q)^(-s)`;
`p(k)=(k+q)^(-s)/H_N(q,s)`.
Finite normalization is well-defined even for `s=0` or `s=1`. For **s>1** the absolutely convergent Hurwitz defining series gives
`H_N(q,s)=zeta(s,q+1)-zeta(s,q+N+1)`.
At `s=1` the two infinite defining series diverge; an analytic-continuation limit would need its own justification. Nothing about RH zeros, Eisenstein series, fractal symmetry or PDE coercivity follows from this normalization. The new exact Fraction/SymPy test exercises an integer-parameter finite subset and the `s=2` identity, *not* an empirical corpus fit.

**Pareto check:** among five ranks, the top-one mass is `1/5` at exponent 0, `60/137` at exponent 1, and exceeds `4/5` at exponent 4. There is no universal 80/20 rule, let alone a 1%→99% factor-reduction theorem. Zipf rank/frequency, Heaps vocabulary growth, Bradford reference concentration, Lotka authorship, Benford digits, King outliers and the 1% participation hypothesis have distinct random variables and evidence requirements. The original Clauset–Shalizi–Newman model-comparison protocol guards against mistaking log-log slopes for proof.

## 2. Same physical R734 source: rank/phase/pressure information loss

**Reuse** `tests/test_ns_r734_pure_plus_physical_w2_no_go.py` and `tests/test_ns_r734_phase_curvature.py`, not a fabricated fluid surrogate. At sharp Galerkin N=2, with real conjugate modes and positive curl helicity, take `p=(1,0,0),q=(0,1,2),k=(1,1,2)`. Flip the `k,-k` pair's **phase sign** while keeping all six squared modal magnitudes exactly fixed. Every phase-blind rank, top-K, Zipf–Mandelbrot fit or concentration score is thus identical; the original dyadic nonlinear source transfer becomes

`Pcrit(u)=(5+sqrt(5)-sqrt(30))/10>0`,
`Pcrit(v)=-Pcrit(u)`.

This is a *non-injectivity / insufficient-statistic theorem* for magnitude-ranking summaries, not a claim that Zipf physics causes vortices. The earlier R734 phase-curvature source already contained the physical pair; the new regression formally couples it to the exact finite rank test and does not claim priority for the inherited witness.

For the complete sign flip `u -> -u`, the actual quadratic Leray force satisfies `F(-u)=F(u)` while velocity-weighted critical work is cubic and flips sign. For the full incompressible equation, zero-mean pressure is determined by
`-Delta p = partial_i partial_j (u_i u_j)`.
Its source and recovered pressure are even under `u -> -u`, but **that does not determine** the sign of nonlinear spectral work. Pressure recovery is a real nonlocal elliptic operator, not evidence from a vortex-like picture, nor a statistical compensation term. The new test verifies the same-cutoff quadratic Leray-force parity; pressure parity follows algebraically from Poisson, without pretending to reconstruct pressure in the test.

For `u -> a u` normalized ranks are unchanged, nonlinear production is cubic `a^3`, and the original R734 viscous dissipation is quadratic `a^2`. At `a=512, nu=1`, the original source gives `a*Pcrit>2*Dcrit`, `Dcrit=36`; the *unrestricted universal* positive-margin R734 W2 source leaf is false. The R734/R735 **conditional compilers** remain valid under their hypotheses. This finite Galerkin counterexample is **not a finite-time Navier–Stokes singularity**.

## 3. External sources, genealogy and authorities

- Jean-Baptiste Estoup and George K. Zipf: earlier rank-frequency observations and dissemination; Benoît Mandelbrot: shifted rank model; Adolf Hurwitz: Hurwitz zeta. Distinguish statistical names from formal proofs and direct primary originals from encyclopedia descriptions.
- Fabian Waleffe, *The nature of triad interactions in homogeneous turbulence*, *Physics of Fluids A* 4 (1992) 350–363, DOI `10.1063/1.858309`; original helical signed triad physics. Existing DASHI R92/R102/R691/R734/R735 are the source owners.
- Aaron Clauset, Cosma Rohilla Shalizi and M. E. J. Newman, *Power-law distributions in empirical data*, *SIAM Review* 51 (2009), DOI `10.1137/070710111`; proper statistical fitting, goodness-of-fit and alternatives.
- OpenAI's **8 Sep 2026** publication `https://openai.com/index/navier-stokes-solution/` reports an analytic and Lean-formalized **smoothly forced** Clay-C/D finite-time singularity. Clay's **11 Sep 2026** statement `https://www.claymath.org/news/navier-stokes-announcement/` calls it *apparently* settled pending its formal process. Neither supplies an unforced periodic R734/R735 proof or an independently audited bridge into this code.
- Ibrahim et al.'s 2026 geometric-depletion/regularity proposal is independently attributed, not a proven same-source lemma imported here. Shared terminology is no substitute for checking the original hypotheses.

## 4. Max-cut / Pareto / snowball follow-through

| Phase | Deliverable and actual status | Next hard gate |
| --- | --- | --- |
| P0 R734 | Original real six-mode signed counterexample and phase curvature already in PR #1271 | Retire false universal W2; retain signed helical + same-helicity dyadic weight defect |
| P1 rank | New `tests/test_ns_r734_zipf_hurwitz_rank_gate.py` with five exact tests | **5 passed** in a matching local fixture; exact full PR head and Agda/Lean kernel unverified |
| P2 actual statistics | Source-qualified Zipf–Mandelbrot and null/model-comparison diagnostics | Need empirical source counts, held-out validation, outlier/tail preservation |
| P3 PDE | Same-source phase-aware four-channel signed estimate and middle-time gap | Must defeat rank-collision/amplitude control, and then continuum pressure/tail/localization defects |
| P4 fleet/ITIR/SB | Source→span→statement→PNF→canonical ZERO quotient→nonzero reviewable residual→world | Cross-repo live reduction **not executed**; 319,211 raw factors are not 319,211 admitted gaps |
| P5 forced-NS reconciliation | External source pin and Clay formulation C/D vs our unforced problem | Lean version/proof audit and independently reviewed theorem map still open |

Rank is an **optional operational priority feature** after typed semantic quotienting and source-genealogy deduplication; neither high-frequency utterances nor high-amplitude modes automatically confer semantic relevance, source independence, causal force, theorem authority or proof. Preserve outlier/rare-tail gaps and the zero-vs-nonzero residual separation. The 99% target is not a demonstrated result.

**Proof/status receipt:** new five tests locally passed against a matching standalone copy of the original source helpers; this is not an exact PR-head suite. No empirical fleet audit, new kernel certificate, universal R734 W2 payment or continuum regularity theorem is claimed.
