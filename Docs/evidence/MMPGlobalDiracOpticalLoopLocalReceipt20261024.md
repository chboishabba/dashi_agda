# Local validation receipt — global Dirac optical-loop max-cut, 2026-10-24

**Scope:** independent local Python/SymPy/SciPy calculations, NO GitHub Actions/Agda/Lean receipt and NO 4D semiclassical fermionic solution. Original sources: MMP arXiv:1807.04726 (2018), CQG 40 (2023) 155016; Polyakov/2D Dirac circle Casimir/Hurwitz ζ; Zahn (2014) charged locally covariant Dirac renormalization; Lewis (2020) 2D Dirac Hadamard stress.

## Same source bytes checked

- Script `scripts/check_global_dirac_optical_circle_source_20261024.py`: GitHub connector returned **2880 characters**, FNV-1a 64 `1126339ca755f758`. Locally executed `/mnt/data/check_global_dirac_optical_circle_source_20261024.py`: **2880 ASCII bytes**, independent FNV-1a 64 `1126339ca755f758`, SHA256 `8b9da5ddf777f9036ef1dc23d3770f98c01b8e08e29f38d60c2701ea7e3c5535`. Same-source local PASS, NOT a GitHub-run CI receipt. The PR-head marker for the inspected source is from draft PR #1248 on the branch as of this note. Commit can advance in parallel; recheck SHA before acceptance.
- The optical BVP and open-line no-go scripts committed to GitHub were independently audited and have *locally equivalent* executed scripts; they are not asserted byte-identical to the latter local reference files, so their exact-byte execution is still to be independently confirmed on PR head.

## Executed calculations

`python /mnt/data/check_global_dirac_optical_circle_source_20261024.py` PASS:
- one zeta-renormalized 2D static complex Dirac conformal-circle state energy `E[N,h,α]`;
- independent lapse and spatial-metric energy gradients: at mesh 96,192,384 rho errors `1.534047e-6,3.843970e-7,9.607542e-8`, radial pressure errors `1.789269e-7,4.484615e-8,1.120505e-8`, O(dx²);
- symbolic energy conservation/trace anomaly; large U1 gauge periodicity; equilibrium Wilson-loop current;
- NS phase α=1/2 negative `B2=-1/12`, hypothetical ±2π/3 holonomy shifts give `B2=1/36`.

`python /mnt/data/check_mmp_closed_fieldline_optical_fixedpoint_20261024.py` PASS:
- old dimensionless L=20 effective BVP: q10,11 have nonnegative interior-only optical budgets, q12,13,24 have negative budgets (impossible for same closed-loop interpretation at that L).
- With **prescribed** return optical time 2 (no physical geometry): q12 root `L=22.516301125725`, inside time `20.516301125718`; junction radius `12.79381947`, exterior mass `5.99725136`, local K jump `2.24e-13`, effective ANEC `-3.6310e-4`.
- This is ONE necessary global optical normalization condition of an old *effective* source, not a global 4D fermion state.

`python /mnt/data/check_noncompact_static_dirac_state_nogo_20261024.py` PASS:
- stationary conserved conformal state t'=0 on noncompact line absent compensating stress; flat-vacuum ends select t=0.
- 2D (NOT automatically 4D) null integral `∫(rho+p)/N = c/(12π)∫F²/N` checked on a smooth asymptotically constant-lapse test: both sides `0.00098644110863324`, difference around `1e-18`.

## The still-unpaid physical same-object leaves

1. Topology: both MMP mouths in one ambient universe and exact magnetic return paths; radial two-exterior RN surrogate not same object.
2. A global, Hadamard admissible, covariantly renormalized 4D spin-c charged Dirac state on that geometry, with angular/massive modes, transverse stress and phase/Schwinger/Hall current.
3. Coupled **one-source** Einstein and Maxwell equations, no imposed source shutoff, real external geometry and stability/convergence.
4. Three-plasma actual MHD sources and observable physical effect. A mathematical C3 phase is not a measured Wilson loop.

**All negative claims are scoped to the indicated 2D assumptions** and cannot be applied to exclude MMP's original loop-based construction.
