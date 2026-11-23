# Conservative Moving-Boundary Geometry and Adjoint Curvature Attribution in Five-Dimensional Braneworld Dynamics

Paper 2 — working research draft, 2026-11-20. Not a live-core manuscript or continuum claim.

## Finite moving-interface receiver attribution

For an affine discrete step x[n+1]=G[n]x[n]+s[n], evolve the independently masked state with its own initial state and stage source insertions. Its difference from the masked full state satisfies e[n+1]=G[n]e[n]+sum_j K[n,j], with three marked-stage and two SSPRK carry contributions. The multi-time receiver adjoint p[n]=G[n]^T p[n+1]+o[n] contracts the five terms at each step. The complementary masks cancel termwise, while the receiver affine offset is allocated exactly once. Stage clock incidences (2n,2n+2,2n+1) pull back shared controls and sum their sensitivities; equal clock indices are not equal computational states. Existing time-indexed hyperfabric is the structural owner, not a new physical ontology. Original Israel source and F8 numerical operators are reused in reconstructed local Python/Numba form; precise original literature attribution and production attachment remain manuscript work.

## Numerical diagnostic and refinement boundary

Prior short-window local runs detected all seven mutations for both normal orders; nondegenerate complementary regions and a nonzero exterior propagated response were obtained at longer windows. At rx=.073 and eps=.04 the receiver stencil is directly source-free. First nonzero sampled functional at N=3 is discrete reach, not physical causal arrival. The independent refinement screen fixes zero initial state, centre observation clock .06 and source history .02 sin^4(pi T/.04) on [0,.04], zero thereafter. Baseline dr=.008, dy=.012, dt=.0005, extents .096/.072. Twelve configurations (six per order) execute with finite receiver values and independent strong trace reconstruction. Maximum receiver changes under timestep halving .02404/.02212, domain doubling .03432/.03209, normal halving 18.66462/17.52579, radial halving 106.69593/103.74307, joint half spacing on doubled domain 120.81967/119.95055. Max geometric identity defect 1.63425e-13 does not imply curvature convergence. Normal-only refinement reduces strong/characteristic discrepancy but radial-only and joint refinement increase it. No continuum inference is licensed.

## Open numerical and formal obligations

Three-level independent source/field/jet refinement; receiver stencil alignment, stability and separate radial/normal extension; original guarded production receiver; longer-window applicable mutations; strong trace convergence; literal Agda hyperfabric and CMYKalpha/full pose. The canonical implementation roadmap is `../../physics/KSW668F8YMNSNonlinearCurvatureRoadmap20261120.md`. Paper 8 imports only scoped finite architecture. No Clay or unification promotion.


## LXXIX — independently audited native source/moment interface

The source programme in PR #1527 has constructed exact rational four-row moment witnesses and a signed dual-bound interface, but their loads are not yet proven identical to the native `exact_cell_averages` physical source used for the receiver programme on PR #1530. The local four-mesh control preserves original integrated l0/l2=0 and l4~2.57617 while naive cell-centre u²-weighting produces nonzero, nonmonotone fourth-row defects. These do not refute the continuum identity; they prohibit silently substituting cell averages for source-specific exact weak loads. The remaining paper obligation is a same-load coefficient-level interface (including within-cell weighted moments), then a genuine native receiver VJP and certified numerical error ledger. This manuscript remains a working satellite, not a continuum GR result.
