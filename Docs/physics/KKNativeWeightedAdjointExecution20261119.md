# Native weighted adjoint acceptance — 19 November 2026

Parent PR #1530 head 790efd01eccf8a20577f8a6e2a24445a14c867d4. Original stage owner on this branch has blob 323954f2094da93a0d53acc4e831510f69faed52; source flux owner dec4e79e3a4899952a5deceb786324bc0745982c. Direct GitHub clone failed DNS; local execution used manually recovered Numba stage function, SymPy source primitive implementation, cached sparse transpose and matching integrated SSPRK3/readout formulas. This is not a byte-verified full checkout or independently executed exact committed script. Local SymPy 1.14.0, SciPy 1.17.0, Numba 0.65.1.

## Stage parity

Order 3: lhs 257168.18129760798, rhs 257168.18129760862, abs residual 6.402842700481415e-10.
Order 4: lhs 6202280.716773634, rhs 6202280.716773637, abs residual 2.7939677238464355e-09.

## Resolved source fixture

dr=.012, dy=.03, requested dt=.003, eps=.04, final_t=12, pulse=.065, r_outer=3.01, y_outer=2.01, order=4.
Grid 252 x 68, 904 steps, discrete photon margin 0.006459111173937387. Conservative source moments and radial CFL checks passed. All four kernels and all five forward controls agree within rtol=2e-6, atol=1e-13 (20 scalar comparisons). Shared Israel temporal upper-bound cost 0.9466383880922333; all optimized costs equal within floating rounding.

| channel | baseline | optimized target | compliance | amplitude ratio |
|---|---:|---:|---:|---:|
| E4 | -7.02418159e-05 | 7.82324435e-05 | 6.4653148301430204e-09 | 1.1137588404002705 |
| E5 | -2.88434453e-06 | 3.34679729e-06 | 1.1832450737049961e-11 | 1.1603320110443114 |
| E4 tangent | -7.02017973e-05 | 7.81773492e-05 | 6.456211793430429e-09 | 1.1136089422516886 |
| E5 tangent | -2.80143483e-06 | 3.22905103e-06 | 1.101452329476269e-11 | 1.1526418520475248 |

Cross-channel forward/prediction pairs (rounded, channel order E4 E5 E4 tangent E5 tangent):
- E4 control: [7.82324435e-05,3.31875590e-06,7.81773424e-05,3.20722820e-06]
- E5 control: [7.75769672e-05,3.34679729e-06,7.75182625e-05,3.22873452e-06]
- E4 tangent control: [7.82324367e-05,3.31858158e-06,7.81773492e-05,3.20707860e-06]
- E5 tangent control: [7.77037266e-05,3.34646923e-06,7.76453828e-05,3.22905103e-06]

The optimized controls are separate, not one common optimum. Baseline sign is negative; positive optimum maximizes the linear observable. Squared-response comparison is sign-independent. Temporal budget is an Israel bound factor with a fixed spatial profile, not measured energy or SI work. Discrete support guard is not continuum causality evidence. Original default resolution, larger domain, donor byte/import parity, independent readout accuracy, source-work and detector calibration, same-action Einstein matter closure remain open. No physical antigravity or graviton measurement claim.
