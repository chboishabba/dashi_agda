# Sprint 149 Linearization Spectrum Probe

This artifact is a deterministic finite-difference toy probe for the ScalingConsistencyForHouLuoConcentration gate. It does not claim a proof.

## Control Card

- **O**: Lane 3 owns only scripts/ns_sprint149_linearization_spectrum_probe.py and outputs/ns_sprint149_linearization_spectrum_probe/ artifacts.
- **R**: Emit deterministic evidence rows for beta candidates in a transparent finite-difference toy linearization around a Hou-Luo-like concentration profile.
- **C**: Single stdlib Python script writes rows JSON, rows CSV, summary JSON, Markdown, and manifest through an atomic staging directory.
- **S**: The state is evidence-only: positive toy spectral drift may be observed, but no self-similar profile analysis or scaling-consistency theorem is proved.
- **L**: Use a fixed Dirichlet grid, explicit second-difference diffusion, multiplicative concentration source, damping terms, and Jacobi eigenvalue scan.
- **P**: Treat the result as a reproducible diagnostic for the missing ScalingConsistencyForHouLuoConcentration gate, not as proof.
- **G**: Validation passes only when all beta rows are present, spectral values are finite, output hashes are recorded, and all proof/promotion flags remain false.
- **F**: Missing: rigorous Hou-Luo self-similar profile analysis, PDE linearization identification, scaling-consistency theorem, and Clay Navier-Stokes solution.

## Method

- Model kind: `deterministic_transparent_finite_difference_toy_linearization`
- Profile: `q_beta(x)=max(0,1+0.45 beta) exp(-(x/w_beta)^2)+0.22/(1+16x^2)`
- Width: `w_beta=0.24/sqrt(1+0.35 max(beta,0))`
- Operator: `L_beta = nu Dxx + beta*0.82*q_beta(x) - 0.18*x^2 - 0.22*|x|^4 with Dirichlet endpoints`
- Spectrum: deterministic Jacobi eigenvalue scan of the symmetric toy matrix.

## Gate Flags

- `linearization_probe_complete`: `true`
- `beta_positive_candidate_seen`: `true`
- `self_similar_profile_analysis_proved`: `false`
- `scaling_consistency_proved`: `false`
- `full_clay_ns_solved`: `false`
- `clay_navier_stokes_promoted`: `false`

## Rows

| beta | dominant | drift from beta=0 | gap | stability indicator |
| ---: | ---: | ---: | ---: | --- |
| -1.0 | -0.357087342647954 | -0.240770874492759 | 0.148264182847829 | toy_stable_nonpositive_drift |
| -0.5 | -0.280055736086458 | -0.163739267931263 | 0.191671801974428 | toy_stable_nonpositive_drift |
| -0.25 | -0.212287447678938 | -0.095970979523744 | 0.235414938046524 | toy_stable_nonpositive_drift |
| 0.0 | -0.116316468155194 | 0.0 | 0.301280852774495 | toy_stable_nonpositive_drift |
| 0.125 | -0.0560767438265419 | 0.0602397243286525 | 0.344325009002258 | toy_stable_with_positive_drift |
| 0.25 | 0.0123789245687855 | 0.12869539272398 | 0.394738537134334 | toy_unstable_positive_dominant_mode |
| 0.5 | 0.176438757277 | 0.292755225432194 | 0.519726993374983 | toy_unstable_positive_dominant_mode |
| 0.75 | 0.37956469947347 | 0.495881167628664 | 0.678854542311789 | toy_unstable_positive_dominant_mode |
| 1.0 | 0.623529398614631 | 0.739845866769825 | 0.872435919586377 | toy_unstable_positive_dominant_mode |
| 1.25 | 0.908858407375517 | 1.02517487553071 | 1.09910009996656 | toy_unstable_positive_dominant_mode |
| 1.5 | 1.23553386347103 | 1.35185033162622 | 1.35643356355015 | toy_unstable_positive_dominant_mode |

## Interpretation

Positive beta rows with positive dominant toy eigenvalue are recorded as candidate evidence only. They do not prove scaling consistency, PDE stability, self-similar profile validity, or any Clay Navier-Stokes claim.
