# Selected Wilson/CMP119 physical source execution — 30 Sep 2026

This is a **source-oriented calculation interface**, not a claim of constructed quantum gravity, continuum Einstein solutions, a mass gap, or laboratory antigravity.

## Primary attribution, with actual scope

- Kenneth G. Wilson, *Confinement of Quarks*, Phys. Rev. D 10 (1974), 2445–2459. DOI **10.1103/PhysRevD.10.2445**. Relevant source for the Wilson plaquette action.
- Tadeusz Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories. I. Generation of Effective Actions in a Small Field Approximation and a Coupling Constant Renormalization in Four Dimensions*, Commun. Math. Phys. 109 (1987), 249–301. DOI **10.1007/BF01215223**. Relevant source for the orientation of inverse-coupling recurrence and perturbative four-dimensional scaling.
- Tadeusz Bałaban, *Convergent Renormalization Expansions for Lattice Gauge Theories*, Commun. Math. Phys. 119 (1988), 243–285. DOI **10.1007/BF01217741**, Sect. 2, especially Eq. (2.23). Relevant source for the effective density sectors. Its abstract identifies completed convergent expansions **for superrenormalizable models**; it is **not** in itself a proof of the full four-dimensional YM continuum theory or its gravitational quantum stress.

These are original published claims. The new coefficient/readout/obstruction code is DASHI work using separate finite carriers. DOI citation, a source comment, or an Agda field is not an externally verified proof of a selected physical identification. The exact primary-text Eq. (2.23) plaquette normalization and trace convention still require a direct page-level source extraction.

## Code in this tranche

1. `DASHI/Physics/Foundations/CMP119LiteralWilsonProjectorSignAuditExact.agda`. Uses the **existing** two-coordinate T4 localized plaquette **coefficient** basis and its projector; this is not a literal SU(2) matrix plaquette evaluator. The +inverse-coupling *Wilson action* has a +inverse-coupling projected coefficient; the -inverse-coupling *exponent convention* has the negative coefficient. All E/R/B/vacuum sector projections are retained rather than set to zero. The current `Canonical.canonicalNodeAction` built from the native CMP109 trajectory extracts **+u_k** plus the four symbolic source-sector projectors; this is now a theorem on the actual canonical source representation. This theorem **does not** choose the sign of the published effective action by construction, and it does not identify the selected primary-source exponent with the repository's positive-action coefficient.
2. `scripts/grqft_selected_finite_stress_exact_audit.py`. Reads a selected finite configuration/measure/insertion receipt and evaluates, exactly over `Fraction`, `Z=∫rho`, `A=∫rho O`, `B_h=∫((-rho DS_h) O+rho DO_h)`, `D_h=∫(-rho DS_h)`, `C_h=B_h Z-A D_h`, and `C_h/Z²` on **all ten symmetric metric directions**. Recomputes the four-direction `C_trace=Z ∫rho sum DO_aa` identity under the existing classical d=4 trace-zero action assumption. Separates time-time, three spatial components, Lorentzian trace *candidate*, and active *candidate*.
3. Optional `geometry_diagnostic` compares the ten **normalized** candidate components with a specified ten-slot Einstein tensor on the identical source identity, cutoff and metric frame, using an independently fixed scale. A zero numerical residual is **not** physical stress identity.
4. Optional `weak_coupling_reference` computes the independent weak-YM-only active baseline `A_YM=(4*kappa+margin)E²+margin B²>=0` and the additional effective active contribution that **would have to exist if** the selected numerator had the corresponding Lorentzian physical meaning. It does **not** construct such a contribution.
5. `scripts/test_grqft_selected_finite_stress_exact_audit.py` exercises positive, negative, trace-silent, missing-slot, source/frame mismatch and weak-YM baseline cases (all test inputs explicitly marked as toy-only). `.github/workflows/cmp119-literal-source-audit.yml` requests an Agda kernel and Python regression check when Actions runs.

## Reproducing a selected physical receipt

```sh
python3 scripts/grqft_selected_finite_stress_exact_audit.py \
  /path/to/source-selected-immutable-finite-measure.json \
  --out /path/to/exact-rational-audit.json
python3 -m unittest discover -s scripts -p 'test_grqft_selected_finite_stress_exact_audit.py' -v
```

The required JSON fields are:

- `provenance`: `source_identifier`, `revision`, `selected_action`, `measure_identifier`, `cutoff`, `metric_frame`, `observable_identifier`, `normalization`; declared `haar_metric_independent: true`, `gibbs_logarithmic_derivative: "d_rho=-rho*dS"`. These declarations MUST ultimately be independently established from the source action, they are not proofs.
- `slots`: exactly `["00","01","02","03","11","12","13","22","23","33"]`.
- `configurations`: a nonempty list of explicit objects containing unique `id`, exact rational `haar_weight`, `density`, `insertion`, and two ten-slot dictionaries `d_action` and `d_insertion`. The `d_action` diagonal sum must vanish in each configuration.
- Optional geometry: `geometry_diagnostic` with the same source id/frame/cutoff; `geometry_revision`, independent `normalization_origin`, `source_to_geometry_normalization`, exactly ten `einstein_tensor` components and `factor_fitted_to_this_geometry: false`.
- Optional weak-YM: `weak_coupling_reference` with the same id/frame/cutoff; `reference_revision`, `normalization_origin`, `factor_fitted_to_this_source: false`, nonnegative `kappa,margin,electric_square,magnetic_square`, and a fixed positive `connected_to_physical_active_factor`.

The returned `input_sha256` is the hash of raw JSON bytes, making subsequent result comparisons byte-attributable. Raw external reports MUST still identify the selected physical source of their rows, not simply reuse the GitHub source name.

## Fail-closed frontier

*Literal source action*: Wilson plaquette basis signs are internally derived; the paper's own selected (c_k), `g_k`, matrix trace and density-exponent convention still need equation-level equality to the actual constructed source action.

*Selected finite measure*: the script is an independent exact `N/Z/DN/DZ` producer **only once given a complete finite table from the selected action**. It neither derives the metric `DO_h` from the published CMP119 observable, enumerates the SU(2) nonlinear configuration integral automatically, nor proves the quadrature enclosures, gauge Ward identities, shell coverage or (b_{lower}>0).

*Timelike and Lorentzian physics*: a Euclidean connected numerator is NOT yet the Lorentzian timelike energy density. Continued stress and metric counterterms, the same physical (T_{00}), renormalized trace, and the physical (A=Theta+2rho) identification are missing. In the ordinary weak-coupling YM family, the preexisting nonnegative active stress result prohibits a negative same-source active stress. A supplemental negative contribution needs an independently constructed source and must dominate that nonnegative baseline.

*Continuum and cosmology*: selection of curved-spacetime state (including relevant Hadamard/renormalization criteria), stress conservation, gravitational coupling, finite-to-continuum curvature and source convergence, backreaction, sourced FLRW, and independently frozen observational predictions remain unsolved. This numerical tool and these finite Agda theorems do not close quantum gravity or the Clay gap.

## Verification and status

The new test files are committed, but at this cut no exact-head GitHub Actions runs were found. A GitHub source commit or a CI workflow definition alone does **not** imply Agda elaboration or Python test success. Treat the code as source-written until a passing workflow or reproducible local run supplies a receipt.
