# V2 generator × reluctance/permeance × Tesla-compatible 369 maximum cut

**Synthetic mathematics and testbench only. Not calibrated or reproduced from any real generator.**

Original V2 source root: user-supplied @madscience369 Instagram 90 s reel transcript and screenshots from 14 November 2026, separately hashed in `Artifacts/v2_original_source_manifest.json`. Actual number of coils, pulse schedule, converter routing, material curves, shaft torque and loss inventory remain unknown. Tesla's rotating-field/polyphase work, historical MG10 and David Holmstrom's independent Resonate369 motors are cross-pollination donors, *not the same V2 apparatus* and not co-inventors of DASHI mathematics.

The package contains:

- `Docs/physics/ReluctancePermeanceTesla369PulsedGeneratorMaxCut20261115.md` — comprehensive new phased roadmap, model limits, rival mechanisms and exact remaining producers.
- `Docs/physics/MadScience369V2PulsedGeneratorMaxCut20261114.md` — previous V2-only finite source audit.
- `DASHI/Physics/Motors/MadScience369V2FinitePowerDiscriminatorsExact.agda` — previous finite Agda evidence and accounting examples.
- `DASHI/Physics/Motors/ReluctancePermeancePulseBoundaryExact.agda` — new conditional reluctance/permeance interface and real Nat no-surplus conditional proof; **source-written, Agda kernel acceptance not performed**.
- `scripts/check_reluctance_permeance_phase_maxcut.py` — signed pulse power ODE/coenergy, 3/6/9 vs others, dense 8x voltage check, SLSQP optimisation and SymPy exact identities.
- `tests/test_reluctance_permeance_phase_maxcut.py` — 18 additional tests (22 total with previous 4).
- `Artifacts/v2_reluctance_phase_maxcut_receipt.json` — all synthetic parameters, winners, test model readings, and numerical residuals.
- Prior finite scripts/tests/receipt from the previous audit.

Reproduce in a Python environment with `numpy`, `scipy`, `sympy`, `pytest`:

```bash
python scripts/check_v2_maxcut.py
python scripts/check_reluctance_permeance_phase_maxcut.py
python -m pytest -q tests/test_v2_maxcut.py tests/test_reluctance_permeance_phase_maxcut.py
```

**Verification on 15 November 2026:** original 22 checks plus five phase-symmetry checks = 27 Python tests passed; SymPy linear, mutual-coupling, nonlinear-coenergy and 3-phase phasor identities passed. The `agda` executable was unavailable; the Agda source was **not** kernel-verified. Eightfold numerical resampling is not a continuous-interval certificate. For GitHub integration, verify the live PR and commit separately; local code does not itself certify remote acceptance.

## New symmetry correction and honest 369 frontier

- `Docs/physics/ReluctancePhaseSymmetryAdversarialMaxCut20261115.md` — exact independent-phase normalization identity, zero intrinsic mean-export advantage in the selected matched-current model, cost thresholds for 3/6/9 vs nonmultiples, and original apparatus proof leaves.
- `scripts/check_reluctance_phase_symmetry_maxcut.py` / `tests/test_reluctance_phase_symmetry_maxcut.py` — symbolic general nonlinear coenergy, phase-cancel proof, 3 pulse-shape tests (3–12 phases), regulator-efficiency sensitivity and regression checks.
- `Artifacts/v2_phase_symmetry_maxcut_20261115.json` — exact symbolic results, phase thresholds, negative controls.

**Important correction:** the earlier synthetic output differences between m=3 and m=9 originate primarily from a per-phase switching-loss assumption. Mean electromagnetic extraction and copper loss were equal by construction, while phase ripple and peak voltage differed. 3, 6 and 9 may win different explicit weighted objectives; 4, 5, 7 etc also win on other weights. C6 and C9 are distinct refinements with common C18, not a 3→6→9 divisibility chain.