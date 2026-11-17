# V2 steelman: factorial load × recovery × shaft-reaction maximum cut

**17 November 2026.** Owner: DASHI electromechanical steelman, not source-selected @madscience369 apparatus. This cut avoids adding a new cable/Maxwell research dependency. It reuses the previously established signed magnetic, recovery, and converter models, but asks a genuinely different causal question: **when the electrical load is applied, what happens simultaneously to motor input, rotor shaft transfer, conversion losses, other outputs and storage?**

## 1. Two-ledger shaft weld, with no double counting

Let `M` be motor electrical input; `A` be independent auxiliary electrical input; `S` shaft power transferred from motor to generator; `L` generator electrical load; `O` other mechanical/electrical outputs; `D_m,D_g` the nonnegative motor and generator losses; `E_m,E_g,E_r` motor, generator, and rotor stored energy. The exact port equations, averaged over a common observation window, are

\[
M=S+D_m+\dot E_m, \qquad
S+A=L+O+D_g+\dot E_g+\dot E_r.\]

Summation eliminates the **internal** shaft transfer:

\[
\boxed{M+A=L+O+D_m+D_g+\dot E_m+\dot E_g+\dot E_r}.\]

These identities are checked with Python `Fraction` arithmetic for every synthetic operating state. They prohibit the common false surplus obtained by counting `M` and `S` as *independent* energy inputs. Dissipation must be nonnegative. Negative energy derivative is permitted only when stored energy actually declines; stationary acceptance forbids all such inventory changes unless a rigorously matched cycle is separately certified.

## 2. Exact constant-meter counterexample (not the V2)

A fixed 286 W input does not fix shaft work: in an energy-consistent constructed state, unloaded `S=200 W, D_m=86 W`, while loaded `S=245 W, D_m=41 W`. Keeping `O=120 W, D_g=80 W`, the 45 W additional output is fully mechanical and comes with 45 W higher transferred shaft power. Both motor and generator energy balances hold exactly and all inventory endpoints are stationary.

The required motor efficiency would increase from `200/286 ≈ 69.9%` to `245/286 ≈ 85.7%`, a *large hypothetical change*. Nothing in the demonstration establishes such a change; the model demonstrates **non-identifiability**, not a likely explanation.

Five distinct synthetic 45 W counterworlds give identical motor-input/output displays: (i) generator heat falls 45 W, (ii) shaft transfer rises 45 W and motor heat falls 45 W, (iii) auxiliary input adds 45 W, (iv) rotor/storage supplies 45 W transiently, (v) another output drops 45 W. They have different physical signatures and require independent measurements to discriminate.

## 3. Four-arm load × recovery intervention

Factorial arms `(load,recovery)∈{0,1}²` are constructed with equal nominal 286 W input and exact closed storage. The recovery controller has a separately charged 0.4 W auxiliary input. When loaded, the example recovers 7 W additional useful output from generator loss; it does not eliminate shaft reaction. Define `I[Y]=Y₁₁−Y₁₀−Y₀₁+Y₀₀`.

The *exact* integrated energy identity is

\[
I[L]=I[M]+I[A]-I[O]-I[D_m]-I[D_g]-I[\dot E_m+\dot E_g+\dot E_r].
\]

In the constructed factorial example `I[L]=+7 W`, `I[D_g]=−7 W`, and all other interaction terms vanish; the residual is exactly zero. Thus **recovery has a genuine interaction benefit only if an independent dissipation or power pathway compensates it**. A change in bus output is not automatically a claim about reduced shaft torque. For a fixed output target, a separate test can determine whether recovery reduces `S` or merely reduces losses; these are distinguishable by torque measurements.

A conservative worst-case error guarantee for the four-arm interaction is the sum of their absolute measurement-error bounds. If each arm's measured useful-output mean is bounded within ±1 W, the constructed 7 W interaction lies within `[3,11] W`; if each bound is ±2 W the interval includes zero. **These are deterministic bounds, not confidence intervals**, and do not protect against drift, sensor correlation, inconsistent windows or uncontrolled changes.

## 4. Measurement identification and randomized intervention design

For an original apparatus, measure *synchronously* and with consistent signs: (a) true motor electrical watts and all auxiliary ports; (b) generator bus/load and other mechanical/electrical outputs; (c) shaft torque with RPM in both states; (d) capacitor/rotor/magnetic state endpoints (including changes in temperatures/internal fields where measurable); (e) independently quantified losses, ideally calorimetric, to validate inferred dissipation.

If the unobserved changes are ordered `(auxiliary, dissipation, storage, other output, shaft transfer)`, complete electrical meter balance supplies rank **1** of **5**, leaving nullity **4**. Adding independently measured auxiliary, storage, other output and shaft signals yields rank **5**, so the residual loss change can be inferred. A duplicate input or output meter adds no rank. This is an *algebraic observability criterion*, not a claim that rank alone guarantees physically accurate measurements or that shaft torque without calibration is reliable.

Proposed experiment: randomize independent factors `load∈{off,on}` and `recovery∈{ordinary,enhanced}` within blocks; keep phase/pulse timing fixed initially, then repeat with controlled timing treatments. Use blinded arm ordering, repeat baseline windows, shaft torque/RPM and all-port synchronized acquisitions. Reject windows with unmatched stored-energy endpoints, temperature drift, nonstationary rotor speed, insufficient input-meter bandwidth, missing port or undocumented switching. Evaluate each arm's energy closure and factorial interactions with predeclared bounded uncertainty *before* interpreting any claimed effect. Repeat over load strength, RPM and temperature to expose hysteresis and motor-efficiency changes.

The original reel provides approximately 2354 RPM, 285–287 W displayed motor input and narrated ~45 W loaded electrical output. It does **not** supply the shaft torque, source-selected netlist, all-port meter calibration or matched inventory endpoints needed to populate this table. No intervention result may be inferred from those coarse values.

## 5. A–H/Ω roadmap interpretation

| Tranche | Model-level cut now closed | Strong remaining gate |
|---|---|---|
| **A×B** | Previous nonlinear coenergy/finite-slew current benchmark retained | Source-selected flux/torque law with load/pulse variation |
| **C×D** | 2×2 recovery interaction has exact dissipative displacement witness; previously explicit reverse-path switch losses | Real bidirectional converter and original switching state |
| **E×F** | Exact **two-ledger motor/shaft/generator weld**; fixed-input versus increased-shaft counterexample | Source original torque, motor efficiency and generator braking map |
| **G** | Factorial energy-closure acceptance and source-independent intervention contrasts | Global resource-constrained physical frontier plus uncertainty |
| **H** | Five distinct energy-consistent rival worlds; rank-5 independent sensor design | Actual synchronized original V2 data and uncertainty calibration |
| **Ω** | Exact energy-port cancellation and 4-arm interaction theorem | Source-calibrated stationary complete apparatus proof |

**New restricted model-leaf names:** `v2OmegaMotorShaftGeneratorTwoLedgerAllStatesExact`; `v2OmegaLoadedUnloadedConstantInputShaftNonidentifiability`; `v2OmegaFactorialLoadRecoveryInteractionSignedDissipationWeld`; `v2OmegaFiveWorld45WNegativeControls`; `v2OmegaTorqueAndStorageMeasurementRankFive`; `v2OmegaWorstCaseFourArmInteractionUncertainty`.

These are verified as rational algebra and Python regressions; they are **not yet Lean/Agda kernel theorems**. The original 16 strict P0–P4 endpoints remain **OPEN**. In particular, a manufactured physical machine model cannot be counted as independent evidence that the original speaker's circuit recovers magnetic energy, has a particular coil count, or runs at a stationary efficiency anomaly.

## 6. Reproduction and independent checks

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 bash scripts/check_v2_omega_load_intervention_weld.sh
```

Expected: 41 new tests; 242/242 total in the selected repo modules when the prior 201 tests and their donors are present. Agda and whole original-machine physical acceptance are distinct and **NOT RUN**. The artificial case numbers are intentionally transparent rational accounting witnesses, not calibrated efficiency predictions.
