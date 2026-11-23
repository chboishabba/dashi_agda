# J17 — Native J12 restored-cycle wave absorption reverse solve and event-stable local controls

**23 November 2026.** This analysis consumes the *original source-authored* J12 nonlinear, seven-state, coupled-coil/capacitance/diode/bank/hysteretic-spark/open-wave-port ODE, plus the existing J16 switch-event concept. Results are **conditional dimensionless synthetic mathematics**, not an original Filsinger apparatus, a calibrated Duga/HAARP/SURA electromagnetic input, energy measurement, gravity effect, or Agda-kernel certificate.

## Reused original-owner and acceptance provenance

- Native J12 owner: [`scripts/check_smith_filsinger_j12_restored_cycles_20261122.py`](../../scripts/check_smith_filsinger_j12_restored_cycles_20261122.py), originally Git blob `5e4d272438556327034e1f8ae949c5102f06cf6a`; now **`f5f66e343a979dfe2bc70f68e1e98fce75817653`**, changing only the hardcoded default drive `2*np.sin(t)` to **`p.get('drive_amp',2.)*np.sin(t)`**, retaining the exact old default and making a true driver-OFF negative control possible without constructing a new circuit.
- Existing J16 source `scripts/check_smith_filsinger_j16_event_order_20261122.py`, originally blob `89d63c04d57e97a638e65479ff83159ff1b9d0b2`; switch-event label and time matching are distinct from mere count matching.
- **New exact native consumer:** [`scripts/check_smith_filsinger_j17_wave_absorption_reverse_solve_20261123.py`](../../scripts/check_smith_filsinger_j17_wave_absorption_reverse_solve_20261123.py), Git blob **`d0e5220367b17d121a453b147d7de1eec7ae5f7e`**, byte-matched to actual locally executed script; **exit 0, PASS**, local SymPy 1.14.0.
- [Machine-readable J17 local acceptance receipt](../../Artifacts/smith-filsinger/j17_native_restored_wave_absorption_inverse_20261123.json). This records both positive and negative controls, exact model checks, branch limitations, and NO physical promotion. No GitHub Actions credits spent.

## Exact original J12 wave work inversion

The J12 wave port computes

$
\begin{aligned}
p_{\mathrm{in}}&=s_r^2+s_i^2,\\
p_{\mathrm{out}}&=(s_r-hq)^2+(s_i-hz)^2,\\
h&=\sqrt{2\gamma_{\mathrm{rad}}}.
\end{aligned}
$

Local SymPy proves without approximation:

$
p_{\mathrm{wave,net}} =
2h(s_r q+s_i z)-h^2(q^2+z^2).
$

Hence **positive finite-time net wave work** requires the integral of coherent source-to-resonator overlap to exceed the radiative response cost; it does not establish a separately measured source, positive electric load work, or efficiency. The original J12 *one-boundary* energy identity is

$
W_{\mathrm{driver}}+
(W_{\mathrm{incident}}-W_{\mathrm{outgoing}})
=
W_{\mathrm{spark}}+W_{\mathrm{diode}}+
W_{\mathrm{copper/bleed/internal}}+
(U_1-U_0).
$

All terms are retained, and the model must return **all seven** states (including magnetic, electric, bank and internal radiating state) rather than a single capacitor voltage.

**CRITICAL naming:** `W_spark` is `∫ Gspark * on * b² dt`, a **dissipative switched bank dump** in native J12, NOT a separately instrumented useful load. The observed enhancement in `W_spark` is a circuit allocation/transient signature; it cannot be called harvested usable output unless an actual secondary load and conversion/collection path is added with its own loss ledger. Positive net wave absorption by itself may be entirely converted to heat.

## Local restored-cycle acceptance at selected low spark thresholds

Native `periodic` is called with `Von=0.003`, `Voff=0.0009`, `phase=0.3 rad` and original other default J12 coefficients. It iterates the **native 20π model-time interval**, checks state closure at `tol=2e-6`, checks storage delta below `1e-5`, and checks signed work residual below `1e-6`. `phase` is the *model incident wave phase*, not physical Duga/HAARP/SURA phase.

| Input amplitude | Incident work | Outgoing work | Net wave work | Spark dissipation | Storage change | Events |
|---:|---:|---:|---:|---:|---:|---:|
| 0 (driver only) | 0 | 0.122902 | **−0.122902** | 0.00006096 | −4.73e−10 | 20 |
| ~0.825627 (numeric boundary) | 42.829933 | 42.829925 | **+7.64e−6** | — | within restored tolerance | — |
| 1.20 | 90.477868 | 90.341265 | **+0.136604** | 0.00017489 | +2.64e−8 | 6 |

**First actual inverse root:** `brentq` on the native model's finite restored-cycle `W_net(a)`, bracketing `0.8–1.2`, found `a≈0.82562676438`; residual `7.64e−6` work units at its finite accuracy. It is a **numerical sign crossing**, NOT a proven globally unique/smooth threshold. Source amplitude 1.2 is **12×** the earlier illustrative source amplitude 0.10 and has **no physical calibrated antenna or transfer interpretation**. At 1.2, *only about 0.151% of incident wave work* remains net across this selected wave port, while signed driver work is approximately **24.7787**; the small net is a subtraction of two large numbers and requires precision / model-fidelity scrutiny.

## Two-objective reverse solve: wave absorption vs bank spark dissipation

At fixed `a=1.2`, phase=0.3, restored-cycle default other coefficients:

| Coil-to-wave coupling k | Net wave work | Spark dump work | Spark events |
|---:|---:|---:|---:|
| 0.08 | +0.217977 | 0.00002394 | 4 |
| 0.15 | +0.136604 | 0.00017489 | 6 |
| 0.25 | −0.022446 | 0.00087734 | 8 |

**Strong coupling can increase bank discharge while switching net wave absorption back negative**; neither objective is equivalent to actual recovered useful electrical energy. Radiative damping perturbations (`gamma_rad=0.04` vs `0.16`) gave net wave +0.037702 vs +0.356040 at the selected branch; changing diode drop `Vd=0.05` vs `0.15` gave spark dump 0.00021779 vs 0.00013691. These are **selected restored synthetic cases**, not monotonicity/global extremal theorems or measured device controls.

## Source-off and switching negative controls

The native optional driver-amplitude flag yields four **actual single-interval** comparisons: both OFF (zero initial state, zero work); driver ON/wave OFF; driver OFF/wave ON; both ON. The driver-off/wave-on case has **positive finite-interval** net wave work `+0.3319192856`, spark work `~9.64e−5` and **positive storage accumulation `+0.05510515`**. This does not certify a restored source-only cycle. Additional native `periodic` tests at `max_iter=28` and 50 **did not produce a restoration certificate**; that is an unresolved selected numerical fixture, not a proof that source-only solutions cannot exist.

At `a=1.2` three `±0.005` local perturbation pairs each preserved the original six ON/OFF switch labels and positive net work; maximum paired event-time shifts were approximately **0.00164** (input amplitude), **0.00980** (input phase), **0.08032** (coil coupling) model-time units. These selected **local checks** do not repair the prior J16 **~6.34** event-time branch ambiguity elsewhere. More generally, source-amplitude changes altered the count from 20 at a=0 to 6 at a=1.2; **do not claim global smoothness** of the crossing or rank 5/5 inverse identifiability.

## Existing external source and geometry constraints

Prior [Duga/HAARP/SURA/Pais/YBCO native J12 source weld](SmithFilsingerDugaHAARPHFSuperconductingGravitySourceWeld20261123.md) remains canonical for source labels and time/field separation. The positive absorber is a **generic** dimensionless J12 `omega=1.1` source; nothing identifies its amplitude 0.82563 with Duga's HF ~10 Hz pulse rhythm, HAARP electrojet ELF/VLF, SURA whistlers, or 7.8-kHz *acoustic* Filsinger recording. RF/plasma frequency conversion/phase-matching and same-time receiving E/H still need an original source-specific Maxwell F13 transfer operator. Pais superconducting/gravitational claims remain in a separate mechanical/field-momentum/gravimeter channel and are not funding for electric source work.

## Maximum-cut continuation (without unverifiable observations)

1. **J17b:** source-independent signed incremental work at *matched driver and model storage/switch branch*, then classify bank dump, useful load and resistive losses separately. Optimise **useful load / net incident-wave absorption**, not `W_spark` alone.
2. **J17c/J16:** certify smooth event-time indexing near every proposed zero crossing; use matched event labels and chronology, clamp branch-grazing negatives, explicit perturbation intervals and source-amplitude hysteresis loops. Where event histories differ, treat each as a distinct branch; no differentiation across untracked switch relabellings.
3. **J17d/F13:** with exactly existing Maxwell/ADE, compute causal passive source-specific field-to-port response and explicit loss/conversion work, keeping source clock and dimensional units; no reuse of observed historic signal as actual Filsinger input.
4. **F15:** obtain a restored, signed, source-only physical load case *if it exists*; current native driver-off test is merely transient. Maintain source, pump, stored field, diode/spark, outgoing and heat in the same boundary.

**Status:** J17 native synthetic acceptance complete, exact script and receipt committed; *physical environmental extraction / usable load / source-only restored cycle / original pin connectivity / pinned Agda kernel* remain OPEN. Reuse source owners and original external attribution rather than constructing a duplicate theory.
