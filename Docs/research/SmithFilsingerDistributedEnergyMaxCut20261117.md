# Smith/Filsinger distributed causal energy max-cut — 17 Nov 2026

**Source ownership:** User-origin hypothesis of resonantly timed differential branches and potentially large external Sun–Earth energy transfer. DASHI constructed finite spatial analogue. Existing PR #1521 owns nonlinear polarization / Hall–Pedersen and original soil source access. PR #1524 owns source-first original gates, source/phase, dynamic replenishment and formal welds. Classical telegrapher circuit and discrete energy cancellation are conventional physics/math, not original-device evidence.

## Highest-value advance: explicit spatial source, storage, loss and channel state
New `scripts/check_smith_filsinger_distributed_causal_energy.py` uses N node voltages, N-1 link currents, a finite source storage capacitor, nonlinear state-dependent plasma **shunt** and explicit carrier creation/decay. Source is independently stipulated and delayed in time; it is not a claimed calibrated solar generator.

```text
Cs dVs/dt = g_recharge(Vexo(t-delay)-Vs) - g_feed(Vs-V0)
C dVk/dt = I_previous - I_next - local shunt - load
L dIk/dt = Vk - V(k+1) - R Ik
dn/dt = S_seed + S_control - attachment*n - recombination*n²
G_plasma(n) = g_n*n
```

**Exact finite-chain ledger** obtained by multiplying node equations by node voltage, links by their currents and summing across internal interfaces:
[
U=\tfrac12 C_sV_s^2+\sum_k \tfrac12 CV_k^2+
\sum_j \tfrac12 LI_j^2 + E_{\rm pair}n
]
[
\dot U =
V_{exo}I_{recharge}+E_{pair}S_{create}+P_{ctrl}
-P_{recharge\ heat}-P_{feed\ heat}-P_{link\ heat}
-P_{plasma\ heat}-P_{load}-P_{ion\ loss}-P_{ctrl\ aux}.
]
Controller work and identical auxiliary loss cancel only because this simple model assumes the auxiliary work is immediately dissipated, NOT because actual controllers are free. All other work integrals are time-aligned and signed. A **new SymPy polynomial check confirms the telescoping identity** for selected N=3,5,8. It is not yet an all-N Agda induction, a continuous Maxwell proof or a strict continuum light-cone theorem. The finite LC semidiscrete ODE can have nonzero response outside an ideal wavefront due to analytic ODE propagation; no exact continuum causality is promoted. The externally stipulated waveform has a delay, not a solved Sun-to-Earth travel/feedback path.

## Independently replayed local acceptance
`python -m pytest -q test_smith_filsinger_distributed_causal_energy.py` — **12/12 PASS** after fixing command-line JSON serialization, including exact N=3,5,8 symbolic identities, source-off, stored-energy depletion, nonnegative constraints, conductance response and a loss counterexample.

Illustrative normalized N=5, horizon T=10, source exogenous DC=2, small AC envelope, 0.4 time delay:
| Metric | Baseline | Ionization-controlled |
|---|---:|---:|
| Final channel shunt conductance | .00632937 | .02717360 |
| Useful load work | .03674219 | .03591523 |
| Ion-pair creation expenditure | 1.0000 | 5.0000 |
| Controller auxiliary expense | 0 | 0.2000 |
| Net load minus the two counted pump expenses | -.96325781 | -5.16408477 |
| Energy ledger residual | 7.39e-12 | 7.33e-12 |
| Full stored-state return | false | false |

**Interpretation:** the controlled local conductivity increased **4.29×**, but the plasma is connected as a lossy internal *shunt*, so load work **decreased**. Increased conductivity is not sufficient to produce energy transfer to a chosen load, even though the controller does alter source state and total dissipation. This is a constructive failure mode, not a refutation of all plasma bridges or ionosphere-current coupling geometries. The two runs do not return to the same final stored state: do NOT call them repeatable sustained-extraction receipts or matched original-world comparisons.

## Exact remaining high-alpha upgrades
1. D1: pinned Agda acceptance for existing formal welds, source-work and phase owners; all-N discrete telescoping induction or abstract port-Hilbert cancellation.
2. R2/F10: spatially **real** Maxwell with material/ion transport, Hall/Pedersen and open ionosphere/soil boundary, and a causal retarded full-field operator. Semidiscrete LC is an intermediate negative/positive control.
3. F13/P2: independently source-calibrated terminal admittance and controllable **series or source-connected** plasma path, not assuming every high-G link is useful. Geometry must be sourced before an effective aperture is promoted.
4. F15/R3: same exogenous forcing, complete comparable initial/final source/storage states, positive signed work minus ALL controller, plasma, thermal, ionization and load losses, independently replenished.
5. F16: controller-to-cloud microphysics and cold-pool causal chain remains separate; no evidence of actual climatic influence supplied.

**Acceptance note:** The local numerical/symbolic check was executed on a standalone copy before committing GitHub text. The integrated repository shell runner now includes the test, but the **exact GitHub-head combined suite and Agda kernel were not executed** here. Physical S0/P1/P2/R1/R2/R3/D1/D2 remain OPEN; provenance/attribution preserved and ESD untouched.

## Complementary topology cut — series access versus lossy shunt

After the first 12/12 tests, the selected finite model was extended with a **series channel** on one LC link as a direct architectural comparator to the existing dissipative shunt. In the series branch the link law includes an extra carrier-dependent `R_channel=1/G_channel(n)`; the energy ledger adds `I_link² R_channel` explicitly. The algebraic telescoping energy check now verifies **both** shunt and series variants for N=3,5,8; local regression **16/16 PASS**.

| Model topology (T=10; normalized) | Base channel conductance | Controlled conductance | Base load work | Controlled load work | Outcome |
|---|---:|---:|---:|---:|---|
| Shunt (`g_n=.02`) | .00632937 | .02717360 | .03674219 | .03591523 | −2.25% load |
| Series (`g_n=2`) | .63293717 | 2.71736044 | .01310441 | .02755956 | +110.31% load |

All scenarios use independently stipulated delayed exogenous input; both controllers have the specified increased ionization expenditure **1 → 5** plus controller auxiliary **0 → 0.2**. Both models have **negative** net load after subtracting these counted expenses, and their final storage is **not** equal to their initial storage, hence **no F15 sustained natural energy acceptance**.

**Why this is important:** identical carrier-density amplification can either decrease or increase useful output depending on whether the controlled plasma is placed as a parasitic shunt or as a source-to-receiver access path. But higher load work does not imply a positive overall energy return. This establishes a useful **topology-sensitive conditional model result**, not that the actual proposed portable plate is a series conduit or that ambient solar currents can enter it. Any physical weld requires collector and return geometry, plasma material budget, independently sourced source admittance and complete-cycle comparison.

**Acceptance correction:** initial CLI had a NumPy boolean JSON serialization issue, corrected before 12/12 and then 16/16 local tests were rerun; the distributed-model committed path is included in the original consolidated Python acceptance runner. Full combined exact GitHub-head suite and pinned Agda kernel remain unverified. No original-world evidence contract was modified.
