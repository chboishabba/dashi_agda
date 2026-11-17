# Smith/Filsinger F10-PLASMA / F13-NL — retarded and replenished source frontier

**17 November 2026.** This is a specified **computational model**, not evidence that the original apparatus can access solar/magnetospheric work. The motivating bridge, conductivity and source/sink timing are user hypotheses. Original Filsinger reel/proposed plate and Smith cited designs remain separate sources.

## Reuse / status before extension
- PR #1521 `SmithFilsingerDispersiveMaterialPortExact.agda`, `check_smith_filsinger_earth_admittance_access.py`, and the nonlinear Debye/Hall port own constitutive and source-access abstractions. They are not silently copied or assumed merged into PR #1524.
- PR #1524 `SmithFilsingerFinitePhaseMatchingExact.agda`, `SmithFilsingerReplenishedCycleCapExact.agda`, `check_smith_filsinger_local_maxwell_port.py`, `check_smith_filsinger_f10_f13_field_bridge.py`, `check_smith_filsinger_source_first.py` and the fail-closed `Artifacts/smith-filsinger/source_first_original_evidence_contract_20261117.json` provide original source/measurement and reversible-work contracts. The evidence contract remains **all original-world nulls**.

## Constructed finite passive causal port
`scripts/check_smith_filsinger_nonlinear_retarded_source_port.py` supplies a finite trial admittance,
[
Y(s)=G_{m dc}+sC+sum_k \frac{g_k s}{s+\omega_k}
+\sum_m \frac{\alpha_m s}{s^2+\gamma_m s+\Omega_m^2}.
]
With nonnegative `Gdc,C` and strictly positive poles/dampings/gains, each branch is causal and has nonnegative real part on the imaginary frequency axis. **Debye** state: `q'=omega(V-q)`, `i=g(V-q)`, stored energy `g*q²/(2*omega)`, dissipation `g(V-q)²`. **Lorentz** state: `q''+gamma q'+Omega²q=V`, `i=alpha*q'`, stored `alpha*(q'²+Omega²q²)/2`, dissipation `alpha*gamma*q'²`.

These are finite positive-real LTI *surrogate* branches, not a fitted Wait/Greifinger vertical modal solution. `Y(i omega)` passivity does not establish a source-driven response, and positive-real frequency-axis behaviour alone does **not** justify a positive integrated port work for arbitrary nonzero initial reservoir states; include all internal storage and initial/final terms. `C s` contributes an instantaneous displacement-current component: causality need not imply delayed-only response. Likewise no generic `omega h/c` radiation rule is assumed.

## Nonlinear conductivity + electron continuity and exact energy split
For synthetic geometry of cylinder length `L`, radius `a`, mobility `mu_e`:
[
 G_{m ch}(n)=\frac{\pi a^2 e\mu_e n}{L},\quad
 I=\frac{V_s-v}{R_{m ext}+1/G_{m ch}(n)},\quad
 C_r\dot v=I-G_L v.
]
The prescribed carrier kinetics are
[
 \dot n=S_0+\nu_{m ion}n-\nu_{\rm att}n-\beta n^2.
]
Ionization pair energy `E_pair` is stored as `U_ion=pi*a²*L*E_pair*n`. Crucially, every creation term `E_pair*volume*(S0+nu_ion*n)` is paid by an **explicit ionization pump** and every attachment/recombination loss is `E_pair*volume*(nu_att*n+beta*n²)`. This is a *simplified bookkeeping convention*: real discharge channels may require excitation, electron thermal, gas enthalpy, attachment to negative ions, transport, radiation and chemical energy not captured by `U_ion`; an electron-only density does not by itself measure pair inventory. Physical F10 remains OPEN.

The separate dynamical source scenario has
[
 C_s\dot V_s=g_{\rm recharge}(V_{\rm exogenous}(t-\tau)-V_s)-I.
]
This makes source depletion and recharge explicit and represents a causal delayed **exogenous** forcing; it does not solve remote solar ionospheric backaction, propagation geometry or delay-dependent Maxwell sources. Its conservation reads
[
 W_{\rm exogenous}+W_{\rm ion,pump}+W_{\rm ctrl}
 =W_{\rm load}+W_{\rm feed}+W_{\rm ext}+W_{\rm ch}
   +W_{\rm ion,loss}+W_{\rm ctrl,aux}+\Delta(U_s+U_r+U_{ion}).
]
Every term is integrated synchronously by the ODE numerical solver; the analytic instantaneous cancellation is exact from the specified equations. Numerical residual and convergence require local replay, not inference from symbolic algebra.

## Exterior bottleneck and nonlinear admittance
For `Gch>0, Gext>0`, `G_series=Gch Gext/(Gch+Gext)<Gext`. A large local `Gch/Gch0` is possible under assumptions, but cannot bypass the exterior series connection, and does **not** mean that the remote solar source supplies that current. The assumed nonlinear `I(V)=G0 V+gamma V³` provides `dI/dV=G0+3 gamma V²` and secant/power conductance `I/V=G0+gamma V²`. Small signal `dI/dV` and real extracted port work must not be conflated.

**Experimental promotion:** same-unit source identity + P1 synchronous V/I + P2 nonlinear retarded source impedance under load + R2 spatial Maxwell/plasma/soil/ionosphere + R3 positive net signed natural source work with complete return and independent replenishment. Nonlinear channel conductance, delivered load work, ionization paid by pump and source depletion are necessary checks, not sufficient proof of F15.

## Literature / attribution
- Y. P. Raizer, *Gas Discharge Physics* (1991): general plasma electron kinetics and breakdown physics, **not** fitted parameters.
- X. M. Zhao et al. (1995) and A. Houard et al. (2023) https://doi.org/10.1038/s41566-022-01139-z: atmospheric discharge channel observations; not a measured solar harvesting receiver.
- A. Tip (1998), *Linear absorptive dielectrics*, *Phys. Rev. A* 57, 4818, https://doi.org/10.1103/PhysRevA.57.4818.
- Wait, *Electromagnetic Waves in Stratified Media*: technique/qualitative field background; no claim we derived a stratified eigenoperator from it.
- Akasofu (1981), https://doi.org/10.1007/BF00218810; Newell et al. (2007), https://doi.org/10.1029/2006JA012015: solar/magnetosphere *global* coupling priors, not locally available current at original apparatus.
- User's control/phase/solar source hypothesis and DASHI model construction explicitly not attributed to the cited researchers.

**Safety:** observational and purely mathematical simulation only, no physical atmospheric discharge or lightning triggering instructions.

## Acceptance
Source code `scripts/check_smith_filsinger_nonlinear_retarded_source_port.py` and `scripts/test_smith_filsinger_nonlinear_retarded_source_port.py` added to the existing `check_smith_filsinger_dynamic_replenishment.sh` harness. No exact-head acceptance/kernal CI result or original device evidence is asserted here. Original `source_first_original_evidence_contract_20261117.json` remains unchanged.
