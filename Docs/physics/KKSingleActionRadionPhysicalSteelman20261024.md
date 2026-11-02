# KK gravity 2026-10-24: same-action radion, fifth-force and winding stabilisation max-cut

## Canonical physics consumer / contributor provenance

This cut deliberately *does not* elevate the Alexander horned-sphere donor (PR #1244) into an Earth KK prerequisite. It is relevant only for global holonomy/complement-topology claims: full non-Abelian loop consumers do not factor through flat U(1) characters in certain perfect-group examples. No wild Earth geometry is assumed.

The main algebraic donor is **PR #1239**, `scripts/check_kk_radion_reduced_action.py`, with the classical KK Jordan-frame zero-mode Lagrangian `sqrt(-gJ)*[b R_J - kappa² b³ F²/4]` (up to a boundary term and overall 5D coupling). PR #1241 already owns the massive-radion spherical Helmholtz solution. This tranche derives its *conditional source coefficient from an explicit matter-frame assumption* rather than freely selecting it.

External scientific anchors:
- Wehus & Ravndal, *Dynamics of the scalar field in 5-dimensional Kaluza-Klein theory*, arXiv:hep-ph/0210292 (5D->4D E-frame, cosmological/exponential terms), https://arxiv.org/abs/hep-ph/0210292
- Bertotti, Iess & Tortora, *Nature* **425**, 374–376 (2003), DOI 10.1038/nature01997, measured gamma=1+(2.1±2.3)*10^-5.
- Herdeiro, Radu & dos Santos Costa Filho, JCAP 2026(4) 005, DOI 10.1088/1475-7516/2026/04/005: KK EMD coupling sqrt3, rotating charged black holes are source-specific vacuum exteriors, not neutral Earth.
- Standard scalar-tensor/Brans–Dicke weak-field relation for the specified universal Jordan matter coupling, not an attribution of this reduction or new mathematics to DASHI.

## Model 1: gravitational zero-mode plus explicitly chosen physical matter frame

For circle y~y+2pi, `ds5²=gJ_mu_nu dx^mu dx^nu+b²(dy+kappa A)²` and a positive circle radius b(x), the metric determinant obeys `sqrt(-G)=b sqrt(-gJ)`. Set background b0 and `M4²=2pi b0 M5³`. The Einstein-frame metric `gE=(b/b0)gJ` yields a canonical scalar
`varphi=sqrt(3/2) M4 log(b/b0)`, and `gJ=e^{-sqrt(2/3)varphi/M4}gE`.

**Matter is NOT automatically Jordan-coupled.** A physical zero-mode matter action `Sm[gJ,psi]` is a candidate-specific assumption to be separately sourced in 5D. Under THAT assumption, `A(varphi)=exp[-varphi/(sqrt6 M4)]`; `d log A/dvarphi=-1/(sqrt6 M4)`. The unscreened scalar force strength is `2(M4 dlogA/dvarphi)²=1/3`, giving massless-Brans–Dicke `gamma=(1-1/3)/(1+1/3)=1/2`. This bare, unscreened weak-field model conflicts with Cassini if it describes the Sun. Alternative 5D matter coupling or stabilisation cannot be inferred merely by conformal frame relabelling.

For an EFFECTIVE, independently specified positive radion mass m (not from the winding sector below), variation gives the weak, static linear source equation `(nabla²-m²)varphi= -rho/(sqrt6 M4)` for nonrelativistic Jordan-coupled ordinary matter. This is the missing coupling map to PR #1241's Helmholtz fixture. For a uniform sphere R,rho, r>=R, the fifth-force magnitude relative to `F_N=GM/r²`, with bare `8pi G=1/M4²`, is exactly
`F_radion/F_N = [z cosh(z)-sinh(z)]/z³ * (1+mr) exp(-mr)`, `z=mR`.
As `mR->0`, this tends to 1/3. The inside/outside solutions remain regular, C1 and satisfy the declared linear field equations. Real Earth structure, fifth-force calibration, scalar backreaction, environmental screening and measured terrestrial G are not included.

Command: `python3 scripts/check_kk_jordan_sourced_sphere.py`. Verified illustrative values at r=12,270 km from center, R=6371 km: mR=0.01 ~0.333276; mR=0.1 ~0.328219; mR=1 ~0.156875; mR=5 ~0.00165985; mR=10 ~8.6824e-6; mR=20 ~4.2564e-10. These are synthetic theory sensitivity values, NOT measurements or observational KK bounds.

## Model 2: concrete 5D bulk cosmological energy + phase-winding scalar

Specify **one** fixed-modulus bulk phase-field model

`S5= integral sqrt(-G) [M5³ R5/2 - Lambda5 - v²/2 G^AB (partial_A Theta)(partial_B Theta)]`,
`Theta=n*y+chi(x)`, n integer nonzero, v>0, kappa nonzero. Circle period is 2pi. Fixed modulus itself is an EFT assumption; a microscopic radial-mode potential and full higher-dimensional stability are still independent.

Using the KK metric inverse,
`G^AB partial_A Theta partial_B Theta = (dchi-n*kappa*A)^2_gJ + n²/b²`.
The invariant `dchi-n*kappa*A` survives local gauge transformations, hence the phase yields a **Stueckelberg mass for the KK graviphoton** when n*v*kappa !=0 (after canonical kinetic normalisation). If the geometrical U1 is claimed to be ordinary unbroken electromagnetism, this minimal winding condensate is not admissible without a separately justified mechanism preserving a massless photon or changing the EM identification. Gauge invariance of the action is NOT enough to imply the vector remains massless.

For constant phase gradients dchi-n*kappa A=0, the 4D E-frame zero-mode potential is
`V_E(b) = 2pi b0² [Lambda5/b + W/b³]`, `W=v² n²/2 >0`.
Critical radius b* requires `Lambda5=-3W/b*² <0`, and then
`V_E(b*)=-4pi b0² W/b*³ <0`,
`V''_E(b*)=12pi b0² W/b*^5 >0`.
So the **stable stationary radius has negative four-dimensional vacuum energy** (AdS), not an asymptotically flat Earth-compatible exterior. Simultaneous `V=0` and `V'=0` forces W=Lambda=0, contradicting nonzero winding. This is a conditional two-term potential no-go, not a theorem ruling out realistic stabilised KK theories. Additional bulk matter/Casimir terms, screening or potentials may change the conclusion; any addition changes the action and must be checked against both physical consumers again.

Command: `python3 scripts/check_kk_single_action_winding_steelman.py`. SymPy checks inverse metric, gauge-invariant Stückelberg derivative, Einstein-frame potential derivatives, E-frame/Jordan-frame canonical scalar, PPN gamma and scalar source coefficient.

## BIDI against observable AND steelman

Existing `KKSteelmanBidirectionalConsumerExact.agda` is the canonical scoped physical eligibility contract, importing the repository's `FormalClaimTransportGeometryExact` and `ConsumerFibreRepairExact`; we do NOT add another abstract framework.

- Consumer **C_scalar**: positive-mass sourced Helmholtz model and finite-size force at fixed explicit Jordan coupling. **PASS (conditional at linear effective-field level)**, with arbitrary stabilisation mass remaining a source-side gap.
- Consumer **C_EM**: an unbroken massless geometrical U1 photon. **FAIL** for the particular nonzero-winding condensate above, since the Stückelberg derivative generates a positive A² contribution.
- Consumer **C_flat**: stationary zero 4D vacuum energy with nonzero winding using *only* Lambda5 + winding kinetic energy. **FAIL** as proven by simultaneous stationary/potential equations.
- Consumer **C_Earth**: regular sourced rotating 5D solution, coherent 5D matter origin, scalar mass, source and exterior matching, existing experimental tests, and same-observable LARES nodal drift. **UNINHABITED**.
- Optional consumer **C_horn**: global non-Abelian complement topology/flat U1 limitations, answered in PR #1244 only. It neither blocks nor certifies ordinary physical Earth KK.

**High-alpha next model**: find a stabilisation sector which preserves the chosen massless U1 and has a stable near-zero 4D vacuum, then derive its matter-source coupling and test scalar force before doing more frame dragging. Quantum/Casimir and massive-field one-loop radion potentials are promising candidates to evaluate, but none is claimed viable here. If no candidate has both properties, a no-go is a valid physical finding.

## Audit boundaries

SymPy scripts locally executed and passed mathematical checks on analogous committed source. No exact-head Agda kernel receipt, no 5D full variation verification, no 5D matter interior, no measured parameter inference. Keep the original mathematical and scientific attributions. DO NOT use SensibLaw/PNF/W3, horned-sphere geometry, or a fabricated Earth KK charge as prerequisites.
