# KK–YM369 same-metric spin-connection maximum cut (2026-11-18)

## Executive conclusion

The old literal gauge-equivalence test (KK U1 monopole ≠ BPST SU2
connection) was EXPECTED and is not the right unification test. We now have
an exact **positive local same-metric derivation** from the Taub–NUT
four-metric: its Levi–Civita curvature has a nonzero, noncommuting chiral
SU2 component and the opposite chiral component vanishes at a selected
nonsingular point. This is a derived spin-gauge curvature of ONE metric,
not an independent BPST connection and not a proof that the original
Balaban physical Wilson carrier equals the KK field.

The derivation is classical prior mathematical physics, not an original
DASHI theory discovery. This round adds an independent source-equivalent
exact coordinate calculation and an explicit 4D Euclidean/5D Lorentzian
stress-energy discriminator.

## Exact original geometric input and normalizations

Choose the 5D Lorentzian vacuum action
```
S_gravity = (16 pi G5)^-1 int d^5x sqrt(-G) R5
ds5^2 = -dt^2 + ds_TN^2
ds_TN^2 = V(dx^2+dy^2+dz^2) + V^-1(dpsi+A)^2
V = 1 + m/r,  r^2=x^2+y^2+z^2,  m>0
```
The regularity circle period is 4*pi*m. The orientation originally used
in PR #1531 used A=m*cos(theta)dphi, yielding dA=*dV and normalized
Chern -1 with a=(dpsi+A)/(2m), circle period 2pi. Here choose the
opposite but isometric fibre orientation (psi -> -psi),
```
A_N = m(1-cos(theta))dphi
    = m(-y dx+x dy)/(r(r+z))
dA_N = - *dV.
```
It is a smooth north-axis gauge away from the nut. Its normalized
Chern number is +1; sign and the names SU2+/- swap under orientation
reversal. NEVER compare the two conventions without this mapping.
Neither Chern integer by itself produces a spin-half quantum state.

Select m=1 and p=(x,y,z)=(0,0,1). The coordinate metric equals
diag(2,2,2,1/2). Use its orthonormal **vector** frame
(∂x,∂y,∂z)/sqrt(2), sqrt(2)∂psi. Derive all g_ij, first and
second coordinate derivatives, Christoffel symbols and derivatives,
then R^a_{bcd} (not a supplied curvature ansatz).

Independent script:
`scripts/check_kk_taubnut_induced_su2_spin_connection_exact.py`
has exact SymPy assertions:

- 16 Ricci components vanish at p.
- In the self-dual/anti-self-dual SO4 Lie-index projection,
  `C_±(cd)=(R_23cd ± R_14cd, R_31cd ± R_24cd, R_12cd ± R_34cd)`,
  the minus sector vanishes at p in this orientation.
- `C_+(12)=(0,0,1/4)`, `C_+(13)=(0,1/8,0)`.
- Full 2-form self-duality at p:
  `C_+(12)=C_+(34)`, `C_+(13)=-C_+(24)`,
  `C_+(14)=C_+(23)`.
- With the EXISTING quaternion Lie convention `[u,v]=2u×v`,
  `[C_+(12),C_+(13)]=(-1/16,0,0)`.
  This is a concrete noncommuting chiral curvature **derived from the
  same metric** as the KK U1 connection.
- The factor used here is an unnormalized chiral Lie-index projection;
  an actual SU2 connection requires selection of generators,
  't Hooft symbols, half factors, trace normalization, and coupling.
  Do not call the displayed curvature components the fully physically
  normalized gauge curvature without those factors.

**Verification:** source-equivalent local script executed and passed;
the exact commit blob must still be run in a checked-out repository.
The calculation is LOCAL at one point and does not independently
typecheck the smooth global spin-bundle construction.

## Published direct positive route: already solved classically

1. Maciej Dunajski, *Skyrmions from gravitational instantons*,
   Proceedings of the Royal Society A **469** (2013), 20120576,
   DOI: **10.1098/rspa.2012.0576**.
   Section 2 takes the SU2 self-dual spin connection of Taub–NUT as a
   Yang–Mills connection; derives the Pope–Yuille instanton and
   computes its holonomy and a Skyrme field. His Taub–NUT skyrmion
   has **topological charge 2** in the specified orbit reduction,
   NOT a demonstrated electron or automatically spin-1/2 particle.
   Published original source:
   https://www.damtp.cam.ac.uk/user/md327/skyrmion_proc.pdf
2. Li-Sheng Tseng and Jiawei Zhou, *Mapping Cone Connections and their
   Yang–Mills Functional*, Communications in Mathematical Physics
   **406**, 156 (published 3 June 2025),
   DOI: **10.1007/s00220-025-05311-8**.
   Example 3.2 EXPLICITLY derives an SU2 cone Yang–Mills solution by
   reducing Taub–NUT's spin connection along a nontrivial circle
   fibration, including the extra adjoint scalar B and its coupling
   to the bundle curvature zeta=d(theta). This is a FAR stronger
   existing original source than simply matching C3 labels.
   https://link.springer.com/article/10.1007/s00220-025-05311-8
3. Classical Gibbons–Hawking (1978), Gross–Perry (1983), Sorkin (1983):
   original gravitational instanton and KK monopole.
4. B. Diez, *Gravitational Cheshire effect from Yang–Mills
   instantons*, arXiv:2610.24127v1, 16 October 2026, **preprint**,
   considers four-dimensional EUCLIDEAN Einstein–YM, not the generic
   five-dimensional Lorentzian particle problem.
   https://arxiv.org/abs/2610.24127

## Why the 5D backreaction is still open: rigorous algebraic discriminator

On an oriented Euclidean 4D spatial orthonormal frame, any self-dual
SU2 curvature has components, for each colour a,
```
F12^a=F34^a=p_a
F13^a=-F24^a=q_a
F14^a=F23^a=t_a
```
Define |F|²_full=Σ_a Σ_i,j (F_ij^a)^2 =
4 Σ_a (p_a²+q_a²+t_a²). Then
`T_E,ij = (1/g²)[Σ_a,k F_ik^a F_jk^a - δij |F|²_full/4] = 0`.
This is the familiar four-dimensional Euclidean cancellation, exactly
checked for all arbitrary 9 coefficients by
`scripts/check_kk_ym_selfdual_stress_dimension_gate.py`.

But under `G_5=-dt²+g_TN`, static `F0i=0`, the **Lorentzian**
energy density is
`T_00 = |F|²_full/(4g5²) = Σ_a(p_a²+q_a²+t_a²)/g5²`,
strictly positive wherever F ≠ 0. Hence the vacuum product metric
has `G_00=0` and cannot satisfy the coupled Einstein-YM equation
`G_00=8πG5 T_00` with that nonzero field alone. The 2026 Euclidean
Cheshire statement does NOT pay this 5D gate.

Options: solve fully backreacted equations, change the higher-dimensional
matter/source content with accounted stresses, or explicitly restrict
the claim to Euclidean gravitational-YM geometry and its holonomy.
Do not claim an independent 5D Lorentzian Einstein–YM solution here.

## Native 369/YM source translation

Existing original owners: `BalabanSU2QuaternionCarrier`,
`BalabanSU2LieBracket`, `SU2Bracket369OrientationBridgeExact`,
`BalabanCMP109SpatialC3ActionExact`,
`CompactLieLatticeGauge`,
`BalabanC3MonsterEquivarianceAuditExact`,
`YMClayNativeSixPlaneC3SourceReductionExact`, existing Hopf U1
and source stress/Hodge modules. Reuse rather than duplicate.

The correct source-to-source chain is:
```
actual 5D KK metric
 -> actual Levi-Civita/Spin4 connection on its spatial four-metric
 -> one SU2 chiral spin connection (Pope–Yuille route)
 -> circle dimensional reduction with adjoint scalar (Tseng–Zhou)
 -> original 369/YM continuum connection and Wilson path comparison
 -> original physical RG/Schwinger/OS and eventual soliton spin gates
```
The third and fourth arrows are already classical literature
constructions, but **not** kernel accepted on the existing original
DASHI carrier. To identify the physical native Wilson field, derive
source-indexed edge holonomy for this exact smooth connection, patch
transport, gauge-covariant continuum limit, actual original-generated
Balaban source identification and action/energy/stress normalization.
Spatial C3 equivariance is necessary symmetry data, not enough.

## Updated exact acceptance gates

- [x] Derived local chiral SU2 nonabelian curvature from same TN
      metric, exactly verified using local coordinate derivatives.
- [x] Source-verified direct prior-art spin-connection/YM/Skyrme route;
      original authors credited.
- [x] Separated 4D Euclidean no-backreaction from 5D Lorentzian T00
      using arbitrary-colour exact SymPy identity.
- [ ] Construct actual global chiral spin connection forms from chosen
      tetrad on all northern/southern overlap patches and fix generator
      normalization with original YM SU2.
- [ ] Establish global YM action, topological charge and finite energy
      including ALF boundary terms. Published Dunajski/skyrmion topology
      is not by itself a normalized KK instanton charge.
- [ ] Transport exact same field to original native 369/YM Wilson
      source, not an arbitrary surrogate gauge field.
- [ ] Couple to full 5D Lorentzian Einstein–matter source and solve
      nontrivial backreaction, or state a Euclidean-only goal.
- [ ] Derive the physical soliton configuration-space rotation/exchange
      loops; do not infer spin-1/2 from Chern, Hopf or baryon integer.
- [ ] Full nonlinear stability, observational deviations and source
      test with actual physically measured channels.
- [ ] Exact-head pinned Agda kernel acceptance; new Python scripts
      are exact local arithmetic, not kernel theorems.

## Attribution and trust rules

CLASSICAL roots (Gibbons–Hawking, Gross–Perry, Sorkin,
Pope–Yuille as reported by Dunajski, Dunajski 2013, Tseng–Zhou 2025,
Diez 2026 preprint) retain original credit. Existing DASHI 369/YM,
Hopf and spin owner modules retain their independent proof credit.
The user's questions identify the target same-geometry normalization,
research priorities and insistence on source attribution. New
ChatGPT-assisted work, dated 2026-11-18, consists ONLY of the local
symbolic tensor checker, 4D/5D stress discriminator and source-to-source
integration/audit ledger. No invention of the known spin/YM/Taub–NUT
or Skyrme mechanisms is claimed.

## Supplemental exact generator and curvature normalization

Dunajski (2013) Eq. (2.7) uses `[t_i,t_j]=-(1/2)epsilon_ijk t_k`.
The original DASHI SU2 quaternion basis uses
`[e_i,e_j]=2epsilon_ijk e_k`. For the SAME Levi-Civita orientation
and epsilon conventions the exact embedding is
`t_i=-e_i/4`, checked in the committed SymPy script.

Our raw Lie-index chiral vector `C_i=R_jk+R_i4`, in this self-dual
frame, is `2R_jk`, while Dunajski's `F^i=(1/2)epsilon_ijk R_jk`
has numerical coefficient `C_i/2`. Therefore the full generator
coefficient expressed in native `e_i` is `-C_i/8`. At the selected
point the resulting two native-basis curvature vectors are
`(0,0,-1/32)` and `(0,-1/64,0)`, with quaternion Lie bracket
`(-1/1024,0,0)`. These exact normalized finite computations PASS
in the revised script.

This is a chosen *generator convention* matching the published
spin-connection construction. It still does not assign the YM action's
physical coupling `g5`, trace normalization or gauge-bundle global
identification. If an alternate 't Hooft eta convention is selected,
the signs/factors must be transported explicitly, not copied blindly.
