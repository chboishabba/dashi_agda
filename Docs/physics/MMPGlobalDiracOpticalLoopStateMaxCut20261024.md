# Global charged-fermion quantum-state max-cut: true closed loop vs surrogate two-ended line

**Date:** 2026-10-24. **Owner:** draft PR #1248, head is dynamic; exact-head tests are not asserted by this source. **Critical authority:** Maldacena, Milekhin & Popov (MMP), arXiv:1807.04726 (2018, final 2020 preprint), *Classical and Quantum Gravity* **40** (2023) 155016, DOI 10.1088/1361-6382/acde30. Other primary donors: 1+1D conformal/Polyakov anomaly, zeta/Hurwitz spectral Casimir of a massless charged Dirac spinor; Lewis *Physical Review D* 101 (2020) 125019 DOI 10.1103/PhysRevD.101.125019 (2D Dirac Hadamard subtraction); Zahn *Reviews in Mathematical Physics* 26 (2014) 1330012 DOI 10.1142/S0129055X13300124 (locally covariant charged Dirac renormalization and conserved current/stress). Sadhukhan arXiv:2609.33511 and arXiv:2610.09847 (September/October 2026) supply first-order anomaly, Hall, Schwinger/polarization donor equations, **not** a full nonlinear global state.

## Critical topology correction (not another numerical tolerance issue)

MMP's negative Casimir state is formed by LLL fermions localized to **closed magnetic field lines**, traversing the wormhole and returning through the **same external ambient region**. A purely two-ended spatial geometry `R × S²` has `H1=0`, `H2=Z`: it supports nonbounding S² magnetic flux but no nontrivial spatial loop **through the throat returning outside**. Reissner–Nordström geometry glued separately to the two ends does not provide the return. By contrast a one-universe handle with two mouths has the interior topology of `(S¹ × S²)\{point}` (schematically `R³ # (S¹ × S²)`) with `H1=Z` and `H2=Z`, so closed return paths and throat flux can coexist. Topology does NOT guarantee every physical field line closes, its spin structure, its electromagnetic Wilson phase, or the renormalized quantum state. PR #1244 wild horn-sphere complementary regions have `H1=H2=0` despite nontrivial perfect pi1; their non-Abelian holonomy does not substitute for this charged fermion closed loop.

**Strongest newly identified critical dependency:** construct a *single* same-universe 3D/4D geometry, closed magnetic field lines and global spin-c/gauge connection before claiming MMP-identical circle Casimir. The previous C1 radial Israel RN matching is valid only as a separate **effective-matter GR** theorem.

## 1. One exact renormalized 2D fermionic loop functional (bounded but genuine progress)

For a specified static Lorentzian 1+1D optical circle with `ds²=-N(x)²dt²+h(x)²dx²`, circumference
`ell[N,h]=∮h/N dx`, massless complex Dirac central charge c>0, spin/flat-gauge Wilson phase `exp(2πiα)` and twisted boundary `ψ(y+ell)=exp(2πiα)ψ(y)`, define the zeta/Polyakov Killing vacuum energy **of this one globally fixed state**:

```
B2(α) = α²−α+1/6, α taken modulo 1
E_ren[N,h,α] =
     (2π c / ell[N,h]) B2(α)
   − (c/(24π)) ∮ N'(x)²/[h(x) N(x)] dx .
```

The first term is the genuine closed-circle Dirac Casimir energy. Derivation: the zeta-regularized `∑_{n∈Z}|n+α| = −B2(α)`, with fermionic zero-point sign and eigenfrequencies `2π|n+α|/ell`. The second is the curved static conformal-anomaly contribution under the specified reference subtraction. No arbitrary radial pressure input.

Set `F=(1/h)∂_x log N`, `D=(1/h)∂_x`, `t=π c B2(α)/ell²`. Variations of the SAME E yield
```
rho_2 = (1/h) δE/δN
      = (c/(12π)) D F + (c/(24π)) F² + 2t/N²
p_2   = −(1/N) δE/δh
      = −(c/(24π)) F² + 2t/N²
−rho_2+p_2 = c R_2/(24π),   R_2=−2(D F+F²)
D p_2+F(rho_2+p_2)=0
```
because the *global* optical circumference `ell` depends nonlocally on the metric but the state parameter t is constant in x on a fixed static circle.

Wilson holonomy variation with `α=α_spin+e θ/(2π)`, `θ=∮A_x dx`, gives the equilibrium persistent current
`I=−∂E/∂θ=−e c (2α−1)/ell` (away from Dirac spectral crossings, and in this convention). It is a conservative zero-frequency response, **not** the 2026 Schwinger electric polarization current or a Hall term. Large gauge change `α→α+1` preserves E.

**Exact C3 phase discriminator in this model**: NS α=1/2 has `B2=-1/12` hence *negative* Casimir energy; shifts by ±1/3 give α=1/6,5/6 with `B2=+1/36` hence *positive* Casimir energy. It is not a prediction that any three plasma regions physically create those Wilson phases. JMD 12/24 numerical coincidences do not determine α.

**Receipts:** `scripts/check_global_dirac_optical_circle_source_20261024.py` proves symbolic local Ward and curvature trace equations, tests gauge/holonomy variation, and independently finite-differences BOTH lapse and spatial metric variations at 96,192,384 sites. Observed rho derivative errors `1.534e-6,3.844e-7,9.608e-8` and radial-pressure errors `1.789e-7,4.485e-8,1.121e-8`, consistent with second-order discretization. Local PASS. A *fully globally renormalized 4D* state remains OPEN.

## 2. Optical circumference must be derived, not inserted independently

Previously [local finite Polyakov+massive S² KK effective BVP] the NS state parameter was fixed to `t=−π q/(12 L²)` with `L=20` independent of the solved lapse. If that parameter is asserted to represent a **single closed 2D fermionic loop**, its total Killing-time optical circumference must satisfy:

```
L_loop = τ_inside + τ_exterior_return,
τ_inside = 2 ∫_throat^matching dx / N(x),
τ_exterior_return >= 0.
```

The committed baseline `scripts/check_mmp_global_effective_bvp_replay_20261024.py` at L=20 yields:

| q | τ_inside | available L−τ_inside | conditional loop result |
|---:|---:|---:|---|
| 10 | 17.110915 | +2.889085 | nonnegative exterior optical budget |
| 11 | 18.966874 | +1.033126 | nonnegative exterior optical budget |
| 12 | 20.810488 | −0.810488 | **impossible** for that L and closed-loop interpretation |
| 13 | 22.640312 | −2.640312 | **impossible** |
| 24 | 41.643438 | −21.643438 | **impossible** |

A positive budget is necessary, not sufficient: external spatial geometry, spin/EM holonomy, state and backreaction still missing.

**New scoped loop-length fixed point:** with q=12 and a **hypothetically specified** exterior optical return time `τ_exterior=2`, solve the effective Einstein BVP and `L=τ_inside(L)+2` jointly. Numeric root `L=22.516301125725`, interior optical time `20.516301125718`, effective RN junction radius `12.79381947`, RN mass `5.99725136`, K jump ~`2.24e-13`, effective radial ANEC ~`−0.00036310`. This is a solved **single global optical NORMALIZATION constraint** for the assumed reduced source, not a solved exterior fermion quantum field or full 4D Einstein-Dirac system. The external return is prescribed, and the effective quantum stress is still cut off at RN.

Executable: `scripts/check_mmp_closed_loop_optical_fixedpoint_20261024.py` imports committed BVP replay and checks all 5 budget values plus the q12 conditional root. Local equivalent replay passed.

## 3. Explicit static noncompact-line no-go at exactly scoped strength

On a globally noncompact optical line, a stationary conserved 2D *massless conformal Dirac state* has constant chiral state integration constants `t_uu,t_vv`; imposing flat vacuum asymptotics on both ends forces them to zero. A constant negative NS-circle t cannot extend to infinity as the same asymptotically vacuum static state. Introducing t=t(x) with otherwise unchanged Polyakov formula causes a radial Ward defect `2t'(x)/N²`; it requires actual additional stress, flux or a different nonlocal quantum state.

For t=0 and smooth asymptotically constant positive N with `F/N→0`, the **2D** integrated null combination is
```
∫ dx (rho_2+p_2)/N
 = c/(12π) ∫ dx F²/N >= 0.
```
This is a statement about the **2D conformal vacuum and these asymptotics**, NOT a general 4D ANEC theorem and NOT a no-go for the MMP closed circle. Explicit symbolic / numerical proof fixture: `scripts/check_noncompact_static_dirac_state_nogo_20261024.py`.

## 4. What 'complete global Einstein–Maxwell–Dirac' now requires

1. **P0 / topology and loop:** construct an actual same-universe two-mouth handle, magnetic flux / field lines and their return, spin-c patches, holonomy and asymptotic metric. Explicitly compute `ell[N,A]`, not a supplied L or an invented disk/three-ball correspondence.
2. **P1 / full QFT:** 4D globally Hadamard charged Dirac two-point function (or equivalent covariant in-in generating functional) with spherical spin connection, nonzero Landau tower, renormalized finite local counterterms and state-dependent nonlocal correlations along the actual field line. Derive all `<T^Dirac_{μν}>_ren`, `<J^μ>`, transverse pressure, curvature trace, Hall/Euler and dynamic Schwinger/polarization from that SAME state; prove all coupled Ward identities and regulator independence under a declared scheme.
3. **P2 / physical saddle:** solve Einstein `G=8πG (T_EM+<T_Dirac>_ren)`, Maxwell `∇F=J`, global Dirac state and geometry simultaneously on the handle; include external field-line stress/forces rather than pressure-zero quantum shutoff. Demonstrate converged physical constraints, no unaccounted shell/horizon, appropriate global time/causal conditions and measured or bounded stability.
4. **P3 / physical traversal:** null/fermion/photon transfer and injected-probe backreaction, quantum inequalities and strong stability, not just scalar toy `ξ=1/2`.
5. **P4 / three localized driven plasma regions:** actual Maxwell–MHD material sources + boundary/spin-Wilson phase response `δα`, helicity/ABJ and in-in `δ<T_kk>`. A balanced C3 phase rotation has zero volume-integrated helicity pump in existing models. A *holonomy phase*, if actually generated, can FLIP the sign of the circle Casimir energy, so measure/source-check α explicitly. Mere local A5/horn geometry or 12/24 numerology does not identify this U1 Wilson loop.

**Hard-stop evidence boundary:** a zeta-renormalized **2D** global conformal ground state is now computed from one functional; an asymptotically two-ended 4D source-free RN patch was already constructed as a mathematical effective-matter model; the composition is NOT a full 4D quantum-state same-object derivation. MMP itself supplies an approximate sourced wormhole construction and retains original authorship. No working three-plasma gravitational device or experimentally reproducible effect is established.

## Acceptance

```sh
python3 scripts/check_global_dirac_optical_circle_source_20261024.py
python3 scripts/check_mmp_closed_loop_optical_fixedpoint_20261024.py
python3 scripts/check_noncompact_static_dirac_state_nogo_20261024.py
```

All three corresponding LOCAL scripts were executed with PASS on 2026-10-24. GitHub exact-head workflow receipts, Agda/Lean kernel certification, full curved 4D renormalization, and empirical physical evidence are NOT claimed.
