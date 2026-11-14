# 2026-10-24 MMP / Dirac / quantum-channel SOTA snowball and new source-first max-cut

**Primary owners:** draft Agda PR #1248, draft Lean `chboishabba/dashi_lean4` PR #85. This is a bounded *mathematical channel / provenance* improvement, **not** a construction of a 4D globally renormalized semiclassical charged-fermion wormhole or a real three-plasma gravitational device.

## Provenance ledger: distinguish original roots, descendants, and applicability

| Root / source, dated | Source-authored result | Applies to PR #1248 | Does **not** pay |
|---|---|---|---|
| Maldacena, Milekhin, Popov, [arXiv:1807.04726](https://arxiv.org/abs/1807.04726) (2018 preprint; CQG 40 155016, 2023, DOI 10.1088/1361-6382/acde30) | Four-dimensional magnetically charged fermionic Casimir wormhole, closed magnetic return paths | reference physical geometry/state/scale source | our independently sourced exact 4D global fixed point |
| Capoferri & Murro, *Mathematische Nachrichten* 298 (2025) 2942–2974, DOI [10.1002/mana.12032](https://doi.org/10.1002/mana.12032) | Geometric/global Dirac propagator and quasifree Hadamard Cauchy covariances, **Cauchy-compact globally hyperbolic 4-manifold** premise | P1 operator/microlocal construction donor | Hadamard source on unconstructed **noncompact one-universe magnetic-handle spacetime**; no wormhole Einstein saddle |
| Zahn, *Rev. Math. Phys.* 26 (2014) 1330012, DOI [10.1142/S0129055X13300124](https://doi.org/10.1142/S0129055X13300124) | Charged locally covariant Dirac Wick-renormalization, conserved current and stress, renormalization ambiguities | local counterterm/Ward acceptance donor | globally selected quasifree state, closed field lines, finite renormalized stress numerics |
| André Pereira Marques Trindade Miranda, *From renormalized stress-energy tensor to the effective action for Dirac fields in curved spacetime* (available online **22 Nov 2025**, published *Nucl. Phys. B* 1022, Jan 2026, 117220), DOI [10.1016/j.nuclphysb.2025.117220](https://doi.org/10.1016/j.nuclphysb.2025.117220) | One-loop point-splitting and heat-kernel counterterm methods with curvature, scalar, torsion | explicit local UV coefficient/counterterm check under its heat-kernel/Euclidean analytic-continuation assumptions | nonlocal state on selected Maxwell/handle background or a general Lorentzian Hadamard existence theorem |
| Freivogel, Fumagalli, Tomašević, [arXiv:2606.12528](https://arxiv.org/abs/2606.12528) (2026) | MMP probe-scattering paper: low-energy scalars show reflection/trapping/resonance; charged massless fermions transmit efficiently; Callan–Rubakov-like connection | independent *same physical family* scattering comparison | exact match to **our** artificially cut-off effective metric; finite 4D Dirac state |
| Sadhukhan [arXiv:2609.33511](https://arxiv.org/abs/2609.33511) (Sep 2026) | MMP linear polar-metric/axial-gauge response; trace anomaly + Hall/Wen–Zee-like correction for first-order conservation | P1/P3 perturbative Ward/currents/stability check | full nonlinear/backreacted state, l=0/1 all modes |
| Kanai, Maeda, Yoshida, *PRD* 113 (2026) 064026, DOI [10.1103/dsnv-gq47](https://doi.org/10.1103/dsnv-gq47) | Restricted higher-derivative perturbative EFT no-go near RN/Myers–Perry, with Casimir as separate needed ingredient | P2 negative control for fake "higher-derivative solution" | no-go for nonperturbative sourced Casimir MMP state |
| Gao–Jafferis–Wall (JHEP 2017 151) and Maldacena–Stanford–Yang (2017) | Holographic traversability/teleportation protocol in different models | protocol comparison | MMP physical 4D same-object equivalence |
| Lu, Yang, Zheng, arXiv [2603.26051](https://arxiv.org/abs/2603.26051) (Mar 2026), **PRD accepted 22 Oct 2026**, DOI [10.1103/7trm-rykk](https://doi.org/10.1103/7trm-rykk) | Quantum channel capacity of **GJW** protocol related to time-derivative OTOC/operator size, bounded by Einstein limit under their large-N/holographic setup | P3Q capacity/OTOC independent benchmark | MMP capacity formula or experiment |
| Bennett, DiVincenzo, Smolin, *PRL* 78 (21 Apr 1997) 3217, DOI [10.1103/PhysRevLett.78.3217](https://doi.org/10.1103/PhysRevLett.78.3217); Barnum, Smolin, Terhal *PRA* 58 (1998) 3496 | Quantum erasure-channel capacity Q=max(0,2T−1) for balanced qubit erasure, and capacity proof structure | exact formula for our **equal-loss finite subchannel only** | unbalanced channel full capacity, finite MMP physical rate |
| Negari & Salek, *PRL* 137 (18 Aug 2026) 080201, DOI [10.1103/65dd-448y](https://doi.org/10.1103/65dd-448y) | Fermionic Gaussian-state extendibility and antidegradable Gaussian-channel SDP; no nontrivial EB Gaussian channel (in their exact definition) | future covariance/extendibility/antidegradability comparison | direct identification with our **restricted charge-sector qutrit erasure output**; no actual spin-c QFT state |

**Bibliographic rule:** 2018 MMP preprint and 2023 journal paper are **one original source family**, not independent proofs. March 2026 Lu–Yang–Zheng preprint and October PRD accepted article are **one study**. Follow-up perturbation/scattering papers are descendants but their calculations are distinct. Do not attribute source theorem to DASHI or grant geometry through shared names "wormhole", "Majorana", "zero mode", "C3" or numerical equality.

## New mathematical cut 1 — source-specific fixed-charge two-rail physical operator

An integral magnetic spin-c flux index `q` on a round `S²` has exactly `|q|` lowest-Landau-level zero modes **under the standard spin-c Dirac hypotheses**. Therefore `|q|>=2` supplies two distinct selectable basis labels. This is the original Dirac/index-theory mathematics, *not* newly proved by the 2026 Python/Lean code. Actual two localized field-line mode wavefunctions, global spin-c connection, addressable sources/detectors, external environment and backreaction are separate obligations.

**Important q12/24 correction:** a two-rail *mathematical* code only requires two independent LLL zero modes, not a physically privileged q=12/24/Golay/SUSY interpretation. Semiclassical throat control may require much larger q for **different physical reasons**.

For the declared static reduced 1+1D massless LLL model `H=-iσx∂z`, each channel is exactly reflectionless and carries conserved Dirac current. Two selected same-charge LLL modes then give **ideal** independent transport `T1=T2=1` within this model; any physical 4D source deformation/connection may cause mixing, localization, pair creation, nonadiabatic effects, or attenuation. Do not infer measured quantum capacity 1 from this idealized limit.

**Lean draft #85** [`MMPMonopoleLLLDualRailCapacity.lean`](https://github.com/chboishabba/dashi_lean4/blob/research/mmp-dirac-majorana-fock-channel-bidi-20261024/QuantumChannels/MMPMonopoleLLLDualRailCapacity.lean) constructs two distinct `Fin q` indices for a *source-assumed* `q≥2`, and proves the equal-loss algebraic coherent-information threshold conditional on the standard erasure model. It does not prove the spin-c index or fermionic field equations.

## New mathematical cut 2 — one charged-fermion Stinespring with receiver/environment

Two orthogonal charged input rails `|1>,|2>` have **fixed total U1 charge +1**. For each rail `j` define the pure-loss isometry, with B=receiver, E=environment:

```
|j>_A -> sqrt(Tj) |j>_B |vac>_E
          + sqrt(1-Tj) |vac>_B |j>_E .
```

Every term has total fermion charge +1. This differs from Lean #37's even-parity `|00>,|11>` charged-sector coherence (which needs a reference/dressing), and avoids a parity-only false herald. The 3-dimensional receiver and environment bases are `vac,rail1,rail2`. The isometry, two complementary CPTP channels, Kraus positivity and true receiver/environment partial traces are explicitly checked in the locally executed Python.

For the **maximally mixed input** `ρ=I/2`, the eigenvalue lists are **derived from this same state**:

```
spec(ρ_B) = (1−(T1+T2)/2, T1/2, T2/2)
spec(ρ_E) = ((T1+T2)/2, (1−T1)/2, (1−T2)/2).
I_c(I/2,N) = H(spec ρ_B) − H(spec ρ_E)  bits.
```

This single-letter `I_c` is **not generally the fully optimized/regularized capacity** of the unequal-loss channel. It must not be promoted to a capacity claim by a numerical sign alone.

For **balanced** T1=T2=T, the channel is the qubit erasure channel with receiver survival T, and its complement is the same with survival 1−T:
```
I_c(I/2,N_T)=2T−1 bits,
Q(N_T)=max(0,2T−1) qubits/use  [external Bennett et al 1997 theorem].
```
A valid CPTP *degrading* map for `T≥1/2` erases an additional fraction `1−(1−T)/T` of surviving receiver states to simulate the environment. For `T≤1/2` an *antidegrading* map erases a fraction `1−T/(1−T)` of surviving environment states to simulate the receiver. Both were explicitly tested on a basis of five density states.

**Numerical results from executed local Python:**
| Fixed two-rail channel | Mean receiver success | I_c(maxmixed), bits |
|---|---:|---:|
| q12 E=.20 finite-RN *effective* massive n1,n2 | .499949871 | −.000682974 |
| q12 E=.55 finite-RN *effective* massive n1,n2 | .999999995 | .999999991 |
| balanced T=.2 | .2 | −.6 |
| balanced T=.5 | .5 | 0 |
| balanced T=.8 | .8 | +.6 |
| independently selected two ideal massless LLL rails | 1 | 1 |

A coherent-information lower bound can be negative; do not equate a negative single-input I_c with an actual negative channel capacity. Likewise near-unity **postselected conditional fidelity** at T=.2 does not imply a usable asymptotic quantum channel: full Q is zero for the balanced unassisted erasure case.

**Run**:
```sh
python3 scripts/check_mmp_dualrail_coherent_information_20261024.py
python3 scripts/check_mmp_dualrail_erasure_degradability_20261024.py
```
Both local independently equivalent scripts ran PASS (full Stinespring, receiver and environment, Choi, CPTP degradation maps, balanced threshold); GitHub exact-head executables and Lean kernel receipts still UNVERIFIED.

## Pareto phase recut and hard blockers

**P0**: GitHub exact-head numerical+Lean smoke receipts for two new source-bound channel scripts; reproduce S-matrix's finite-radius truncation/massive lead convergence and select q≥2 labels.

**P1 — fundamental physical blocker**: same-universe connected magnetic return geometry, global spin-c bundle/fermionic state and 4D covariant Hadamard renormalization. The Capoferri–Murro donor's Cauchy-compact premise does not automatically match our noncompact exterior; explicitly construct the relevant noncompact globally hyperbolic setting or use a more general theorem. Zahn's source controls local renormalization and Ward, not selected state. Must compute `<Tμν>_ren`, `<Jμ>`, trace, angular stress and current from ONE source with finite-counterterm conventions.

**P2**: real Einstein–Maxwell + fermionic source fixed point with **one global state**, no manually switching negative Casimir stress off at radial pressure zero. Test original MMP scale and closed return path rather than free model parameter L.

**P3Q**: now choose two **LLL** spin-c zero modes of equal charge if they exist as physically addressable asymptotic rails; compute full 4D retarded/advanced transfer, loss to antiparticle/angular/background modes, coherent information, Gaussian covariance/antidegradability where class assumptions hold, actual flux-normalized wavepackets, causal support and perturbative probe energy. Compare Freivogel et al. physical MMP scattering, Bennett erasure reference and **Lu et al. GJW OTOC** only as distinct-scope benchmarks.

**P4**: three independent physical Maxwell/MHD regions must produce sourced `δα`/holonomy, `δ<T>`, `δJ` and `δ channel` on the same 4D state. Existing three Gaussians/Beltrami/helicity toys satisfy Maxwell identities but do not source an actual plasma apparatus, nonbounding wormhole or negative null stress. Balanced C3 integrated E·B null remains a negative control.

**P6 optional**: horned non-Abelian holonomy, JMD/GF3/Golay 12/24, Monster, RT/Jacobson, supersymmetry only if a concrete same-operator physical transport theorem demonstrably reduces P1–P4.

**No new absolute quantum capacity or real wormhole was measured or proved.**
