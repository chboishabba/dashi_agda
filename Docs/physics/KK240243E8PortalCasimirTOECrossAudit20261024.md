# 240/243, TOE Lean, Higgs portals and Casimir: physically typed max-cut
2026-10-24 — canonical KK PR #1241.

## Original sources, repository donors and verification grades

**Mathematical prior art:** E₈ has 240 norm-two roots (112 of form ±e_i±e_j and 128 half-integer roots of even minus parity). The E₈ root graph with adjacency at inner product 1 is 56-regular. The genuine classical ideal-plate Casimir force is -π² ℏc/(240d⁴) per unit area, obtained by differentiating E/A=-π²ℏc/(720d³) (Casimir 1948; Brown and Maclay *Phys. Rev.* 184 (1969), 1272–1279, DOI 10.1103/PhysRev.184.1272). These are separate mathematics/physics; the numerical 240 does not imply a common operator.

**Ternary source owner:** [Agda PR #1094](https://github.com/chboishabba/dashi_agda/pull/1094), `DASHI/Reasoning/T5E8RelativeComplementCandidateExact.agda`, exact `T9 ↔ T4 × Kernel5`, `|Kernel5|=243=3^5`; three diagonal ternary states `(t,t,t,t,t)` and remaining non-diagonal carrier. Its owning source does NOT identify the remaining 240 states with E₈ roots: it requires a two-sided root correspondence and action-intertwining proof. The arithmetic is a DASHI construction, not an existing E₈ root system embedding.

**Ideal Casimir source owner:** [Agda PR #701](https://github.com/chboishabba/dashi_agda/pull/701), `CasimirParallelPlateKernel`, `CasimirCoefficient720To240CompilerExact`, `Casimir720FactorisationBidiExact`, `CasimirCanonicalEndgameStatusExact`. Its 720→240 arithmetic is correct but requires the source-specific electromagnetic mode carrier, transverse radial measure, matched regulator/cutoff and zeta defect transformation to establish the actual *plate* observable. It is not a 5D S1 gluon/quark fermion determinant. #701 retains four producer families open.

**Physical KK source owner:** [Agda PR #1241](https://github.com/chboishabba/dashi_agda/pull/1241), `scripts/check_kk_qed_qcd_casimir_budget.py`, for a specific free periodic S1 spectrum with massless SU(3) vectors (8×3=24 bosonic units) and six vectorlike colour-triplet Dirac fields (6×3×4=72 fermionic units). Their net +48 Casimir units give the *approximately* -240 dimensionless stationarity residual at the declared b0=10^-24 m. The -240 arises from `-5 × (72-24)`, an exponent/degree-of-freedom derivative **not** a Casimir-plate 240 denominator or E₈ root count.

**Dark-sector actual portal:** existing `DASHI/Physics/DarkSector/{GaugeSingletPortal,HiggsPortalDecay,LinkedColliderChainExact}.agda`. `GaugeSingletPortal` proves an interaction can be gauge singlet, NOT that it supplies a coupling, mass, condensation, renormalised determinant or physical collider branching fraction. Original scalar Higgs-portal literature: Silveira and Zee (1985); Patt and Wilczek (2006, arXiv:hep-ph/0605188), with a scalar singlet interaction `lambda_HS H†H S²/2`. In the explicitly *uncondensed, fixed-mass* free S1 scalar candidate below, no portal interaction is automatically a vacuum-stabilisation theorem.

**Recent purported 'portal / Casimir' result:** [Agda PR #1248](https://github.com/chboishabba/dashi_agda/pull/1248) is a Maldacena–Milekhin–Popov **wormhole / charged-Dirac optical-circle Casimir** research branch, not a Higgs portal to bulk QCD or a 5D Earth compactification. Its functional `E_2D ∝ B₂(alpha)/ell` and global returning magnetic field-line topology differ from the 5D free-field compact S1 vacuum `V_J ∝ 1/b⁴`. Reusing its **same-functional metric/holonomy variation discipline** is productive, but importing its negative-energy solution to the KK matter spectrum would be unlicensed. Original MMP research: arXiv:1807.04726, *Classical Quantum Gravity* 40 (2023) 155016, DOI 10.1088/1361-6382/acde30.

**TOE Lean:** [Lean PR #80](https://github.com/chboishabba/dashi_lean4/pull/80) already owns `Integration/DASHITOE/{PrimitiveMaxCut,Verticals,Everything}.lean` and correctly marks common selected metric/stress and calibrated physical realisation unpaid. [Lean PR #84](https://github.com/chboishabba/dashi_lean4/pull/84) owns the cross-prover operator/provenance atlas. New `Integration/DASHITOE/KK240RoleDiscrimination.lean` in #80 proves an *exact typed* same-number non-descent and the scoped arithmetic without claiming the sibling Agda sources are locally kernel-compiled Lean theorems. Agda #1241 adds an analogous canonical `ClaimNonTransportWitness`.

## New actual E₈ vs T5 adjacency discriminator

Executable `scripts/check_kk_240_243_e8_portal_casimir_bidi.py` exhaustively enumerates all 3^5=243 ternary five-tuples, removes the three diagonal states, and enumerates the actual 240 E₈ norm-two roots using integer doubled coordinates.

| Selected 240-element object | Selected native adjacency | Degree multiset |
| --- | --- | --- |
| non-diagonal ternary `P3^5` induced subgraph | coordinate nearest-neighbour path edges | 5:40, 6:70, 7:80, 8:50 |
| non-diagonal ternary `C3^5` induced subgraph | periodic single-coordinate shift | 9:30, 10:210 |
| classical E₈ root system | inner product +1 (with roots squared norm 2) | 56:240 |

Therefore **neither natural ternary adjacency is isomorphic to the standard E₈ root adjacency**. This is a valid *specific operator consumer* non-descent witness, stronger than number equality; it does NOT rule out alternative bijections, nontrivial E₈ actions, new graph connections or physical realizations. In particular, a 240-element set can always be placed in arbitrary bijection with the roots, but the original physical geometry is not thereby transported.

The 5D field counting remains separate: E₈ gauge theory in an unbroken 5D bulk would have an **adjoint of dimension 248 = 240 roots + 8 Cartan** and, for massless 5D vectors, three polarizations each (744 bosonic free Casimir units), not '240 E₈ root scalar fields'. No such E₈ sector has been physically attached to the selected 5D KK+QCD action.

## New portal lower bound: original physical QCD consumer

Let `U(x)=ell/x+W(x)/x^6`. 4D zero energy and stationary radius at x=1 require `D = W'(1)-5W(1)=0`, independently of `ell`. Previous QED+QCD selected fixed-radius computation gives `D≈-239.99999999978987694`.

For ONE uncondensed periodic free 5D *real* scalar with a nonnegative, radius-independent mass m_eff (which may be defined from a **fixed background** Higgs vev in a candidate Higgs-portal action), its one-loop contribution is `-f(zx)/x^6`, z=2π m_eff b0. Therefore its stationarity contribution is

`ΔD_scalar = 5 f(z)-z f'(z) = 5 h(z)`, `h(z)=f(z)-z f'(z)/5`.

The SAME source-dependent periodic Casimir kernel obeys
`h(0)=1, h(z)>0` and
`h'(z)= -z/[15ζ(5)] ∑_{n≥1} exp(-nz)[3+3nz+(nz)^2]/n³ <0`
for z>0. Hence `0<ΔD_scalar<=5` for ANY such nonnegative real scalar mass. It cannot cancel an approximately 240-unit negative residual. A complex scalar is two real polarizations and contributes at most 10, still insufficient. Even four additional scalar bosonic degrees at most 20.

With *only* such additive free real bosonic degrees and the same b0, quarks, gluons and trivial holonomies, **at least 48 real scalar units** are necessary. A formal compensating example with 48 degenerate real scalars yields one tuned common mass **86.3077058935 GeV** and gives D=0. This has NO demonstrated origin, coupling, phenomenological viability or radion/Wilson Hessian; it is not a discovery of 48 particles. The 48 bound is a *restricted additive repair class*, not a model-independent theorem.

**If the Higgs vacuum expectation value, scalar effective mass or boundary data depends on b**, the total derivative adds terms involving dm/db and d(Higgs vev)/db. If the portal scalar condenses, there are mixed Hessians and gauge/electroweak symmetry-breakdown obligations. Those are new actions/consumers and NOT excluded by the fixed-mass scalar inequality. Correct next treatment is to derive them from the same 5D action and quantum determinant.

## Source-graded BIDI verdict

1. **C_243 arithmetic**: true, already owned in #1094.
2. **C_E8 root adjacency**: new selected source graph comparison disproves two naive ternary-graph identifications; an alternative action-equivariant realisation remains open.
3. **C_ideal-plate 720→240**: correctly organised in #701; does not answer 5D QCD Casimir pressure.
4. **C_Higgs singlet portal permission**: existing dark-sector source permits interactions, not physical scalar mass or quantum potential.
5. **C_5D QED+QCD stationary vacuum**: fails for the prior bare spectrum; one minimal real/complex Higgs-portal compensator cannot repair it in the declared free fixed-mass class.
6. **C_fermionic wormhole Casimir**: PR #1248 owns a different global optical loop/renormalized quantum-state consumer, not a KK radius source.
7. **C_TOE physical action**: Lean #80 and Agda #1217 continue to require SAME selected action/stress, common metric variation, original experimental sources and held-out tests. Zero numerical role crossings are promoted.

## Executed verification / files

This tranche:
- `scripts/check_kk_240_243_e8_portal_casimir_bidi.py` — locally executed equivalent full integer root enumeration and high-precision massive scalar/portal residual tests, PASS; exact committed blob not byte-replayed.
- `DASHI/Physics/Gravity/KK240243PortalCasimirConsumerBIDIExact.agda` — source-written original source-role discrimination with canonical DASHI claim transport, NOT current-head Agda kernel checked.
- [Lean PR #80] `Integration/DASHITOE/KK240RoleDiscrimination.lean` — source-written Lean analogue, NOT current-head Lean/Lake checked.
- Both repository roadmaps updated with exact PR attribution and physically scoped failure conditions.

**Highest-alpha next:** physical source-select the *full* QED+QCD+chiral-EW one-loop 5D action, derive the Higgs/portal background and radion-dependent masses as ONE field theory, then check energy, 5D pressure and both Wilson/Higgs/radion Hessians against existing collider/QCD/stability constraints. A lower-priority alternative is upgrading the ternary-to-E₈ candidate only for a declared representation/operator consumer; its 240 count is not a substitute for the physical vacuum.


## Physically structured alternative: E₆ trinification, not bare 240 numerology

The standard exceptional-group branching (Slansky, *Group theory for unified model building*, *Physics Reports* **79** (1981), 1–128, DOI **10.1016/0370-1573(81)90092-2**, Table of E₈ maximal subgroups and E₆ ⊃ SU₃³) yields

`E8 adjoint 248 -> (78,1)+(1,8)+(27,3)+(27bar,3bar)`, hence `248=78+8+81+81` and the **SU₃-adjoint complement** has dimension `240=248-8`. The separate E₆ trinification restriction contains

`E6 adjoint 78 -> (8,1,1)+(1,8,1)+(1,1,8)+(3,3,3)+(3bar,3bar,3bar)`,

i.e. `78=24+54`. These are bona fide **representation-theoretic decompositions**, stronger than the unrelated number 240.

Choose one SU₃ factor as colour and hypothetically keep the other two SU₃ vector octets in a free periodic 5D ultraviolet spectrum. They supply `2*8=16` additional spin-1 vectors with `16*3=48` 5D massless bosonic polarizations. Existing six colour-triplet 5D vectorlike Dirac quarks have `6*3*4=72` fermion units. With THREE total SU₃ vector octets, `3*8*3=72` bosonic units, so the **leading massless free-Casimir coefficient balances**. In the previous *nonzero quark-mass* selected fixed-radius model, `D_QCD+240≈+2.10123e-10`, so exact stationarity still needs a small mass-dependent correction or model/radius revision. Treating all sixteen new vectors as 48 degenerate bosonic free polarization modes, the same source-mass equation would require `m_vector≈86.3077 GeV` at b0=10^-24 m. This is only **a mathematical compensator solution**, not a viable physical E₆/trinification vacuum: realistic gauge mass generation, charged current couplings, precision EW, collider limits, proton physics, symmetry breaking, anomaly cancellation, full E₆/E₈ coset towers and interactions have NOT been supplied.

In particular, merely declaring all 248 E₈ adjoint gauge bosons massless would contribute 744 5D vector polarization units, **not 240**; that model overcompensates the selected QCD residual. The natural E₈ 240-root graph (degree56) still cannot be equated with the natural 240 non-diagonal ternary graph (degrees5–8/9–10). The physically useful bridge is a specified gauge-representation decomposition and constrained mass spectrum, NOT a cardinal identification.

The old single gauge-singlet scalar Higgs portal contributes at most 5 free stationary units and cannot do this alone. This makes **SU₃³ with carefully sourced symmetry breaking** a more structural, but much higher-risk, candidate for testing than adding 48 unrelated scalars. No experiment or phenomenological feasibility has been claimed for extra ∼86 GeV gauge bosons.

## Latest same-action correction: SU3^3 radial pass, electromagnetic Wilson failure

**THIS SECTION SUPERSEDES any preceding suggestion that a physical 86.31-GeV SU3 vector mass follows from the 48-unit calculation.** A 5D massless Yang–Mills vector has 3 physical polarizations; an ordinary 5D Higgsed/Proca massive vector has 4, so the naive replacement `-48 f(m_Vb)` has no actual broken-gauge determinant or source action. The ~86.3077GeV value in earlier lines is **ONLY a scalar-like effective mass used to tune 48 arbitrary bosonic units**, never a predicted physical SU3 vector mass.

Latest exact free one-loop case is [`scripts/check_kk_e6_trinification_joint_radion_wilson.py`](https://github.com/chboishabba/dashi_agda/blob/lares2-kk-observable-maxcut-20261023/scripts/check_kk_e6_trinification_joint_radion_wilson.py) and `Docs/physics/KKE6SU3TrinificationJointRadionWilsonSteelman20261024.md`: TWO extra entirely massless SU3 octets give the 48 units and permit retuned stationary **RADION** z=0.908156990770679, Uxx=+15.3940. However six quarks with correct charges drive Utheta-theta from +1.99587 to **−21.1890963678556**; the electromagnetic Wilson minimum at theta=0 is a SADDLE. Quark EM charges cannot be suppressed while claiming the same observed light-quark consumer.

An uncondensed SM-singlet Higgs-portal scalar (electric charge 0) has NO direct Wilson curvature at free one loop. At least 19 real unit-charge bosonic polarisations / 10 complex unit-charge scalar fields would be needed to repair the Wilson Hessian *alone*; they shift radion stress too, so there is no completed joint stable/observational model. This new stronger BIDI result controls the current Pareto roadmap.