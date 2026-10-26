# Chi33 phase-only WZ field-space gate (2026-10-26)

## Exact consumer and attribution
Original orbifold anomaly framework: Scrucca–Serone–Silvestrini–Zwirner (2002), von Gersdorff–Quirós (2003). Existing selected first-Tits 27 implementation: Agda #1106. Selected CS-to-one-boundary transfer, Chi33 charge-two local WZ candidate, photon-rank check: physical KK Agda #1241. Latest adjacent PR audit: Agda #1260 (3-adic finite carrier), #1261 (D4h same-action symmetry), #1266 (consumer-relative proof-search), Lean #52 (original-Q same-object classification), Lean #84 (carrier distinction). None supplies a physical 5D quantum anomaly certificate; do not promote or duplicate.

## Sharper phase-only functional obstruction
Let z=Chi33 be an *unconstrained* complex field value at a boundary point. A pure phase-only functional whose nontrivial characteristic-charge sector contributes exp(i n arg(z)), n a nonzero integer, has no continuous extension from C\\{0} to z=0. For rays z=r exp(i theta), r tends to zero, its limit exp(i n theta) depends on theta. Choose theta=0 and theta=pi/|n|: limits +1 and -1. This is independent of how closely one approaches zero. For n=0, extension exists. The exact script `scripts/check_kk_e6_chi33_phase_domain_gate.py` tests multiple signed integer sectors and approach radii.

The field-space obstruction is conditional: it applies to a **phase-only** action required to extend continuously over scalar configurations with Chi33=0 and a nonzero topological coupling. It does NOT prove the original full 5D source must include such configurations without defect completions; nor does it rule out a constrained fixed-modulus Higgs EFT, patched/differential cocycle definitions, heavy fermion UV completion, or another anomaly repair.

## Stronger max-cut
1. Define the actual quantum field domain. If Chi33 is constrained to be nowhere-zero, state and derive that constraint from the same 5D action (including thermal/quantum excitations, orbifold endpoints and non-liftable quotient bundles). A quartic minimum at |Chi33|>0 by itself does not remove zero-valued off-shell configurations from a standard scalar path integral.
2. If zeros are permitted, supply an explicit extension of exp(i S_WZ), with patches/defects or a source UV completion; otherwise *reject phase-only WZ as a global all-field action* even before quotient CS and eta are attempted.
3. Separately establish normalized G=(SU3^3)/Z3 characteristic class periods, allowed spin CS levels, large-gauge variation, fermion eta and full KK tower; the naive trace polynomial and endpoint cochain do not establish these.
4. Only then promote to radion, coupled odd/even fluctuations and same-action observables.

Proof status: elementary analytic argument; finite Python numerical regression; not Agda/Lean kernel verified, not physical anomaly cancellation. Preserve authors and dates of original literature rather than attributing their original claims to later scripts.


## 26 October same-source upgrade: parity-even nonliftable bundle with forced Chi33 zeros

**This is the strengthened max-cut**, reusing the already-present `scripts/check_kk_e6_orbifold_even_quotient_s2_clutch.py` and `DASHI/Physics/Gravity/KKE6TrinificationDiagonalZThreeQuotientExact.agda`; no new E6 model. The previous simple T2 clock/shift witness uses a shift not commuting with the fixed-plane parity and therefore is not, on its own, a boundary-H counterexample.

The actual parity-even boundary cover is
`H0=SU(3)c x S(U(2)xU(1))L x S(U(2)xU(1))R`,
with faithful `H=H0/Z3_diag`. For integers `kc,kL,kR`, set, on the S2 equator `s in [0,1]`,
`h_k(s)=diag(exp[2pi i(1/3+k)s], exp[2pi i(1/3+k)s], exp[-4pi i(1/3+k)s])`.
Each path lies in SU3 and commutes with `P=diag(-1,-1,+1)`. At `s=1` each endpoint is `omega I3`, independently of `k`. Thus `g(s)=[h_kc(s),h_kL(s),h_kR(s)]` is a **closed loop in the faithful quotient H** whose lift in the cover starts at identity and ends at the nontrivial diagonal-Z3 deck element. The associated S2 principal H bundle is nonliftable to H0. All integer triples have the *same* deck class, since the added torus turns lift to closed cover loops.

Crucially the C33 singlet in the same original first-Tits 27 block `(1,3L,bar3R)` transforms on the equator as
`g_Chi33(s)=h_kL(s)[3,3] / h_kR(s)[3,3]=exp[2pi i * 2(kR-kL)s]`.
This is an actual character of H (diagonal Z3 acts trivially). Hence the associated *complex line bundle* over S2 has
`c1(L_Chi33)[S2]=2(kR-kL)` (chosen equator orientation).

Two selected witnesses sharing **exactly the same quotient lift-obstruction**:
- `(kc,kL,kR)=(0,0,0)`: Chi33 line has degree zero. This *allows* a nowhere-zero section of this one line; it does not establish a simultaneous source Higgs vacuum.
- `(kc,kL,kR)=(0,1,0)`: Chi33 line has degree -2. Every continuous Chi33 section on S2 has a zero. No globally defined unpatched phase `arg Chi33` exists for that sector.

The equal-doublet-torus SUBFAMILY degree formula realizes every even Chern degree at fixed deck label; the full parity-even U2 torus allows independent doublet eigenline turns and every INTEGER degree, as derived below. Consequently, **the quotient Z3 lifting class does not determine Higgs-line triviality**: a concrete consumer-collision, not just a count coincidence. By pullback to spin `S2 x S2`, and trivially through a 5D interval, the forced-zero example is compatible with a parity-even bundle in the selected geometric setup. This is a topological field-domain obstruction to declaring the *unpatched phase-only* Chi33 counterterm a functional on **all** allowed boundary-H bundles. The source may instead restrict to nonzero-Higgs sectors, add patches/defects, or specify a UV completion; those options remain open. Do **not** conflate this result with showing the fermion determinant is anomalous or all GS mechanisms fail.

**Verification**: exact-rational independent Python enumeration for 125 representative triples (`kc,kL,kR=-2..2`) PASS; source extension committed to the *preexisting* S2 clutching script. Agda gains only a typed consumer non-descent of two externally specified finite witnesses: it does **not** construct principal bundles, prove line-bundle clutching classification in its kernel, or establish quantum anomaly cancellation. No Agda executable/typecheck verified.

**Original-root sourcing**: the bundle clutching/line-bundle-Chern-class mathematics is classical topology (e.g., Hatcher, *Vector Bundles & K-Theory*, Prop. 1.11; and general complex line-bundle c1 classification). The original 5D localized-anomaly questions are Scrucca, Serone, Silvestrini & Zwirner (2002), DOI 10.1016/S0370-2693(01)01430-7; and von Gersdorff & Quirós (2003), DOI 10.1103/PhysRevD.68.105002. These authors did **not** establish the present source-selected Chi33 winding formula; it is a repository-specific consequence of the original first-Tits 27 action in #1106 and the physical orbifold parity and quotient choices of #1241. Hosotani (2026), DOI 10.1103/ds9g-5m21, is an independent *model-specific* full-KK anomaly-flow donor, not a same-object E6 regulator.

**Updated Pareto/Ibrahim frontier**: before another formal finite analogue, choose and explicitly model either (A) the full unconstrained scalar quantum configuration space with patch/defect/UV extension across forced Chi33 zeros, or (B) a justified restricted Higgs-reduced field domain, paying for its exclusions and topological superselection. Independently derive normalised characteristic periods, APS/eta and fermion descent for the faithful boundary-H quotient, not merely its bulk G cover. The same-action KK spectrum, interval scalar Hessian, photon and radion/Casimir stress are downstream, and retain existing owners.

## Attribution/revisability rules
- Original authors and dated source roots retain priority for each original theorem or experimental claim. Reprints/preprints of one paper count as one root, not corroboration; separate papers sharing a method are not necessarily independent confirmation of this specific result.
- The author-repo source-derived 27/parity/CS/WZ calculations remain owned by #1106/#1241, with new local analysis recorded separately as Johl Brown / OpenAI ChatGPT-assisted implementation. Agda source writing is not an Agda kernel proof; exact finite Python checks are not physical experiment.
- A counterexample to unpatched phase-only WZ on unrestricted configurations selectively invalidates that **ansatz** only. It does not disprove local anomaly factorisation, unique-photon Cartan rank, corrected interval Hessian, other counterterms, or orbifold gauge theories generally.


## 26 October stronger max-cut: all integral C33 windings within ONE nonliftable Z3 class

The previous h_k(t), with both U(2) doublet entries constrained to the same integer turn k, was **a strict subfamily**. The boundary group contains the *full* U(2) doublet torus, not only its center. Let p=0,1,2 (the common quotient deck class) and m,n be arbitrary integers. Define
`h_(p,m,n)(t)=diag(exp(2πi(p/3+m)t), exp(2πi(p/3+n)t), exp(-2πi(2p/3+m+n)t))`.

This is SU3-valued, commutes with P=diag(-,-,+), begins at identity, and ends at omega^p I3. A triple of such paths with **one common p** gives a closed faithful-boundary H loop, nonliftable for p=1 or 2. It is essential that independent m,n are allowed by S(U2×U1). For the source 27 singlet C33=(3_L)_3 ⊗ (bar3_R)_3,
`chi33Transition(t)=exp(2πi [(mR+nR)-(mL+nL)] t)`.
Thus `c1(L_Chi33)[S2]=(mR+nR)-(mL+nL)` with the selected clutch orientation. Set mL=1 and the other winding integers zero to get c1=-1, or mR=1 to get +1, while leaving p=1 and the *same* nontrivial deck obstruction.

**Correction to earlier inference**: the charge-(+2,-2) Lie-algebra bookkeeping does NOT force even global C33 line degree on this faithful quotient. The earlier degree `2(kR-kL)` was precisely the equal-doublet subfamily m=n=k. The image of the global C33 character on the boundary torus clutch fundamental loops includes 1, i.e. has primitive winding. This is a *necessary global-normalisation warning*, not a complete resolution of the local-to-global WZ coefficient.

Receipt: the original `scripts/check_kk_e6_orbifold_even_quotient_s2_clutch.py` now checks 2,187 integer representatives with all three colour/L/R paths, plus constructive degree witnesses for every target integer from -7 to 7 at fixed p=1. The algebraic formula proves the arbitrary-integer family, not just the sampled finite range. Existing Agda quotient owner records a second BIDI witness: same deck class / different C33 winding parity. Neither script constructs quantum determinant phases.

## 26 October universal spin six-index parity: a larger paid gate

A separate source-derived theorem strengthens the earlier selected CP3 and S2×S4 spin-index checks.

**Theorem (classical index theorem applied to the selected source representation, not yet kernel formalised).** Let H=(SU3c×S(U2×U1)L×S(U2×U1)R)/Z3_diag be the parity-even orbifold boundary group and E27 the globally defined associated 27 bundle from the faithful trinification representation. Let s be the orbifold intrinsic-parity involution commuting with H, so E27=Eplus⊕Eminus as globally defined complex H-bundles. For every closed spin 6-manifold X carrying an H principal bundle,
`ind_X(D_Eplus)-ind_X(D_Eminus) ∈ 2Z`.
In particular the formal signed half-index is an integer for **all spin 6D H bundles**, including nonliftable quotient sectors. This is the free/Dirac-index parity condition, not an APS/eta/torsion statement.

**Proof.** On the Lie algebra su3c⊕su3L⊕su3R, with trace-zero curvatures F_c,F_L,F_R, the 27 has three blocks
`A=3c⊗bar3L`, `B=bar3c⊗3R`, `C=3L⊗bar3R`.
The first Chern character of their direct sum vanishes because the traces of each F vanish. For the cubic trace,
`tr_A(F^3)=3(tr F_c^3-tr F_L^3)`,
`tr_B(F^3)=3(tr F_R^3-tr F_c^3)`,
`tr_C(F^3)=3(tr F_L^3-tr F_R^3)`.
All mixed terms with `tr F_i` vanish. The sum is zero. Although the constituent rank-three cover bundles need not exist on nonliftable H bundles, the **total 27 does** and its Chern–Weil trace polynomials vanish identically on the entire H Lie algebra. Hence `ch1(E27)=ch3(E27)=0` in rational cohomology of every H bundle. The spin Atiyah–Singer formula on closed X is
`ind(D_E27)=∫_X (ch3(E27) - p1(TX) ch1(E27)/24)=0`.
Since the signed parity split is H-equivariant and indices are additive,
`ind(D_Eplus)-ind(D_Eminus)=2 ind(D_Eplus)-ind(D_E27)=2 ind(D_Eplus)`. QED, modulo application of these standard external theorems.

**Nontrivial nonliftable test**: `scripts/check_kk_e6_orbifold_index_even_universal_trace.py` computes all 27 source weight-line cubic products on the spin sixfold X=(S²)^3 with deck p=1 over *each sphere*. On a concrete common-deck flux it gives total 27 index 0, signed index -12, and signed half-index -6. Its symbolic unrestricted Cartan polynomial has 88 nonzero signed degree-three terms, all even coefficients, and zero full-27 degree-one/cubic traces. Local materially equivalent SymPy execution passed; the exact GitHub blob and Agda kernel were not executed here.

**Precisely what this pays**: the integer-valued half-INDEX condition on closed spin sixfolds for the chosen split representation, including quotient bundles; it replaces the weaker finite-index-family argument. It does NOT pay the actual half-level 5D CS functional, the globally nontrivial Higgs/WZ configuration-space extension, torsion in spin bordism, the APS/eta determinant phase on five-manifolds, additional physical bulk fermions, or quantum gauge invariance. Those requirements remain independent and **open**.

## New original-source root and Pareto stop rule

Original mathematical sources: Atiyah and Singer (spin Dirac index theorem); Hatcher, *Vector Bundles & K-Theory*, §1.2 (clutching construction and line-bundle classification), https://pi.math.cornell.edu/~Hatcher/VBKT/VBpage.html. Separate physics root: Kazuya Yonekura, *General anomaly matching by Goldstone bosons*, JHEP 03 (2021) 057, DOI **10.1007/JHEP03(2021)057**, globally formulates WZW terms through invertible theories. A further independent root: Hsieh, Tachikawa & Yonekura, *Anomaly inflow and p-form gauge theories*, Commun. Math. Phys. 391 (2022), DOI **10.1007/s00220-022-04333-w**, treats APS/eta/global anomaly issues. Neither is a proof of this particular quotient-model CS/WZ completion.

**Next Pareto cut / physical stop condition**: the *index/free-period component* is now paid at theorem level with explicitly stated classical inputs. The decisive wall is the global **five-dimensional exponentiated determinant/CS/WZ differential-cocycle and its extension across the forced C33-zero sectors** on actual H quotient bundles. Do NOT keep collecting equivalent positive spin-index samples or repackage this as a completed global-anomaly cancellation. If the source lacks a globally defined compensator, either construct a genuinely patched/defect-complete functional or change the source field content. Subsequent full KK spectral/vacuum/Einstein stress work is downstream of that physical model-selection gate.
