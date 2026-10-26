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

The degree formula realizes every *even* Chern degree while keeping the nontrivial Z3 deck label fixed. Consequently, **the quotient Z3 lifting class does not determine Higgs-line triviality**: a concrete consumer-collision, not just a count coincidence. By pullback to spin `S2 x S2`, and trivially through a 5D interval, the forced-zero example is compatible with a parity-even bundle in the selected geometric setup. This is a topological field-domain obstruction to declaring the *unpatched phase-only* Chi33 counterterm a functional on **all** allowed boundary-H bundles. The source may instead restrict to nonzero-Higgs sectors, add patches/defects, or specify a UV completion; those options remain open. Do **not** conflate this result with showing the fermion determinant is anomalous or all GS mechanisms fail.

**Verification**: exact-rational independent Python enumeration for 125 representative triples (`kc,kL,kR=-2..2`) PASS; source extension committed to the *preexisting* S2 clutching script. Agda gains only a typed consumer non-descent of two externally specified finite witnesses: it does **not** construct principal bundles, prove line-bundle clutching classification in its kernel, or establish quantum anomaly cancellation. No Agda executable/typecheck verified.

**Original-root sourcing**: the bundle clutching/line-bundle-Chern-class mathematics is classical topology (e.g., Hatcher, *Vector Bundles & K-Theory*, Prop. 1.11; and general complex line-bundle c1 classification). The original 5D localized-anomaly questions are Scrucca, Serone, Silvestrini & Zwirner (2002), DOI 10.1016/S0370-2693(01)01430-7; and von Gersdorff & Quirós (2003), DOI 10.1103/PhysRevD.68.105002. These authors did **not** establish the present source-selected Chi33 winding formula; it is a repository-specific consequence of the original first-Tits 27 action in #1106 and the physical orbifold parity and quotient choices of #1241. Hosotani (2026), DOI 10.1103/ds9g-5m21, is an independent *model-specific* full-KK anomaly-flow donor, not a same-object E6 regulator.

**Updated Pareto/Ibrahim frontier**: before another formal finite analogue, choose and explicitly model either (A) the full unconstrained scalar quantum configuration space with patch/defect/UV extension across forced Chi33 zeros, or (B) a justified restricted Higgs-reduced field domain, paying for its exclusions and topological superselection. Independently derive normalised characteristic periods, APS/eta and fermion descent for the faithful boundary-H quotient, not merely its bulk G cover. The same-action KK spectrum, interval scalar Hessian, photon and radion/Casimir stress are downstream, and retain existing owners.

## Attribution/revisability rules
- Original authors and dated source roots retain priority for each original theorem or experimental claim. Reprints/preprints of one paper count as one root, not corroboration; separate papers sharing a method are not necessarily independent confirmation of this specific result.
- The author-repo source-derived 27/parity/CS/WZ calculations remain owned by #1106/#1241, with new local analysis recorded separately as Johl Brown / OpenAI ChatGPT-assisted implementation. Agda source writing is not an Agda kernel proof; exact finite Python checks are not physical experiment.
- A counterexample to unpatched phase-only WZ on unrestricted configurations selectively invalidates that **ansatz** only. It does not disprove local anomaly factorisation, unique-photon Cartan rank, corrected interval Hessian, other counterterms, or orbifold gauge theories generally.
