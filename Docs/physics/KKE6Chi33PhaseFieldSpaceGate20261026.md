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
