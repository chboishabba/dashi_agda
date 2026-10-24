# Source D4 and Heisenberg: full symplectic obstruction and minimal repair

**Date** 2026-10-25 (Brisbane). **Owner** [IIT / jFine PR #1148](https://github.com/chboishabba/dashi_agda/pull/1148). **Consumer** [geometry/consciousness PR #1246](https://github.com/chboishabba/dashi_agda/pull/1246). This note augments, rather than replaces, `2026-10-25-iit-jfine-4-1-4-s3-zeta-mixed-characters.md`.

## Original owners and attribution

- `DASHI/Biology/TernaryMonsterSymmetryCandidateExact.agda`: earlier raw nine-cell D4 permutation decomposition **3A1 + B1 + B2 + 2E**.
- `DASHI/Biology/D4NineCellOrbitCompressionExact.agda`: original D4 cell action, three site orbits and quotient/residual codec; distinct from five irrep species.
- `DASHI/Biology/IITJFineFourOneFourS3ZetaGaugeExact.agda`: PR #1148 literal 4+1+4 shell and balanced value-C3/S3 operators.
- `DASHI/Biology/IITJFineD4EquivariantHeisenbergGaugeExact.agda`: PR #1148 site-D4 equivariant chart and relative coordinates; *linear chart*, not a Heisenberg automorphism theorem.
- `DASHI/Biology/IITJFineHeisenbergFourPairSubgroupExact.agda`: PR #1148 selected `H4` multiplication, model `H6` coordinate embedding and source-specific negative witnesses.
- `DASHI/Moonshine/Monster3BFiniteHeisenbergCentralExtensionExact.agda` and `scripts/check_monster_3b_heisenberg_model.py`: prior six-pair model and Weyl evidence; **not** a literal source-JFine/Monster normalizer intertwiner.

Mathematical background for the finite-group decomposition: J.-P. Serre, *Linear Representations of Finite Groups* (1977); D4 character exercise https://www.maths.tcd.ie/~lebed/HW2.pdf. The actual obstruction and explicit repair below are new calculations from these pre-existing site actions, not results attributed to those texts.

## No-go for **every** possible H4 commutator compatible with the source D4

Set `V8=F3^{edge4} ⊕ F3^{corner4}`. Remove the centre's trivial D4 coordinate from the earlier nine-site decomposition:

```
V8 = 2 A1 + B1 + B2 + 2 E
quarter-turn r: order 4
vertical mirror m: order 2; m r m = r^{-1}
```

A Heisenberg central extension of exponent three with quotient `V8` needs a **nondegenerate alternating** form `ω`. If source D4 acts by group automorphisms it must obey `ω(gv,gw)=χ(g)ω(v,w)`, where `χ:D4→F3^×={±1}` is the induced action on its one-dimensional centre.

Over characteristic three, `3∤|D4|=8` so the representation is semisimple. For `χ=1`, each one-dimensional D4 character must occur with **even multiplicity** to admit an invariant alternating pairing: the unique B1 and unique B2 sectors fail this condition. For `χ≠1`, multiplicity of each character λ must equal that of `χλ` in a nondegenerate χ-valued form; the two A1 versus 0/1 occurrences of the other one-dimensional characters contradict that requirement. Thus **no compatible full-rank alternating form exists for any of the four χ**.

The independent `scripts/iit_jfine_d4_symplectic_obstruction_audit.py` converts exactly the source edge/corner site permutations into 8×8 F3 matrices, solves all 28-coefficient linear alternating-form invariance equations via F3 Gaussian elimination and **enumerates every solution**:

| χ(r),χ(m) | form-space dimension | total forms | ranks: multiplicities | max rank |
|---|---:|---:|---|---:|
| +,+ | 2 | 9 | 0:1, 2:2, 4:2, 6:4 | **6** |
| +,- | 4 | 81 | 0:1, 2:10, 4:34, 6:36 | **6** |
| -,+ | 3 | 27 | 0:1, 2:8, 4:2, 6:16 | **6** |
| -,- | 3 | 27 | 0:1, 2:8, 4:2, 6:16 | **6** |

This strengthens the earlier `mirror does not preserve chosen dot cocycle` counterexample: **no alternate nondegenerate cocycle rescues the source eight-trit D4 action**, even with a sign inversion allowed on the centre. This no-go is restricted to the same source D4 *linear quotient action*, with one-dimensional central multiplier. It does not assert that D4 cannot act on any other eight-dimensional module or on a different Monster representation.

## Explicit **minimal** D4-compatible H5 repair and H6-sized completion

Use these equivariant F3 coordinates of the source edge (N,E,S,W) and corner (NW,NE,SW,SE) shells:

```
tE = N+E+S+W,       bE = N-E+S-W
XE = N-S,            YE = E-W
tC = NW+NE+SW+SE,   bC = NW-NE-SW+SE
XC = NW+NE-SW-SE,   YC = -NW+NE-SW+SE
```

The source action becomes `2 A1 + B1 + B2 + 2 E`, with `r(bE)=-bE, m(bE)=bE` and `r(bC)=-bC, m(bC)=-bC`. Both E pairs transform by `r:(x,y)→(-y,x)`, `m:(x,y)→(x,-y)`.

Adjoin one auxiliary B1 coordinate `bE'` and one auxiliary B2 coordinate `bC'`. On the ten coordinates define

```
ω10 = tE ∧ tC + bE ∧ bE' + bC ∧ bC'
     + XE ∧ XC + YE ∧ YC .
```

Here `x ∧ y` means the alternating 2-form on these named coordinate axes. The script constructs the explicit 10×8 source injection, proves by exact F3 matrices that it intertwines *both* D4 generators, and checks `rank(ω10)=10` and `gᵀω10g=ω10` for r and m. The original eight-dimensional D4 subspace restricts to **rank six**, with radical precisely the two unmatched B1 and B2 directions.

The two new coordinates are **minimal** for this source D4 action: no 0- or 1-coordinate extension can make the resulting ten-dimensional-style invariant form symplectic, as the parity/matching of B1 and B2 requires two corrections. The resulting *different* H5 model has quotient dimension ten and nontrivial complex Schrödinger degree **3^5=243**. A further trivial symplectic pair yields a nondegenerate 12-dimensional model with D4 action and the same *symplectic dimension* as the earlier `H6` owner; `rank(ω12)=12`.

**Crucial non-promotion:** the original *chosen H4* can embed into H6 with a chosen non-equivariant pairing (previous PR), but the repaired **D4-invariant source shell is degenerate**. It is therefore *not* a D4-stable embedded H4. The repaired H6 form is abstractly standard symplectic, but no explicit intertwiner into the original six-pair coordinates, let alone the actual Monster normalizer or its `W`, has been constructed in Agda.

## S3 / ζ / ζ²: anti-automorphism rather than automorphism

In the chosen first-four-pair H4 coordinates `(a,c,b)`, the source group law is

```
(a,c,b) (a',c',b') = (a+a', c+c'+b·a', b+b').
```

Source global value rotation `c→c+1` acts by *central left multiplication* (not a group automorphism). Source global sign `(a,c,b)→(-a,-c,-b)` cannot be a group automorphism for **any** nonzero alternating commutator: `ω(-v,-w)=ω(v,w)`, whereas it maps the centre by `-1`.

There is an exact **quadratically corrected anti-automorphism** of the *chosen group law*:

```
A(a,c,b)=(-a, -c+a·b, -b)
A(x y)=A(y) A(x),    A²=id.
```

It is not the source S3 reflection, which lacks the `a·b` correction. With symmetrised centre `t=c+a·b`, the map is simply `(t,v)→(-t,-v)`. The local audit checked all **19683** H4 states against the nine natural generators (**177147** generator-state anti-law checks), plus involutivity for every state; the anti-law also follows algebraically from bilinearity. This clarifies the mathematical provenance of phase-conjugation analogies without identifying the physical/Monster ζ and ζ² eigenspaces.

## Acceptance, phases and priorities

1. **Finite calculation**: independent local F3 exact arithmetic confirms the four full solution-space histograms, rank-10 repair, rank-6 source restriction, rank-12 completion and 177147 anti-involution generator checks. The committed script is integrated into `scripts/iit_numeric_verification.py`.
2. **Formal kernel work OPEN**: extract the source 8×8 matrices as Agda finite-linear maps, formalise the **universal all-four-character rank≤6 theorem**, construct the concrete rank-10 and rank-12 forms, prove D4-equivariance and the corrected H4 anti-law. Existing Agda D4 chart and Monster H6 owners must be reused. No fresh exact-head Agda compiler receipt is asserted.
3. **Same-object Monster gate OPEN**: derive a certified symplectic basis-change into the existing H6 MODEL, and *separately* establish an actual 3B-normalizer action/character intertwiner from original Monster source data. Arithmetic `65610=90×729=810×81` is not this intertwiner.
4. **Physical consumer gate OPEN**: only after specified instrumentation/measurement of neural, optical, causal or quantum systems could a model be interpreted empirically; no consciousness, magnetism, or quantum-ζ effect follows from finite-character coincidences.

The main high-leverage discovery is **an actual incompatibility plus an explicit minimal repair**, rather than another numerological identification. The correct physical-interpretation boundary has not moved.

## Cross-lane correction: PR #1250 already has a different D4/H6 action

The adjacent owner [JFine 3B action-first PR #1250](https://github.com/chboishabba/dashi_agda/pull/1250) must **not** be mistaken for a counterexample to the rank-eight result. In `scripts/jfine_3b_d4_equivariant_chart.py`, a D4-stable **two-label × six-fibre rechart** gives a D4 action on the *chosen 12D Heisenberg quotient* by simultaneously permuting **six translation and six modulation** axes. That representation differs from the natural eight-relative-site D4 quotient in this audit. Its symplectic pairing can be nondegenerate and D4-invariant because it includes both each six-coordinate module and its dual.

The same PR's `reflect_heisenberg(a,b,t)=(-a,b,-t)` is a legitimate centre-inverting **automorphism** of the chosen H6 action: it is anti-symplectic on the quotient (multiplier -1). This does **not** equal the source H4 value-sign action `(a,c,b)→(-a,-c,-b)`, which acts by -I on *both* quotient blocks and is symplectic (multiplier +1). The source H4 sign is not an automorphism; the quadratic correction supplies an **anti**-automorphism. No contradiction exists once the actions, centres and charts remain separately typed.

More importantly, #1250's later source-aligned Monster character audit reportedly **rules out its original chosen geometric D4** on the actual 3B phase sector via published involution/order-six character values; it discusses a *distinct conditional signed-monomial 90-space repair* and the unresolved source-selected 6.Suz linear-character family. Our new 8→10→12 **finite symplectic repair does not repair that actual Monster character obstruction**, certify its signed 90-module, or identify the faithful 6.Suz 78-character. Keep the active discriminators independent:

- source eight-site D4-preserving Heisenberg extension: **NO**, all multipliers exhausted (this cut);
- finite D4-stable symplectic 10/12D completion: **YES**, chosen model (this cut);
- #1250 six-pair chosen geometric Heisenberg normalizer action: **YES at model level**, but **not the source eight-dimensional H4 action**;
- actual Monster 3B / 6.Suz source-selected D4/Hom character: **OPEN / source-dependent**, subject to #1250's separate no-go and more recent 6.Suz family qualification.

These are deliberately different proof objects. Use #1250's existing backend-free D4 character and actual-source screening producers rather than rebuilding or bypassing their authority checks.
