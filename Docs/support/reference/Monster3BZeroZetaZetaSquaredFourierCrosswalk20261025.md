> **25 OCTOBER 2026 — PRIMARY-SOURCE MAX-CUT CORRECTION (latest):** Barraclough–Wilson §5.1 permits *any* irreducible \(6.\mathrm{Suz}\) character as the inflated 729 tensor factor. Earlier faithful-78 **preselection** in the repository main-quotient GAP script was a local filter, NOT the Monster's proven selection. PR #1250 now scans **all** degree-78 outer families and requires the original full main-table split, exact MN3B descent, and positive occurrence in the restricted Monster character to select exactly one. The source-selected family's faithfulness and central C2 trace (either -90 or +66 for the 90-sector) are **OUTPUTS**, not preconditions. Nebe's Sym²78 and faithful78 remain different 6.Suz representations when their central C2 actions differ. Any earlier claim that the Monster *already selects* faithful78 is superseded. See [actual 6.Suz source-family ledger](./Monster3B6SuzExistingSourceFamilyMaxCut20261025.md). The matcher and its revised validator are source-written; no GAP/Agda execution receipt is available in this turn.\n\n> **25 October 2026 — source-family correction:** the existing full Monster-to-6.Suz quotient matcher selects *faithful* degree-78 characters, while Nebe's Sym²(faithful12)=78 descends to 3.Suz and is nonfaithful to 6.Suz. Matching C3 phases or norm8100 cannot identify these two families: their degree90 central C2 traces are -90 and +66, respectively. See [the source-family max-cut audit](./Monster3B6SuzExistingSourceFamilyMaxCut20261025.md). The actual selected Monster pair requires the unexecuted GAP quotient receipt; earlier geometric/Sym² predictions are separate conditional constructions.

# Zero / ζ / ζ²: reusing DASHI's original three-phase and zero-fibre work

**Date:** 2026-10-25. **Latest proof consumer for PR #1250.** This is the intended cross-pollination, rather than an additional independent computation of the norm of `90ζ`.

## Existing source and proof owners (avoid duplicates)

- `DASHI.Algebra.TriadicDepthOneCharacters`: balanced residues `rNeg,rZero,rPos`, additive C3 character tables; symbolic `phase0,phase1,phase2` multiply as `1,ζ,ζ²`. **phase0 denotes exponent zero and VALUE ONE, not scalar zero.**
- `DASHI.Biology.BalancedTernaryFourierModeExact`: exact Fourier eigenphases for translations on the finite 3×3 torus; zero-frequency is a translation-invariant character, not a vanishing eigenvalue. The translation eigenvalues are nonzero roots of unity.
- `DASHI.Cognition.PhaseEnrichedTrit`: concrete distinct fine hidden states project to the same observable neutral balanced-trit zero, carrying different cyclic phase tags.
- `DASHI.Foundations.SignedZeroTernaryOrientationExact`: `-0,0,+0` are three **arrival-orientation records** over the same scalar neutral value; these are not three distinct scalar zero values, nor canonically the three C3 complex characters.
- `DASHI.Core.ZeroValueFibreNontrivialityExact`: the visible-zero quotient is non-injective, and the hidden future-class can fail to factor through that zero observation.
- `DASHI.Moonshine.C3FourierConjugationExact`, `C3CyclotomicAmplitudeAlgebraExact`, `MonsterC3CyclotomicEvaluationExact`: exact nontrivial conjugate characters and 1+ζ+ζ²=0; existing integer multiplicity-coordinate evaluation.
- `DASHI.Moonshine.Monster3BBalancedRegularFibreExact`, `Monster3BRegularC3BulkResidualFiftyThreeBidiExact`: Monster 3B restriction `53*trivial+65610*regular`, and the proof-status frontier separating regular character cancellation from an actual chosen submodule complement.
- `DASHI.Moonshine.Monster3BZetaSuzukiDiagonalNormCutsetExact`: the *conditional* common 729 extension and diagonal-kernel selection between direct and dual Sym² of 12.
- `DASHI.Biology.TernaryPhaseQuotientJCoarseBridgeExact`: the 27-to-9 phase quotient and balanced coarse-pair carrier equivalence; this does **not** itself construct the Monster 3B action or identify a phase frequency with balanced-trit zero.

## Critical semantic disambiguation

| Coordinate / object | Written form | Is it scalar zero? |
|---|---|---|
| additive residue / balanced trit | rZero or BT.zero | **No**; a label or observed neutral value |
| `C3Phase.phase0` | ζ⁰=1 | **No**; identity character/eigenvalue |
| `C3Phase.phase1` | ζ | **No**; nontrivial eigenvalue |
| `C3Phase.phase2` | ζ² | **No**; conjugate nontrivial eigenvalue |
| cyclotomic amplitude zero | 0+0ζ | **Yes**, in Q(ζ) |
| eigenspace multiplicity zero | n_1=0 (or another n_i=0) | **Zero DIMENSION**, not a zero eigenvalue |
| nonidentity character evaluation zero | χ(g)=0 | **Trace cancellation** of possibly nonempty eigenstates |
| signed neutral triad | (-0,0,+0) | one scalar zero, three orientation/arrival records |
| Riemann-zeta zero | ζ_R(s)=0 | wholly different complex analytic claim |

For an order-three **invertible** group operator g, `g³=I` excludes eigenvalue zero on any nonzero eigenvector. Therefore `{0,ζ,ζ²}` cannot be the list of its three eigenvalues. The correct eigenphase alphabet is `{1,ζ,ζ²}`; frequency-zero (rZero or phase0) evaluates to **one**.

The Fourier character of a C3-module with eigenmultiplicities `(n_1,n_ζ,n_ζ²)` is

```
 χ(e) = n_1+n_ζ+n_ζ²
 χ(z) = n_1+n_ζ ζ+n_ζ² ζ²
 χ(z²)= n_1+n_ζ ζ²+n_ζ² ζ.
```

In the rational cyclotomic basis `(1,ζ)`,
`χ(z)=(n_1-n_ζ²)+(n_ζ-n_ζ²)ζ`.
Its numerical value is zero **iff all three multiplicities agree**; in particular the nonempty regular module (1,1,1) has `χ(z)=0`, just like the empty module (0,0,0), but their identity dimensions differ (3 versus 0). This is an explicit example of the existing 'zero observation does not imply absence of fine structure' pattern, here for a character readout.

## NEW bridge: complete Fourier inversion of 12+78 central fingerprints

The four central values discussed in the previous round are equivalent to four Fourier multiplicity triples, **all with an empty 1-eigenspace**:

| Suzuki 12+78 candidate | χ(t1) | (n_1,n_ζ,n_ζ²) | Norm |
|---|---|---|---:|
| 12_ζ + direct Sym²12 | -78-66ζ | (0,12,78) | 5292 |
| 12_ζ + dual Sym²12 | 90ζ | (0,90,0) | 8100 |
| 12_ζ² + direct Sym²12 | -12+66ζ | (0,78,12) | 5292 |
| 12_ζ² + dual Sym²12 | 90ζ² | (0,0,90) | 8100 |

This is the stronger answer to 'ζ, ζ², zero': the **zero component is n_1**, not the scalar/eigenvalue zero. The direct symmetric-square options distribute 12 and 78 across opposite nontrivial phase spaces. The dual options concentrate all 90 in one nontrivial phase space. All four have dimension90, all have nonzero trace at the central generator, and none contains the trivial centre character.

In contrast, the **actual sourced Monster 3B** C3 character has
```
 (n_1,n_ζ,n_ζ²)=(65663,65610,65610);
 χ_W(e)=196883; χ_W(z)=χ_W(z²)=53.
```
Subtracting the 53-dimensional **character** residual leaves `(65610,65610,65610)`, a dimension196830 regular bulk with `χ(z)=0`. No assertion is made that a chosen actual ambient Monster submodule has been split with a literal basis, only that the sourced C3 character has this decomposition.

## Projector and exact checks

For `j∈{0,1,2}`, the ordinary C3 eigenspace projector is
```
 P_j=(I+ζ^(-j)g+ζ^(-2j)g²)/3.
```
Acting on a `ζ^k` eigenvector, it evaluates exactly to `δ_(j,k)`. The three projectors are orthogonal, sum to identity, and recover the multiplicity triple from the three character evaluations by the inverse Fourier transform.

`scripts/monster_3b_zero_zeta_fourier_maxcut.py` verifies these projector scalars over exact `Fraction`-valued `Q(ζ)`; four `12+78` triples and both 3B bulk/full character identities; 1331 finite Fourier round-trips over `0..10` for all three multiplicities; 1331 exact cancellation tests; and malformed-character negative inputs. Python only; no GAP or mmgroup needed. Local extended receipt: `/mnt/data/monster_c3/zero_phase_fourier_receipt.json`. This is a mathematical computation, not an Agda typecheck or selected Monster generator-action receipt.

`DASHI.Moonshine.Monster3BZeroZetaSquaredC3SeparationExact.agda` reuses the original phase, balanced-trit/hidden-zero, cyclotomic and Monster C3 owners and adds typed proofs of the four candidate dimension triples, zero 1-eigenspace counts, tagged scalar-zero/phase separation and original nonempty regular cancellation. Kernel build NOT run. The central quotient gate is separately owned: under a verified **common 729 extension and same diagonal kernel**, equality of 12/78 Suzuki central phases excludes mixed candidates. Neither the Fourier result nor this conditional gate identifies the specific Monster-inertia 12/78 characters without actual source label and quotient checks.

## Max-cut outcome / proof frontier

**Closed:** semantic confusion about phase-index zero versus scalar zero, exact multiplicity triple for each 12+78 character candidate, cancellation-vs-absence counterexample for the real Monster regular bulk, and a portable exact Fourier projective audit. This is new *cross-owner synthesis*, not new finite group representation theory.

**Open:** source-selected actual `6.Suz` 12/78 class-function and diagonal quotient match, same-object 729 extension choice, linear normalizer action and concrete Monster intertwiner. The old D4-only signed representation is an independent useful candidate but does not close these. Do not infer a physical quantum mechanism or Riemann-zeta zero from the shared 'ζ' notation.

**Attribution:** Fourier/characters—Terras (1999), Serre (1977); cyclotomic—Washington (1997); Monster subgroup and quotient—Barraclough/Wilson (2007), Bray/Wilson (2006); Suzuki symmetric square—Gabriele Nebe (2025), DOI 10.1007/s10801-025-01399-2; named DASHI files are repository computations, not original discoveries of those source theorems.
