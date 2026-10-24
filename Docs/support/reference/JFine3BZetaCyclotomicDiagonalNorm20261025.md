# Monster 3B / Suzuki 12+78: cyclotomic norm and diagonal descent

## Primary provenance and existing owners

- R. W. Barraclough and R. A. Wilson, *The Character Table of a Maximal Subgroup of the Monster* (2007), DOI 10.1112/S1461157000001352, construction of 3^(1+12):6.Suz.2 and quotient N(3B), source 729-inertia family.
- Gabriele Nebe, *Symmetrizations of quadratic and Hermitian forms* (2025), DOI 10.1007/s10801-025-01399-2, Section 6, actual irreducible degree-78 Sym² of a degree-12 complex Suzuki-cover module, descending to 3.Suz.
- Lawrence C. Washington, *Introduction to Cyclotomic Fields* (1997), exact algebra of Q(zeta3). Our repository's original owners are `C3CyclotomicAmplitudeAlgebraExact`, `Monster3BCyclotomicNormSeparationExact`, and `Monster3BCyclotomicLinearAlgebraExact`. Do not duplicate their field machinery.
- `IbrahimMonster3BDiagonalKernelPaidSignGaugeCorrectionExact`: source-paid invariant K={identity} union main class 20, with 18/19/20 the lambda lifts; relative generator naming is a gauge.
- `IbrahimMonster3BPhaseOrientationGaugeSnowballExact`: simultaneous inversion zeta<->zeta² exchanges label names, not the physical representation content.
- `IbrahimMonster3BPhaseResolvedCharacterTwelveSeventyEightWeldExact`: published paired 17496/113724 restriction characters imply selected-phase halves 729*12 and 729*78 at source-character-family level. No explicit Monster coordinate intertwiner is thereby constructed.
- `JInvariant369Zeta6561MonsterCrosswalkExact` keeps cyclotomic zeta3 separate from the Riemann zeta function, despite consistent shared terminology.

## New exact discrimination

In the basis 1,zeta, with zeta²=-1-zeta and N(u+v*zeta)=u²-uv+v², the four pre-selection characters of
 `S90=U12 ⊕ Sym²(U12)` or `U12 ⊕ (Sym²(U12))*`
are:

| 12 phase | 78 interpretation | χ_S(t1) | Tr_Q(zeta)/Q | Norm | ranks at (ζ,ζ²) |
| --- | --- | --- | --- | --- | --- |
| ζ | direct Sym² | -78-66ζ | -90 | 5292 | (12,78) |
| ζ | dual Sym² | 90ζ | -90 | 8100 | (90,0) |
| ζ² | direct Sym² | -12+66ζ | -90 | 5292 | (78,12) |
| ζ² | dual Sym² | 90ζ² | -90 | 8100 | (0,90) |

**Reusable theorem:** for rational a,b,
```
 N((a+b)ζ)-N(aζ+bζ²)=3ab.
```
Here 8100-5292=2808=3*12*78. Cyclotomic norm, Fourier rank inventory and Galois conjugation produce an orientation-independent discriminator. Trace alone is uninformative: it is -90 in ALL four cases.

## The decisive conditional quotient gate

Let psi be ONE fixed irreducible 729-dimensional extension of the selected extraspecial Heisenberg representation to the Suzuki inertia group. In the main extension write `t1` for the central 3-element of 6.Suz, `t2` for the extraspecial centre, and `K=<t1*t2^epsilon>` for the same source-verified diagonal quotient kernel. If `psi(t1)=zeta^k` and `psi(t2)=zeta^h` with h nonzero, then the central kernel acts on each `psi ⊗ eta_d` summand (`d=12,78`) as

```
    zeta^(k+epsilon*h+phase(eta_d)).
```

For **BOTH** summands to descend through this SINGLE kernel with the SAME psi, subtracting their exponent equations gives

```
    phase(eta_12) == phase(eta_78) (mod 3).
```

For a 12 of phase ζ^a, direct Sym² has phase ζ^(2a) != ζ^a, while dual Sym² has phase ζ^(-2a)=ζ^a since -2 ≡ 1 (mod3). Therefore *within the explicitly stated common-psi and Sym²/dual candidate family*:

- mixed fingerprints, norm5292: **incompatible** with common diagonal descent;
- pure fingerprints, norm8100: **pass this necessary phase test**.

Passing the phase test is not sufficient for quotient descent, irreducible row occurrence or source-coordinate equivalence. The name ζ vs ζ² remains a simultaneous phase gauge. If the 12 and 78 constituents use DIFFERENT 729 extensions, the common-psi conclusion is not applicable; that possibility must be tested separately rather than silently excluded.

## Implemented and verified

- `scripts/monster_3b_zeta_diagonal_fingerprint_maxcut.py`: exact local exhaustive four-case Q(zeta) arithmetic, norm/Galois/rank and 48 common-kernel phase assignments (2 h × 3 k × 2 signs in each of four rows). Each direct Sym² branch has no compatible assignment; each dual branch has four.
- `DASHI/Moonshine/Monster3BZetaSuzukiDiagonalNormCutsetExact.agda`: imports the existing cyclotomic, gauge and original diagonal-kernel sources, proves source-written finite exclusion of ordinary Sym² under the common-psi condition; lists all four trace/norm results. Imported by the Monster validation owner. Agda was NOT run in this session.
- `scripts/monster_3b_suzuki_sym2_character_screen.g`: supplements the full table `Sym²/dual` equality test with central-C3 equality, explicitly rejecting logically inconsistent paired phases. GAP was NOT run locally.

## Updated Pareto / strongest surviving steelman

The kernel *subgroup* and the matched outer **character families** are already owned in-repo. The new four-to-two phase reduction should not re-open the historical `<t1*t2>` versus inverse nomenclature. The shortest next source-specific check is to use the existing selected 12ab/78ab character-table and main-quotient producer to confirm the **chosen common psi**, select the equal-centre-phase pair, and validate full class-function descent and its 12+78 Hom character. No mmgroup or dense Monster matrices are needed for that character-level comparison. An actual Monster basis intertwiner, normalizer cocycle and physical mechanism remain unproved.

**No physics promotion:** the cyclotomic norm gap is exact representation arithmetic and does not identify a new physical interference process, quantum observation, Riemann-zeta identity or Monster-driven laboratory effect.

## New reason the old D4 model survives the quotient correction

The finite 12-dimensional JFine D4 operators are **orthogonal signed permutations**; their induced operators on Sym²(12) are also orthogonal signed permutations. Their contragredient matrices are therefore exactly the original matrices, giving an explicit D4-equivariant invariant pairing and
`Sym²(U12)|D4 ≅ (Sym²(U12))*|D4`.
Hence changing from direct to dual Sym² to meet the diagonal central-phase gate **does not alter** the locally checked D4 character `[90,18,2,18,18]` or the previous rational D4 intertwiner. No new D4 construction is needed.

This self-duality is ONLY over D4. A 6.Suz central order-three element separates the representations: its scalar on Sym² is ζ^(2a), whereas on the dual it is ζ^(-2a). The source 6.Suz/Monster quotient action does not follow from D4 real character agreement. Exact signed-generator consumer: `scripts/monster_3b_zeta_d4_dual_local_test.py`; independent local test passed.

Further exact prior-art connections, not additional claims: `C3FourierConjugationExact` and `C3CyclotomicRealDescentExact` already prove phase inversion exchanges the Fourier rows but fixes norm/trace, while `MonsterC3CyclotomicEvaluationExact` carries the exact integer phase-multiplicity projector coordinates. The new norm selector is a specific consumer of those results.
