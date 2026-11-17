# KSW668 F8 maximum-cut XII — modular yes; sporadic conditional; positive radial ladder; KK-coordinate correction

**Date:** 16 November 2026. **Owner:** existing KSW PR #1520, following merged #1512. **Origin:** user question "Sporadic maybe, modular, yes, no?" following the original three TT channels and negative cyclic C3 symmetry test.

## Original physical coordinates (important correction)

The moving a(t)=t Poincare AdS5 model has coordinates (T,z,x1,x2,x3). Its extra-dimensional normal coordinate is **z**; the radial coordinate **r=|x3-vector|** belongs to ordinary three-space. The original axial tensor decomposition has ell=0,2,4 with regularised effective radial spatial dimensions d=3,7,11.

Therefore the eigenvalues of the three finite-volume operators in **r** are **NOT Kaluza-Klein masses**. A KK mass spectrum would require a separate z-normal Sturm-Liouville eigenproblem with the z^-3 measure and appropriate moving Israel boundary. A time-dependent brane can also couple instantaneous z-modes, so no exact fixed KK tower follows from the spatial angular decomposition. This corrects the unsupported interpretation that the XI 98.64% radial sensitivity must be caused by high-mass KK excitation.

Further causal guard: if each member of a convergent sum of retarded 4D kernels has support inside the same fixed closed 4D causal cone, the distributional sum also has support there. An earlier outside-brane-cone response requires genuinely different moving-bulk geometry/nonlocal effective propagation; ordinary interference of modes with common causal support cannot produce it.

## Genuine positive operator relation missed by the cyclic C3 test

Let
\[
L_d=\partial_r^2+\frac{d-1}{r}\partial_r,\quad
J=\frac1r\partial_r.
\]
Direct symbolic algebra for a generic smooth radial function proves
\[
\boxed{L_{d+2}J=JL_d,\qquad L_{d+4}J^2=J^2L_d.}
\]
Consequently
\[
\boxed{L_7J^2=J^2L_3,\quad L_{11}J^2=J^2L_7,\quad
L_{11}J^4=J^4L_3.}
\]
This is an exact **dimension-raising differential intertwiner** between the original continuum radial differential expressions. The other moving AdS coefficients, warp and Israel-normal differential operators are independent of ordinary r, so the radial ladder can also be carried through the homogeneous bulk operator and through sources only when the sources are transformed in parallel.

On a triple of radial amplitudes, the non-invertible map
\[
N(f_0,f_1,f_2)=(0,J^2f_0,J^2f_1)
\]
commutes with the direct sum of the three interior radial differential operators and satisfies N^3=0. It is a **nilpotent shift**, NOT the unitary, invertible label cycle Base369.rotateTri previously refuted. J^2 annihilates constants; artificial radial finite-boundary Dirichlet data do not in general transport. The XI finite-volume full-matrix noncommuting natural C3 result and this new continuum positive ladder are compatible.

### Actual compact TT source fails the ladder condition

The source channels are three independent fourth-derivative combinations of the same original compact bump f_eps. For ell0,
\[
S_0f=\frac25(f''''+4f'''/r),
\]
and for ell2,
\[
S_2f=\frac47(f''''+f'''/r-6f''/r^2+6f'/r^3).
\]
Normalize the original eps=.04 compact smooth bump as G0=eps^4 S0 f and G1=eps^4 S2 f/(r/eps)^2. The dimensionless comparison eps^4 J^2 G0 / G1 at r/eps=.3,.5,.7 gives approximately -97.55, +289.71, +146.25. The sign and ratio vary; these source modes are not one common ladder orbit or constant scalar multiple. The independent exact counterexample f(r)=r^10 gives a nonzero polynomial source-ladder residual. The ORIGINAL source-specific F8 dual-Weyl result thus does not follow from the positive homogeneous intertwiner.

## Modular: exact finite Weil representation, but no physical modular symmetry

Native Base369 unsigned ternary indices q=0,1,2 can be endowed with a **CHOSEN additional** finite quadratic form Q(q)=q^2/3 mod 1. Let omega=exp(2 pi i/3). On C[Z/3], set
\[
S=-\frac{i}{\sqrt3}(\omega^{jk})_{0\le j,k<3},\qquad
T=\operatorname{diag}(1,\omega,\omega).
\]
Exact SymPy verifies S^4=I, S^2=(ST)^3=-P, T^3=I (P exchanges indices 1 and 2), and S,T are unitary. The Gauss multiplier -i is necessary for the **linear** SL2(Z) relations rather than an uncorrected projective Fourier action.

This provides a genuine mathematical Weil representation for the chosen 3-element finite quadratic module, NOT a demonstrated physical modular action. The original AdS5 TT source does not supply Q, a modular weight, a vector-valued modular form, an S/T-covariant physical observable, or an SL2Z action on original moving Neumann dynamics. Indeed [S,diag(3,7,11)] is nonzero; modular S mixes dynamically non-equivalent radial channels. Its abstract representation is useful for bookkeeping/spectral transforms, but physical covariance is an independent OPEN gate.

**Reused owners:** DASHI Physics Closure TriadicEisensteinTransformationTheorem (actual SL2Z punctured lattice carrier); DASHI Moonshine JInvariantPuncturedLatticeReindexExact; DASHI Moonshine PenumbralVectorValuedForm (Weil/metaplectic form witnesses); existing B3 -> SL2Z braid checker and the AdS3/Monster bridge. No new base ternary foundation was invented.

## Sporadic / Monster: what is and is not licensed

The Monster has order-three elements and an order-three **subgroup** may act on an abstract index chart. But the entire Monster has no nontrivial three-dimensional complex linear representation: its smallest nontrivial irreducible complex representation has degree 196883. An actual whole-Monster action needs a nontrivial large graded VOA/auxiliary fibre and a physical source-to-observable map; a 3-channel permutation cannot supply that. Do not conflate distinct Monster 3A/3B conjugacy classes.

Existing repo AdS3/Monster documents correctly treat Witten's 2007 c=24 AdS3/CFT2 suggestion as a conjectural physical identification. The modular J/q-series/graded VOA results do NOT show a full Monster/AdS5 moving-brane, bulk tensor, Weyl or KK equivalence. Bridging them would need explicit geometry/reduction, matter/flux, a covariant VOA representation and the SAME physical source/receiver observer.

References:
- J. Dereziński and S. Richard, radial/Bessel operator transformations: https://users.fuw.edu.pl/~derezins/inverse-square-revised.pdf
- F. Strömberg, finite quadratic modules and Weil representations: https://webhomes.maths.ed.ac.uk/~v1ranick/papers/stromberg.pdf
- E. Witten, Three-Dimensional Gravity Revisited, 2007, original proposal: https://arxiv.org/abs/0706.3359
- Griess and Smith, smallest nontrivial Monster complex module: https://doi.org/10.1080/00927879408825189

## Source ownership and exact remaining gates

New actual producer: scripts/ksw668_f8_modular_radial_ladder_crosswalk.py. New tests: scripts/test_ksw668_f8_modular_radial_ladder_crosswalk.py. Source-level generic Agda theorem: DASHI/Physics/Gravity/KSW668AdS5TTModularRadialLadderConsumerExact.agda; this proves nilpotent triple commutation assuming real adjacent physical intertwiner premises, not the complete analytic PDE theorem. Imported into KSW668BraneBulkMaxCutEverything, JInvariantBase369CrossPollinationEverything, EverythingTOESymmetryResolved369 and Unifier. Local independent SymPy tests 13/13 PASS; physical compact bump samples checked at 50-digit working precision. The exact GitHub PR-head executable run and pinned Agda 2.9 kernel are NOT RUN.

| Exact lemma / gate | Disposition |
| --- | --- |
| ads5OriginalEvenTTL3L7L11DimensionRaisingJ2 | CLOSED: smooth interior continuum differential identity; finite boundaries/source remain open |
| ads5OriginalTTThreeChannelNilpotentShiftCommutes | CLOSED conditionally on exact ladder premise; Agda source-only |
| ads5OriginalCompactTTSourceProfilesFormJ2Orbit | REFUTED generically and tested false for the actual eps=.04 compact bump |
| ads5OriginalBase369Z3QuadraticModuleWeilST | CLOSED finite exact S/T modular algebra; Q is a chosen rather than physical charge |
| ads5OriginalWeilSCommutesWithRadialPhysics | REFUTED |
| ads5OriginalMonsterThreeModeNontrivialFullAction | Impossible for whole Monster acting directly on 3-dimensional complex amplitudes |
| ads5OriginalRadialFVSpecIsKKMassSpectrum | FALSE: r is spatial, z is KK normal |
| ads5OriginalTTCompactSourceVsConservativeRadialPropagationErrorSeparation | OPEN, highest numerical gate following XI 98.64% radial signed sensitivity |
| original joint energy-stable Israel constraint, coupled SSPRK3, H4+epsilon Neumann-to-both-Weyl trace | OPEN |
| original t=2 FIO compact-source reception, F9 matter/cylinder, F10 detector, F11 pinned Agda, D1 experiment | OPEN |

**Next discriminating mathematical test:** use the exact continuum J² ladder to manufacture a known source-covariant cross-channel benchmark; compare it against the original shell FV operators, axis/origin and finite outer Dirichlet boundaries. Only then can radial propagation error be separated from original source-profile resolution. This does not change XI's failed three-grid dual-Weyl receiver acceptance.
