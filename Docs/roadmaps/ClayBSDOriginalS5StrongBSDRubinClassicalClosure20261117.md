# BSD S5 original selected curve — full strong BSD CLASSICAL closure (2026-11-17)

**Original selected E/Q: y²=x³−x** (LMFDB **32.a3**, Cremona **32a2**, j=1728, conductor 32). **S5 CLOSED at the previously authorized CLASSICAL-MATHEMATICAL level**. This does **not** close native Agda/Lean fields or S6 universal BSD, and does **not** claim a new theorem relative to Karl Rubin's published CM work.

## Attribution and exact external source

Karl Rubin, *The Birch & Swinnerton-Dyer conjecture*, MSRI Introductory Workshop, **18 January 2006**, slides at https://www.math.uci.edu/~krubin/lectures/msri2.pdf. This original author's direct worked example, at the slide text around lines 237–244 and 287–309, states:

- For the **literal E:y²=x³−x**, its real period satisfies `Omega_E = 8*L(E,1)` (note that another approximate L decimal shown in these slides contains a digit typo; rely on exact relation and LMFDB crosscheck).
- Selected rank 0, regulator 1, c₂=2, torsion `(Z/2)^2`, hence BSD II holds iff `Sha(E/Q)=0`.
- Rubin's CM theorem: for an elliptic curve over Q with CM by imaginary quadratic K and L(E,1)≠0, BSD II holds away from primes dividing the number of roots of unity of K; for K=Q(i), only 2 remains.
- He explicitly notes for this same E: `Sha(E/Q)[2]=0`; therefore **full BSD II is true for E**. This is **Rubin's classical result**, not a new DASHI arithmetic theorem.

Source-specific independent database crosscheck: https://www.lmfdb.org/EllipticCurve/Q/32/a/3 confirms exact original equation, selected rank=0, torsion order 4, c₂=2, real period ≈5.24411510858424, L(E,1)≈0.65551438857303, analytic Sha order 1. The database analytic Sha field alone is numerical/invariant data and is NOT the proof of actual Sha triviality. The classical proof is Rubin odd-primary + genuine S3 global 2-descent. Another 32.a isogenous model has different period/torsion/Tamagawa; do not substitute its invariants.

## Classical closure chain

1. From earlier selected **S1/S2/S3** mathematical results (see `ClayBSDOriginalS3GlobalSelmerSha2RankZeroClassicalClosure20261116.md`), actual global Galois H¹ and Kummer local conditions yield `Sel²(E/Q)=delta(E(Q)[2])`, `Sha(E/Q)[2]=0`, and `E(Q)=(Z/2)^2`. Unlike a mere finite label sieve, these are the established classical same-curve Selmer facts. Native `OriginalSelmerCohomologyRealization` remains unfilled.
2. From selected **S4** classical closure, the actual level-32 modular L function has `L(E,1)>0`, not merely a toy eta series. Rubin/Coates–Wiles/Kolyvagin provide finiteness of Sha for analytic rank zero; Rubin's CM BSD theorem gives correct **odd-prime** order comparisons for each odd prime, since Q(i) has 4 roots of unity.
3. The exact `Omega_E=8L(E,1)`, `reg=1`, `prod c_p=2`, `tors order=4` produce the predicted Sha order
   `Sha_pred = L*4²/(Omega*1*2)= (L*16)/(8L*2)=1`.
   Therefore, for each odd prime `p`, Rubin's theorem forces `ord_p(#Sha)=ord_p(Sha_pred)=0`, so all odd-primary components vanish. The actual finite 2-primary component vanishes because `Sha[2]=0`: a nontrivial finite 2-group has an element of order 2. Hence `Sha(E/Q)=0`.
4. The strong rank-zero selected-curve coefficient identity is exact:
   `L(E,1)=Omega_E * Reg(E) * #Sha(E/Q) * prod(c_p) / #E(Q)_tors² = Omega_E * 1 * 1 * 2 / 16 = Omega_E/8`.
   Classical analytic rank and algebraic rank are both zero; the rank-zero regulator is 1 by convention.

This simultaneously closes S5's specifically unpaid **odd-primary Sha** and **full leading coefficient** at classical mathematical level. It is not an inference from `Sha[2]=0` alone. SymPy verifies the scalar equivalence, NOT Rubin's arithmetic theorem.

## Native / global firewall

- `DASHI/Mathematics/Arithmetic/BirchSwinnertonDyerBoundary.agda` defines `BSDLeadingCoefficientConjecture`, `FullBSDConjecture`, and `BSDScalarData` but these are generic scalar/structure records; it has not been populated with actual curve period as a native constructive real nor with actual Galois Sha cardinality. No `agda` or Lean kernel check is claimed.
- **S5 classical decision CLOSED, S5 native still OPEN. S6 universal BSD OPEN. YM D1/D2 OPEN.** Original six Clay endpoints 0/6. Expanded portfolio settled 14/28; open 14/28. Historical A–F 6/15 unchanged.
- This is imported known mathematics with direct author attribution (Rubin 1987 CM theorem; Rubin 2006 explicit worked example), combined with earlier original S3/S4 selected-curve reductions. Do not attribute Rubin's theorem to DASHI.
- For native work, exact remaining: actual elliptic Q-cohomology Kummer realization, native full Sha finiteness and odd-primary theorem transport, actual period `Omega_E=8L(E,1)` in the original types, original selected coefficient record and typechecked Agda/Lean same-object weld.

## Regression

`scripts/check_bsd_s5_selected_curve_rubin_20261117.py`: actual local Python+SymPy run PASS exact scalar algebra `Omega=8L,c₂=2,tors=4,reg=1,Sha=1`. It explicitly treats Rubin, classical S3/S4, and period identity as external theorem premises. Thus the checker is not a new proof of BSD.
