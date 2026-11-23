# Fermat quintic → C3/369 → heterotic gauge and fermion index: original same-source maximum cut

Date: 2026-11-18. Research programme: [Agda PR #1531](https://github.com/chboishabba/dashi_agda/pull/1531).

## Direct result

We have a concrete compact smooth CY3 candidate, a literal Z/3 automorphism of its **same** Fermat polynomial, and the exact topological/representation-theoretic quantities determining the simplest heterotic standard-embedding chiral-sector candidate.

**Result A: unquotiented standard embedding has net 100 chiral families, not three.**
**Result B: C3-invariant untwisted quintic deformation modes have dimensions 37 + 32 + 32; with the invariant Kähler direction, the untwisted net difference is 36, not three.**
**Result C: the selected C3 action is NOT free. Its fixed locus is a genus-six plane quintic curve and two isolated projective eigenpoints. The underlying ordinary quotient Euler is -72, whereas the orbifold Euler is -88. These do not themselves determine the full heterotic twisted-sector spectrum.**

The argument is a **classical index and algebraic finite-orbit calculation**. This round did not construct an explicit ten-dimensional gauge connection, fermion zero-mode wavefunctions, or BRST-consistent worldsheet.

## Attribution and exact original owners

- Classical mathematics/physics: Euler sequence, adjunction, Chern–Gauss–Bonnet, Jacobian ring deformation theory, Burnside/finite-group invariant exactness, projective hypersurface fixed loci, Atiyah–Singer index theorem, E8 heterotic standard embedding and E6 decomposition. These are not discoveries of DASHI or this PR.
- External source examples: *The orbifold Hochschild product for Fermat hypersurface* (Advances in Mathematics 2023, DOI 10.1016/j.aim.2023.109186) documents the Fermat-quintic orbifold fixed genus-six curve. Classic quintic Hodge numbers (1,101) and Euler -200 appear in standard Calabi–Yau references, including https://www.macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Varieties/html/___H__H%5E__Z__Z_lp__Projective__Variety_cm__Coherent__Sheaf_rp.html. The heterotic standard-embedding chiral count and anomaly requirements are classical string compactification, not a source-created physical result.
- Existing actual DASHI Agda owners: `FermatQuinticGradientNonvanishingExact`, `FermatQuinticJacobianCriterionHandoffExact`, `QuinticThreefoldCandidate`, `CalabiYau369CompactFibreBridge`, `CalabiYauPhysicalProducerCutset`, `CalabiYauPhysicalProducerCompilerExact`, `U1SU2GroupTorusExact`, `TriadicDepthOneCharacters`, `TOE369C3RealizationGraphExact`, `DASHITOETerminalMaxCutExact`, `KKE6EtaCSWZSameBundleConsumerExact`, `KKCircleQEDChiralityConsumerExact`, `KKQEDQCDVacuumConsumerBIDIExact`.
- User research contribution: ask if different observers see different effective dimensions and matter content, and require a single actual higher-dimensional string/369/SM/quantum/KK/GRQFT source—not independent anonymous-sector wrappers.
- New ChatGPT-assisted implementation: exact original polynomial/C3 orbit and selected index comparison, scripts and arithmetic boundary modules, audit and physical-gate ledger. Numerical/finite identities independently reproduced in local Python/SymPy, **not** Agda kernel acceptance or newly discovered mathematics.

## 1. Geometry of the selected original CY3

Original selected candidate:
```
X = {[z0:z1:z2:z3:z4] in CP4 | P=sum(z_i^5)=0}.
```
The existing Agda `FermatQuinticGradientNonvanishingExact` proves non-simultaneous fourth-power zero from explicit field assumptions; `FermatQuinticJacobianCriterionHandoffExact` carries it to smoothness **conditional on the genuine projective Jacobian criterion**, not through a Bool. Classical characteristic-zero CP4 gives that criterion. Projective implies compact. Adjunction gives trivial canonical class.

Using H as hyperplane class:
```
c(TX) = (1+H)^5/(1+5H) = 1 + 10 H² - 40 H³
∫_X H³ = 5
χ(X) = ∫_X c3(TX) = -40*5 = -200.
```
Selected existing `QuinticThreefoldCandidate` and its historical code remain the owner of the geometry target.

Degree-five homogeneous monomials in five variables: C(9,4)=126.
The degree-five Jacobian ideal of Fermat P has independent basis
`z_i^4 z_j`, 5*5=25. Hence Jacobian-ring degree-five dimension
`126-25=101=h^(2,1)`. The hyperplane `h^(1,1)=1`.

## 2. First nontrivial gauge and chiral compactification: standard embedding

The classical heterotic standard embedding makes a **chosen** SU(3)
gauge-bundle identification `V=TX` within one E8 factor, leaving
an E6 factor and a chiral 27 vs conjugate-27 matter index. Subject to
the standard heterotic spin, Bianchi and background assumptions:
```
net(27 - anti27) = (signed convention) χ(X)/2 = -100
net magnitude = 100.
```
This is an honest specific gauge-bundle/fermion index model, unlike
relabeling the earlier circle scalar as a quark. It is NOT the actual
observed SU3c × SU2L × U1Y Standard Model: no Higgsing or Wilson lines
to exact source physical SM representations were constructed; it has
the WRONG three-family index. In particular, the pre-existing
`U1SU2GroupTorusExact` group embedding neither changes the index
nor proves the required E8/SM branching.

Exact checker `scripts/check_string369_quintic_chiral_index_exact.py`:
Chern polynomial, Euler, Jacobian count, 100≠3 and nonfree symmetry.

New `DASHI/Unified/String369QuinticChiralIndexBoundaryExact.agda`:
exact finite arithmetic consequences AFTER the classical Chern/index
input hypotheses; does NOT kernel-prove Chern classes or the physical
spin-Dirac operator. Reuse preexisting quintic dimension theorem.

## 3. ACTUAL same-geometry C3 selection: no label-only claim

Use the exact polynomial automorphism
`g:(z0,z1,z2,z3,z4) -> (z1,z2,z0,z3,z4)`.
Its order is three and it preserves the defining P. Its action on
monomials is a concrete permutation, not a 369 analogy.

For degree-five polynomials, exactly nine exponent vectors are fixed
under the 3-cycle (if a0=a1=a2=k: k=0 produces 6, k=1 produces 3).
By Burnside:
```
dim polynomial degree-5 invariant = (126+2*9)/3 = 48.
```
For the 25 Jacobian basis monomials `z_i^4 z_j`, exactly four are
fixed (both indices among z3,z4), so
```
dim Jacobian degree-5 invariant = (25+2*4)/3 = 11.
```
Taking invariants is exact over characteristic zero for finite groups.
Thus the Jacobian quotient has `48-11=37` invariant directions.
Its 101-dimensional C3 representation decomposes into character
multiplicities `37 + 32 + 32`. The hyperplane Kähler class is C3
invariant (one dimension).

For the selected standard-embedding and simple **untwisted invariant**
interpretation, the invariant difference is `37-1=36`, not three.
This is not a theorem that an actual heterotic C3 orbifold has exactly
36 generations: gauge equivariant lifts, quantum GSO/twisted states,
discrete torsion and anomaly/inflow can change physical sectors.
The invariant decomposition is exact mathematics, irrespective of
how an observer chooses to measure/ignore the modes.

Exact checker:
`scripts/check_string369_quintic_c3_invariant_modes_exact.py`.
New `String369QuinticC3InvariantSpectrumBoundaryExact.agda`
records precise arithmetic and non-three test. The actual monomial
enumeration is currently external Python, not Agda kernel.

## 4. Correct fixed locus and two different quotient Eulers

A projective point fixed by g lies in one of three eigenspaces of the
cyclic permutation of z0,z1,z2.

- Eigenvalue 1 eigenspace is `[t:t:t:u:v]`, giving the smooth plane
  quintic `3t^5+u^5+v^5=0`, genus `(5-1)(5-2)/2=6`.
- The other two eigenspaces are one-dimensional projective points
  represented by `[1:ω:ω²:0:0]` and
  `[1:ω²:ω:0:0]`. Both lie in the Fermat quintic, because
  `1+ω^5+ω^10=0`.
- Thus the fixed locus is an entire genus-six curve PLUS two
  isolated points, not "seven isolated points".

Euler of fixed locus:
`χ(X^g)=2-2*6+2=-8`.
Ordinary topological quotient:
`χ(X/C3)=(χ(X)+2χ(X^g))/3=(-200-16)/3=-72`.
Stringy/orbifold Euler of commuting-pair formula:
`χ_orb=(χ(X)+8χ(X^g))/3=(-200-64)/3=-88`.

The ordinary quotient and orbifold invariants are mathematically
distinct. Neither can be silently called the actual physical 4D
family index without a selected SUSY string model, proper equivariant
gauge bundle, full twisted sector and anomaly cancellation.
The nonfree fixed curve also prevents a smooth free-quotient argument.
The cited 2023 Fermat orbifold literature supplies historical context;
this source-specific arithmetic was independently checked here.

## 5. What observer-relative dimensions can and cannot change

The selected original 10D fine geometry and field bundle may be
observed through different mode-limited observable algebras.
An observer limited to the base metric/zero mode can lose all internal
gauge information; a finer detector can recover extra states if
physically coupled. The previous `String369ObserverFirstBandExact`
and KK scalar action illustrate that exactly.

But hiding internal zero modes by a partial trace does NOT, by itself,
change `χ(X)`, the original gauge-bundle Dirac index, or all anomaly
constraints. A physical quotient/orbifold or distinct bundle can change
the actual Hilbert sector and its effective chiral index—this requires
the selected equivariant spin/gauge structure and twisted corrections.
Observer selection alone cannot be used to declare the extra 97
families absent from the underlying theory.

## 6. Highest-alpha open original-source gates

- [x] Reuse pre-existing original Fermat gradient/Jacobian and actual
      selected quintic; no duplicate geometry proof.
- [x] Explicit classical standard-embedding chiral index magnitude
      100, not 3: exact Chern/Jacobian computations.
- [x] Explicit same-C3 invariant original polynomial/Jacobian
      mode split 37+32+32; untwisted index-difference 36.
- [x] Fixed genus-six curve + two projective points; ordinary vs
      stringy-orbifold Euler (-72 vs -88).
- [ ] Exact Agda kernel acceptance of new modules, plus actual Agda
      enumeration proof of the 126/25 orbit counts, and formal
      Chern/index theorem rather than labelled arithmetic.
- [ ] Construct the same actual compact CY gauge bundle E with
      c1(E)=0, Bianchi `c2(E)+[W]=c2(TX)` (normalization and possible
      two E8 factors explicitly accounted) and stable Hermitian
      Yang–Mills connection; produce actual cohomology zero modes.
- [ ] Find a compatible nonstandard bundle/geometry and any quotient
      giving **three net chiral Standard Model families**, with
      equivariant lift, nonfree twisted-sector correction if used,
      anomaly cancellation and gauge breaking.
- [ ] Connect the exact C3 action to ORIGINAL 369 character and
      original-Wilson YM field/physical SU3c/SU2L/U1Y, not merely
      a matching abstract C3 phase.
- [ ] Prove literal same ten-dimensional action reduces to
      original gauge/QFT/GR stress and quantum TPS/Hamiltonian.
- [ ] Complete SUSY/worldsheet BRST, actual moduli/radion stability,
      physical metric-calibrated TSFV observer and phenomenology.

**No promotion:** The classical standard embedding on this quintic
is a useful **falsifying benchmark for three families**—not proof
that string compactification or DASHI 369 unification is impossible.
