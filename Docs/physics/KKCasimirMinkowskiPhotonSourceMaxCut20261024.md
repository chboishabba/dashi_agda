# KK source/EM/radion max-cut — constructive one-loop Minkowski circle (2026-10-24)

**Priority correction (same-order graviton quantum contribution):** The single physically preferred free one-loop candidate includes **one 5D graviton (-5), one separate 5D Maxwell (-3), one massless scalar (-1), and three massive 5D Dirac fields (+12)**. Its potential has a positive stable Minkowski-radius minimum at z0 = **1.6975217111**. Two massive Dirac fields without the -5 graviton correction constitute only a matter-loop truncation. Every quantitative physical result below is for the graviton-counted primary spectrum unless explicitly labelled otherwise.

**Primary executable:** `scripts/check_kk_casimir_bidi_consumer.py`; **5D neutral-source reduction:** `scripts/check_kk_neutral_source_reduction.py`; earlier `scripts/check_kk_jordan_sourced_sphere.py`. This is the **gravity critical path**; Alexander horns PR #1244 are an optional global-topology countermodel, not a dependency.

## Source and attribution

- M. A. Rubin and B. D. Roth (1983), *Fermions and stability in five-dimensional Kaluza–Klein theory*, Phys. Lett. B 127, 55–60; DOI **10.1016/0370-2693(83)91629-5**. Historical prior art for massive fermion/boson Casimir stabilisation.
- T. Appelquist and A. Chodos (1983), *Quantum dynamics of Kaluza–Klein theories*, Phys. Rev. D 28, 772; DOI **10.1103/PhysRevD.28.772**. Original effective radion quantum potential, reliability concerns and vacuum counterterms.
- G. von Gersdorff and A. Hebecker (2005), *Radius stabilization by two-loop Casimir energy*, Nucl. Phys. B 720, 211–227; DOI **10.1016/j.nuclphysb.2005.06.001**. Perturbative radius stabilisation and extra sectors.
- Bertotti, Iess and Tortora, *Nature* 425 (2003), DOI **10.1038/nature01997** (Cassini post-Newtonian gamma).
- Lee et al., *Phys. Rev. Lett.* 124, 101101 (2020), DOI **10.1103/PhysRevLett.124.101101**, 95% constraint on gravitational-strength Yukawa forces with ranges >=38.6 micrometres in their tested parameterisation. DO NOT substitute this one number for a complete bounds analysis.
- DASHI reduced-action prior art **PR #1239**; spherical Helmholtz and steelman BIDI **PR #1241**. All classical KK/Brans–Dicke/Casimir expressions are standard, not credited as original discoveries.

## One candidate-specific 5D EFT

Take a circle `y ~ y+2pi`, `ds5^2 = gJ_mu_nu dxmu dxnu+b^2(dy+kappa A_mu dxmu)^2`. The physical matter content of the PRIMARY candidate is:
1. five-dimensional Einstein gravity plus a renormalised constant bulk vacuum-energy density `Lambda5`;
2. one massless real periodic 5D scalar field `Phi`;
3. one independent massless periodic 5D Maxwell field `B_A`, with `B_mu` its 4D massless photon zero mode and `B_5` a separate Wilson-line modulus;
4. THREE massive periodic 5D Dirac fermions of the same bulk mass `mF`, neutral under `B_A` for the freely computed vacuum potential;
5. (for sources) standard 5D massive test worldlines, optionally coupled to `B_A`, homogeneously distributed in the circle coordinate at long wavelengths and constrained to zero KK gravitational momentum `p5=0`. This is a classical source EFT, not the entire Standard Model.

At background `<Phi>=<Psi>=<B_A>=0`, the circle translation is unbroken. The graviphoton `A_mu` remains massless by 5D diffeomorphism/gauge invariance; the independent photon `B_mu` remains massless by independent 5D Maxwell gauge invariance. This is NOT a Higgs or winding/Stueckelberg phase condensate. Vector zero-mode masslessness is protected by these symmetries, subject to regulator and vacuum respecting them; full quantum anomaly and other sector audits remain open.

### Why the physical photon must be distinguished from the geometric U(1)

For the KK zero-mode Einstein-Hilbert reduction, canonical normalization gives the n-th fifth-momentum mode `g_KK(n)=sqrt(2)*n/(M_Pl*b0)` in the declared conventions. For the observed unit electron charge `e~0.30282212`, strict identification `g_KK(1)=e` would require `b0~3.78456e-34 m` or **4.67 reduced Planck lengths**, where this one-loop semiclassical truncation is NOT quantitatively controlled. At `b0=1e-24m`, `g_KK(1)=1.146e-10`. No choice of the bare gauge-coordinate normalization kappa changes this relation.

The independent bulk Maxwell zero-mode has independent coupling `e4=e5/sqrt(2pi*b0)`; adjusting e5 can match e4 without shrinking b0 to the Planck scale. This passes the *massless photon and normalization* consumer, NOT the stronger *all of observed QED / chiral Standard Model* consumer: charge spectrum, Wilson-line dynamics, charged matter loops, anomaly cancellations, chirality and local tests still need work. One physical electron from a separate 5D sector modifies the one-loop Casimir spectrum and must be included before a complete cosmological claim.

## Derive one-loop vacuum potential, not an invented radion polynomial

A periodic 5D real scalar contributes the renormalised 4D Jordan effective Casimir potential

`V_J^(scalar)(b,m)= -c0/b^4 f(2pi*m*b)`,
`c0=3*zeta(5)/(64*pi^6)`,
`f(z)=[1/zeta(5)]*sum_(n>=1) exp(-n*z)*(1+n*z+(n*z)^2/3)/n^5`.

This follows from the standard proper-time heat kernel plus Poisson summation, with equivalent Bessel `K_(5/2)` representation. Numerically independently checked against the Bessel formula. The finite nonlocal winding part is extracted; divergent b-linear/local vacuum terms are absorbed into the renormalised Lambda5 and gravitational couplings. For a free periodic 5D Maxwell field, three physical polarizations give -3 scalar units; each periodic 5D Dirac fermion gives +4 scalar units. Therefore the PRIMARY field content yields -4 massless units and +8 massive units.

With background circle radius b0 and Einstein frame `gE=(b/b0)gJ`, define `x=b/b0` and `z0=2pi*mF*b0`. The one-loop 4D Einstein-frame potential is

`V_E(b)=(c0/b0^4)*U(x)`,
`U(x)=ell/x+[-a+d*f(z0*x)]/x^6`,
`a=9,d=12`, `ell=2pi*Lambda5*b0^5/c0`.

A flat stable static 4D vacuum requires `U(1)=0, U'(1)=0, U''(1)>0`. Algebraically these are

`f(z0)-z0*f'(z0)/5=a/d`;
`ell=a-d*f(z0)=-d*z0*f'(z0)/5 >0`;
`U''(1)=d*(z0^2*f''(z0)-4*z0*f'(z0)) >0`.

For `0<a/d<1`, `h(z)=f(z)-z*f'(z)/5` decreases strictly from 1 to 0 as z grows, since

`h'(z)= -z/[15*zeta(5)] sum_(n>=1) e^(-nz)*(3+3*nz+(nz)^2)/n^3 <0`.

Hence the stationary-Minkowski root is UNIQUE for this free-field coefficient choice. The curvature is positive by the same positive series (not merely a finite-difference numerical observation). The numeric primary root is

`z0=1.69752171111651, ell=1.14266825367, U''(1)=23.619407163`.

The positive renormalised Lambda5 **must be tuned** against the loop vacuum energy; zero cosmological constant is NOT automatic or technically natural. The vacuum is a local finite-radius minimum, not a proof of global cosmological stability or ultraviolet completion. The preferred spectrum includes the **free** 5D graviton contribution at one-loop order. Gravitational and charged-matter *interaction* corrections, counterterm/renormalisation assumptions, charged-spectrum contributions and Wilson-line fluctuations can shift this calculation and are not verified here. A two-Dirac matter-only truncation is shown solely as a separate diagnostic, not the full primary action.

## Positive radion mass and source

The canonically normalised scalar is `varphi=sqrt(3/2)*M_Pl*log(b/b0)`, with `M_Pl^2=2pi*b0*M5^3`. The computed positive radion mass is

`m_rad² = (2*c0/(3*M_Pl²*b0^4))*U''(1)`.

For primary model `sqrt(2*c0*U''/3)=0.0282152653406`, so the Compton range is `lambda_rad = M_Pl*b0² /0.0282152653406` in natural units.

There is now a source-side SAME-ACTION bridge: from standard 5D massive worldline action `-m integral ds5`, conserved covariant fifth momentum is `p5 proportional to b²(dot y+kappa*A_mu dot xmu)`. Neutral worldlines with `p5=0` satisfy `dy=-kappa*A_mu dxmu`, and the entire fifth-direction metric block drops from `ds5²`, leaving `ds_J²` exactly. Consequently they couple minimally to the Jordan metric; in Einstein frame `A(varphi)=exp[-varphi/(sqrt6*M_Pl)]` and the radion-matter coupling is `beta=-1/(sqrt6*M_Pl)`. A long-wavelength uniform distribution of such source worldlines can be U(1)-invariant. This proves *test-worldline / dust coupling*, NOT that all Standard Model fields, material stress, pressure and rotating Earth configurations share the same universal coupling.

For dust, the linearised static exterior and interior equation is `(nabla²-m_rad²)varphi=-rho/(sqrt6*M_Pl)`, with the exact C1 uniform-sphere solution checked in `check_kk_jordan_sourced_sphere.py`. The corresponding finite-size Yukawa force at a spherical body's surface (relative to **bare** Newton) is

`F_rad/F_Newton = [(z-1)+(z+1)*exp(-2z)]*(1+z)/(2*z^3)`, `z=R/lambda_rad`.

At `b0=1e-24m` the primary model gives `lambda_rad=4.3734922e-13m`, a scalar-to-Newton force of approximately `3.432e-20` at the Earth surface and `3.143e-22` at the Sun surface; `mF~5.33116e7 GeV`, `b0*M5~2.893888e6`, supplying significant semiclassical hierarchy. These values are **not empirical fits**. No full solar Shapiro-delay integration, laboratory force geometry, nuclear/atomic coupling check or same-physical-matter source is certified.

## Two-consumer BIDI verdict

| Consumer | Primary gravity + Maxwell + scalar + three-Dirac candidate |
|---|---|
| Finite compact circle and stable stationary Minkowski vacuum at one loop | PASS under renormalized EFT assumptions and cosmological tuning |
| Positive radion curvature / mass | PASS at computed minimum |
| Photon B_mu remains massless by independent unbroken U1 gauge symmetry | PASS conditional on anomaly-free, regulator-preserving matter sector |
| Geometric graviphoton A_mu = measured electromagnetic photon | FAIL in semiclassically controlled b0 range |
| Source-dependent neutral dust matter coupling from same 5D worldline action | PASS for p5=0 worldlines; full Earth matter source not proved |
| Scalar fifth force negligible on Earth/Sun-scale source surfaces at selected b0 | PASS for linear constant-density toy source; comprehensive constraints unverified |
| QED charged chiral matter and full Standard Model spectrum | OPEN; modifies loop spectrum |
| One-loop stable radius including complete quantum-gravity, charged matter, Wilson line sectors | OPEN |
| Regular rotating 5D Earth interior/exterior and LARES 2 nodal comparison | OPEN |
| Agda kernel certification | OPEN |

Highest-alpha next work: construct the charged mass spectrum and Wilson-line potential **in the same compactification**, include graviton and gauge corrections in the one-loop potential and retune physical couplings if possible; then solve coupled slow-rotation fields for a conservative Earth fluid before producing a quantitative satellite prediction. Existing formal BIDI owner `KKSteelmanBidirectionalConsumerExact.agda` remains authoritative; no new generic transport framework. The exact analytic positive-series result is described here but is not yet kernel-certified.

## Reproduction

```bash
python3 scripts/check_kk_casimir_bidi_consumer.py
python3 scripts/check_kk_neutral_source_reduction.py
python3 scripts/check_kk_jordan_sourced_sphere.py
```

Local Python/SymPy/mpmath verification passed; the scripts are committed to PR #1241, exact-head Agda compilation and full 5D numerical source solution are not claimed.


## Stronger radius-independent strict-geometric-photon obstruction

The previous comparison of g_KK with the observed electromagnetic coupling is *weaker* than the following same-theory mass/charge test. For a free 5D scalar/fermion mode with nonnegative bare bulk mass squared, periodic fifth momentum n/b0 gives `m4,n²=m5²+(n/b0)²` and canonical geometric U1 coupling `q_n=sqrt(2)*n/(M_Pl*b0)`. Therefore for all n and b0,

`|q_n|/m4,n <= sqrt(2)/M_Pl`.

For an electron, `e/m_e ~ 592.608 GeV^-1`, versus `sqrt(2)/M_Pl ~5.808e-19 GeV^-1`: a factor ~`1.02e21` in the wrong direction. This is not repaired merely by changing the radius! It is the classical KK **unrealistic charge-to-mass / Planck mass problem**, consistent with the original literature and the modern review by João Baptista, *Test particles in Kaluza–Klein models* (2025), DOI `10.1088/1361-6382/ad9b67`. Domain: minimally coupled non-tachyonic 5D mode with standard spacelike KK momentum and no tuned mass cancellations / brane-localised or exotic matter. It is NOT a theorem excluding all higher-dimensional unification or the separately introduced Maxwell B_mu.

Executable: `python3 scripts/check_kk_geometric_charge_mass_nogo.py`. Local symbolic reduction and high-precision charge/mass magnitude checks passed.

**Revised physical decision:** treat the graviphoton A_mu as a mathematically interesting, ultraweak independent U1 (not QED), and B_mu as the massless photon in the explicit three-Dirac + scalar + Maxwell + gravity candidate. Claiming original geometric EM unification is *not* supported without a new matter mechanism defeating this precise no-go while preserving the experimental consumer.
