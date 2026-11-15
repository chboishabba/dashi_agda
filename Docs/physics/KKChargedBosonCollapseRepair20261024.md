# KK Casimir critical path: charged-boson repair of the collapsing circle (2026-10-24)

**Branch**: PR #1241, `lares2-kk-observable-maxcut-20261023`. **Canonical executable**: `scripts/check_kk_charged_boson_global_repair.py` (mpmath/SciPy/NumPy). **Predecessor**: `scripts/check_kk_charged_wilson_bidi.py`, containing an explicit metastable/collapse counterexample. **BIDI source owners**: existing `DASHI/Physics/Gravity/KKSteelmanBidirectionalConsumerExact.agda` and canonical DASHI consumer transport/refinement modules.

**Classical/literature source root:** Abe, Inami, Kawamura and Koyama, *Radion stabilization in the presence of Wilson line phase*, PTEP 2014 073B04 (2014), DOI 10.1093/ptep/ptu097, arXiv:1404.5125. They derive the Einstein/Maxwell/charged-and-neutral one-loop radion/Wilson potential and the complex charged scalar contribution; our explicit spectrum/roots are our scoped computational example, not source-reported data. Historical stabilisation: Rubin–Roth (1983), DOI 10.1016/0370-2693(83)91629-5, and Appelquist–Chodos (1983), DOI 10.1103/PhysRevD.28.772.

## SAME action/spectrum, controlled one-loop EFT

Take a five-dimensional compact circle of physical radius b with:
- 5D Einstein gravity, massless independent Maxwell B_A, a neutral massless periodic real scalar: combined `-9` 5D Casimir polarization units (including graviton five, Maxwell three, scalar one).
- Three neutral periodic massive 5D Dirac fermions with mass mN: `+12` units.
- One periodic massive Maxwell-charged Dirac fermion with mF=4 mN and unit charge: `+4` units.
- One periodic massive Maxwell-charged complex scalar with mB=mN and unit charge: `-2` units, **no classical expectation value** (so NOT a Higgs condensate; the Maxwell vector remains massless).
- A renormalised 5D cosmological counterterm tuned to set a local 4D Minkowski vacuum. The actual light chiral electron, Standard Model and strong/nuclear matter are NOT yet included.

Let `z=2pi mN b0`, `x=b/b0`, `theta` the gauge-invariant independent-Maxwell Wilson phase. The regulated winding/Casimir sum is

`f(s,theta)=sum_{n>=1} exp(-ns)(1+ns+(ns)^2/3)cos(n theta)/(zeta(5)n^5)`.

The Einstein-frame 4D zero-mode one-loop potential is

`V_E(b,theta)=c0/b0^4 * U(x,theta)`,
`c0=3 zeta(5)/(64pi^6)`,
`U(x,theta)=ell/x+[-9+12 f(zx,0)+4 f(4zx,theta)-2 f(zx,theta)]/x^6`.

Here the *same charged scalar and charged Dirac couple to the same physical Maxwell holonomy*, not an arbitrarily patched second theory.

## New local solution

Tuning ell to solve `U(1,0)=U_x(1,0)=U_theta(1,0)=0` yields:

- z=**1.285538842524754**, ell=**0.956936504364421**;
- positive U_xx=**22.46588111350565** and U_theta theta=**1.299260538396466**; U_x theta=0 by symmetry;
- the phase theta=0 is the **unique Wilson-angle minimum modulo 2pi at x=1**, by explicit first-harmonic sine-dominance: harmonic-tail/first bound **0.10532264<1**;
- at b0=10^-24 m, radion Compton range approximately **4.484366761e-13 m**, Wilson scalar Compton range **6.484688796e-23 m**;
- charged boson bulk mass **4.03730728e7 GeV**, charged Dirac bulk mass **1.61492291e8 GeV**. These fields are not realistic electrons or light Higgses;
- b0*M5≈**2.893888e6** in the stated physical mass/radius convention.

The independent Maxwell **B_mu** and the distinct KK graviphoton **g_mu5** have no classical vector mass term. The charged scalar is uncondensed, and an Abelian Wilson line does not spontaneously break its own gauge U(1). The Wilson scalar zero mode acquires a loop-generated mass. None of this produces observed chiral matter automatically.

## The decisive repair: remove the prior small-radius collapse along every Wilson phase

The previous no-boson charged theory had

`U(x,pi) ~ (-3/4)/x^6 -> -infinity` as `x->0`.

In the **current** boson-extended theory, as `x->0` all massive periodic Casimir kernels tend to their massless limit. Hence

`x^6 U(x,theta) -> -9+12+(4-2)f(0,theta) = 3+2f(0,theta)`.

Since `|f(0,theta)|<=1` by the triangle inequality and positivity of `1/n^5`, this gives the **uniform lower coefficient bound**

`3+2f(0,theta) >= 1 > 0`.

Therefore the **one-loop potential diverges positively at small radius for every Wilson phase**. This closes the specific UV-side Casimir collapse **within the one-loop formula**. It is not a proof of the ultraviolet completion: at radii near the 5D Planck length the one-loop EFT approximation breaks down. At x->infinity `U~ell/x->0+`.

### Stronger global-minimum consumer

The new script samples the two-variable landscape x in [0.0001,1000], theta in [0,pi] (260x49 grid), and independently optimizes it from 21 initial conditions. Both find the tuned x=1,theta=0 solution as the lowest sampled value (optimizer minimum approximately zero). This is substantial computational evidence of **no deeper finite-radius one-loop minimum**, BUT it is **not** a certified inequality `U(x,theta)>=0` for every real x>0 and every theta. The needed bounded-interval derivative or interval-arithmetic proof of that global inequality remains OPEN. A vacuum tunnelling/lifetime calculation in the full gravity EFT is also OPEN.

Consequently we now distinguish: positive Hessian (verified), asymptotic small-radius repulsion uniformly over Wilson phase (proved by positive-series triangle inequality), numerical global survey (sampled), absolute stability and UV completion (not proved).

## Source/observation consumers and chirality

- The 5D worldline p5=0 -> Jordan matter metric derivation, fixed radion scalar coupling, and sourced uniform-sphere Helmholtz result in PR #1241 still apply at the level of the same 5D gravitational action, with the **new positive** one-loop radion mass inserted. They do not supply a full pressure-supported or rotating material Earth solution.
- The leading `g_tphi` slow-rotation component at fixed Einstein-frame tensor source and bare G agrees with GR to O(GJ); radion corrections arise at higher gravitational order and are exponentially tiny at macroscopic altitudes for this specific mass range. See `scripts/check_kk_chiral_slow_spin_consumer.py`.
- A smooth S1 reduction of a 5D Dirac field is vectorlike; the new heavy charged fermion cannot be an observed light chiral electron.
- S1/Z2 orbifolding can project a chiral component, but projects out the g_mu5 and B5 Wilson zero modes and changes fermion boundary conditions, so it is a NEW physical candidate with a new Casimir action. No silent BIDI transport.
- No experimental claim about LARES-2 follows from this constructed one-loop vacuum.

## Acceptance and attribution

`python3 scripts/check_kk_charged_boson_global_repair.py`
`python3 scripts/check_kk_charged_wilson_bidi.py`
`python3 scripts/check_kk_chiral_slow_spin_consumer.py`

Local independent mpmath/SciPy/SymPy implementations PASS. The new scripts and doc are committed to the current PR. Exact-head Agda compiler and theorem kernel receipts, complete charged/chiral SM, 5D Einstein–source interior/exterior, nonperturbative stabilization, and empirical KK/LARES residual fit remain OPEN. Horned-sphere PR #1244 is an optional *global topology BIDI fixture*, not a requirement.
