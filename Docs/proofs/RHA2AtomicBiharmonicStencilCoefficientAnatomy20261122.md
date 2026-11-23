# RH P0/A2 — Original four-window biharmonic geometry and coefficient provenance (22 November 2026)

**Status:** exact local SymPy algebra PASS; original Lean sources inspected on `chboishabba/dashi_lean4:main`. This note is NOT a Lean/Agda kernel certificate or a proof of RH/GRH, nor a claim that all six analytic commuting faces are paid. Companion regression: `scripts/check_rh_a2_biharmonic_stencil_geometry_20261122.py` (commit `602b2c42`).

## 1. Original owner, not a new source

`Synthesis/RiemannProjectiveQuarticFourWindowAtomic.lean` defines the four centres `c=(0,pi/3,pi/2,pi)` and weights `w=(1,-1,lambda,mu)`. For the actual original on-line cosine moments:

```text
A1 = 1/2-mu;             A2 = 3/2-lambda+mu;
M1/pi² = -1/18-mu;       M2/pi² = 1/18-lambda/4+mu;
J2/pi² = A1*(M2/pi²)-A2*(M1/pi²)
      = -(54 lambda mu+13 lambda-144 mu-8)/72.
```

The coefficient `13/72` is the genuine sampled-moment cofactor
`1/8+1/18=(9+4)/72=13/72`, built from the `pi/2` and `pi/3` squared angular spacings and cosine phase values. The algebraic identity `13=9+4=3²+2²` is real, but is NOT by itself a Pythagorean metric theorem. On `J2=0`:
```text
mu0(lambda)=(13 lambda-8)/(144-54 lambda)
mu0(1/2)=-1/78, mu0(2/3)=1/162.
144-54*(1/2)=117=3²*13; 351=3*117=3³*13.
```
**117 and 351 are composite, not prime**. Their shared prime 13 is forced by this projective moment determinant and endpoint elimination, not an independent RH invariant.

`Synthesis/RiemannProjectiveQuarticFourWindowPoleSameObject.lean` defines the ORIGINAL finite pole weight `cosh(8x/t)*cos(16x)*cos(cx)`, with atomic high-pole P1=9/8 at lambda=1/2 and P2=1 at lambda=2/3. `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleTarget.lean` uses the projective wedge `P2*profileHalf-P1*profileTwoThirds`. The original normalized projective profile at atom c is `4*w(c)*(A1*cos(2c)-A2*cos(c))`. Its endpoint vectors are

```text
half:       [-74/39, 3,    -40/39,   -1/13]
two-thirds: [-112/81, 8/3, -320/243, 8/243]
P2*half-P1*twoThirds =
            [-40/117, 0, 160/351, -40/351]
          = (40/351)*[-3,0,4,-1].
```

The `pi/3` coordinate is a **projective rank-one cancellation**:
`1*3-(9/8)*(8/3)=0`. Both incoming source contributions are NONZERO, and their observed difference vanishes. This is not scalar zero of the source, not an actual zeta zero, and not an empty C3 phase orbit.

### Where the numerator 40 comes from — exact cofactor, not a fitted scale

The raw selected `40` also has a direct original projective origin. Upon substituting the SAME atomic `J2=0` root into the cosine columns, local exact SymPy gives

```text
A1(lambda)=1/2-mu0(lambda)
          =40*(2-lambda)/(144-54lambda),
A2(lambda)=3/2-lambda+mu0(lambda)
          =2*(2-lambda)*(52-27lambda)/(144-54lambda),
A2/A1=(52-27lambda)/20.
```

Thus `40` is a **cofactor of the original J2-null on-line moment**, arising algebraically from the sampled `(0,pi/3,pi/2,pi)` cosine matrix. It survives the endpoint projective wedge, and the fourfold `160=4*40` then comes from the folded fourth-difference coefficients. Its value changes with weight/normalization conventions, unlike the relative binomial fourth-difference geometry.

## 2. Exact negative square / folded fourth difference

The surviving atoms are `c=0,h=pi/2,2h=pi`; the missing `pi/3` site carries exact observed zero. Write `evenAtom(c)=(delta_{+c}+delta_{-c})/2` (with `evenAtom(0)=delta_0`). The signed atomic high-pole projective carrier is

```text
sigma=(40/351)*[-3 evenAtom(0)+4 evenAtom(h)-evenAtom(2h)]
     =(20/351)*[-delta_{-2h}+4delta_{-h}-6delta_0
                 +4delta_{+h}-delta_{+2h}].
```

This is the **negative 5-point discrete biharmonic stencil**
`-(20/351)*(1,-4,6,-4,1)`; equivalently the negative square of the centered discrete Laplacian Fourier symbol. The FULL EXACT real cosine Fourier response at this *atomic high-pole vertex* is

```text
F(q)=(40/351)*[-3+4cos(pi*q/2)-cos(pi*q)]
    =-(80/351)*(1-cos(pi*q/2))²
    =-(320/351)*sin(pi*q/4)^4 <=0 for every real q.
```

Consequences independently checked with SymPy:
- `F(q)=0 iff q in 4Z` for real q. These are **Fourier-notches, NOT zeros of ζ(s)**.
- `F(1)=-80/351<0`; `F(4)=0`; the fourth-order notch is
  `F(4+xi)=-(5pi^4/1404)*xi^4+O(xi^6)`, exactly the previous atomic moving-q boundary term.
- The symmetric five-node stencil has vanishing raw polynomial moments of degree 0,1,2,3, and nonzero fourth moment. The one-sided even folded mass has `M0=M2=0`.
- `M4=-10pi^4/117`, `S=-M4/4=5pi^4/234`, `M6=-25pi^6/234`, and
  `L=5pi^5*(cosh(pi/2)+8cosh(pi))/351`.
  The 8 in L follows from fifth powers of the distance ratio `pi/(pi/2)=2` together with the relative atom weights. These are geometry-dependent source invariants at the specified vertex, not universal primes.

**Important nonpromotion:** for the ORIGINAL positive-radius compact bump and finite t, the exact factorization `F<=0` does not persist automatically; earlier source-specific calculations find a positive smoothed finite-t q=4 response. The 8-vertex / 12-map / 6-face indexed cube must label atomic-to-smooth, high-to-finite pole and horizontal reflection separately; no global analytic commutation is inferred. Balanced ternary sign and actual ζ-zero/multiplicity remain distinct from observer cancellation. The Fourier notch has period 4, not an established C3/369 group isomorphism.

## 3. Asymptotic A2 constants are mostly integration and proof-envelope constants

Original `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleA2ScalarAudit.lean` defines `LocalPositiveDebt` and `MuGain`. Original `...SignedPolePostSixthAbsorb.lean` supplies the capped sixth phase `(3/20)*pi^6` with `6!=720`, and conservative eighth physical envelope with leading `r^8/17000`. Put `v=t/16`, `eta=1/(pi+1)`, `r=eta*v`, `ell=log(t)/(2pi)`, `N(t-r-1,t+r)~2r*ell`. The leading terms in the local scalar are

```text
MuGain  ~ S/(6 v^6)*(2/5)*r^5*ell
        = eta^5*ell/v * S/15.
M6 debt ~ ((3/20)*pi^6)/(6!*v^8) * r^6*(2r*ell)
        = eta^5*ell/v * pi^6*eta²/2400.
M8 debt ~ (pi+1)^2*L/(v^10) * (r^8/17000)*(2r*ell)
        = eta^5*ell/v * L*eta²/8500.
V4/log errors and r²N charges are lower order here.
```

Thus the signed local leading bracket is
`-S/15+pi^6*eta²/2400+L*eta²/8500`.
The coefficient anatomy:
- `15 = (6*5)/2`: 1/6 from the quartic-jet source, 1/5 from integrating the vertical fourth moment, 2 from the two symmetric sides (NOT the separate binomial 15 in Re(a+i d)^6).
- `2400 = 720*20/(3*2)`: 720=6! Taylor normalization, 3/20 the **conservative selected M6 cap**, and 2 the two-sided window count.
- `8500 = 17000/2`: 17000 the source's **chosen eighth-remainder majorant**, and 2 again the two-sided window. The 17 in 17000 is NOT a geometric index.
- Multiplication by 15 to isolate S gives `160=2400/15` and `15/8500=3/1700`; hence `S>pi^6*eta²/160+(3eta²/1700)L`. No independent geometry produces 160 or 1700.

**Two different appearances of 160 must NOT be equated.** The positive atomic coefficient `+160/351` comes from folding the `+4` binomial difference against the `40/351` projective scale. The **denominator 160** in the leading A2 strength threshold comes from `2400/15`, where `2400` is a Taylor/M6/count envelope and `15` an integrated mu-gain coefficient. They coincide numerically but occupy distinct typed source/consumer layers; no claimed commuting map identifies them. The analogous two `15` occurrences (sixth-phase binomial vs fourth-moment integration denominator) are likewise distinct.

**Source proof slack, demonstrating non-invariance:** in `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleEighthRemainder.lean`, the sixth-degree scalar cosine bound is `q^8/35840`; the truncated cosh factor is at most 2, giving an intermediate `q^8/17920` bound. The final proof relaxes this to `q^8/17000`. A tighter eighth envelope using the already-proved intermediate estimate could replace `17000->17920`, hence `8500->8960`, `1700->1792`, without altering the five-point geometry; this tightened envelope is a **proposed source proof weld, not a new Lean theorem accepted here**. The binomial coefficients `15=C(6,2)=C(6,4)` inside the complex sixth phase ARE angular-polynomial geometry, unlike the denominator 15 of the mu gain.

## 4. Which objects are geometrical?

**Intrinsic to the selected atomic source:** sampled angular columns and their projective determinant; observed vanishing pi/3 column; the *ratio* (-3,0,4,-1); folded five-point fourth difference; the exact negative-square Fourier symbol and 4Z notch. The 13 cofactor is a discrete angular-moment value for this exact grid.

**Normalization-dependent:** the overall factor 40/351, coefficients 117/351, 234 in the target strength, t/16 scaling, and the support cutoff eta=1/(pi+1).

**Proof-bound choices:** 3/20 capped sixth norm and 1/17000 eighth absolute majorant, hence the derived 2400/8500/160/1700 after count/integral normalization. These can change under sharper inequalities without changing the geometric source.

**P0 is not closed:** the source's same-object A2 strict comparison with signed `FarExact`, actual-zero multiplicity, mu integral, target defect and slack is UNPAID; no six-face analytic theorem or RH/GRH proof follows.
