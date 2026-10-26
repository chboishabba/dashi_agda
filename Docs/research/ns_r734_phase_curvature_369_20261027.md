# R734 / R92 / NS369: spectral-weight curvature and phase-complete acceptance cut

**Date:** 27 October 2026. **Owners:** original R734 dyadic critical observable, R92/R102 helical triad conservation, NS369 periodic physical Fourier orientation/ternary sign quotient. **Proof status:** exact finite-mode symbolic regression of *the same* full projected Galerkin source; no kernel-checked Agda theorem, uniform continuum coercivity, or Clay result. New file: `tests/test_ns_r734_phase_curvature.py` (four matching local SymPy tests passed).

## Exact same physical Waleffe triad and arbitrary radial weights

Use the exact previously verified six-mode real divergence-free pure-H+ field from PR #1271, modes `p=(1,0,0),q=(0,1,2),k=(1,1,2)`, conjugate negatives, Galerkin cutoff `N=2`. In the order `p,q,k`, wavevector lengths are `a=1,b=sqrt(5),c=sqrt(6)`. The *actual paired modal nonlinear energy transfers* are
```
(Tp,Tq,Tk) = A*(b-c, c-a, a-b),
A = (5-sqrt(5)+sqrt(30))/10 > 0.
```
These actual transfers (not a postulated shell surrogate) satisfy the Waleffe kinetic and exact helicity laws:
```
Tp+Tq+Tk=0,
a*Tp+b*Tq+c*Tk=0.
```
For **arbitrary real weights** `(wp,wq,wk)`, the same triad's weighted nonlinear production is **exactly**
```
P_w = A [(b-c)wp+(c-a)wq+(a-b)wk]
    = A(b-a)(c-b)*[
       (wq-wp)/(b-a) - (wk-wq)/(c-b)].
```
Thus the signed production is the drop of the secant slope of the spectral weight across this ordered triad, multiplied by a positive Waleffe amplitude and positive wave-number gaps. This is an **algebraic physical-source criterion**, not a global multi-triad flux bound.

Special cases: constant weights (energy conservation) and exact-radius weights (true helical helicity conservation) both have zero nonlinear production. More generally, `w(r)=x+y*r` yields zero on this all-positive-helicity triad. Conversely, for this nondegenerate three-frequency example, vanishing production requires the three weight samples to lie on such an affine function of radius; equivalently, the two secant slopes match.

For R734's original dyadic `w=(1,2,2)`, the first slope is positive and the second is zero; consequently
```
P_dyadic = A(c-b)
         = (5+sqrt(5)-sqrt(30))/10 > 0.
```
This recovers the previously established physical W2 counterexample and pinpoints its discrete spectral-weight-curvature mechanism.

## Same-spectrum phase reversal — what NS369 forgets

Construct a second *real physical Galerkin datum* by changing the sign of only the coefficients at `k` and `-k`, leaving `p,q` unchanged. This respects reality, solenoidality, pure positive curl-helicity, the original cube cutoff, and every Fourier-mode squared norm. In particular both states have exactly the **same** modal energy spectrum, true signed helicity, initial zero H- mass, R734 critical X=8 and D=36, and all ternary wavevector sign signatures. Only one triadic relative phase changes.

The newly executed **complete physical projected Navier–Stokes convolution** yields
```
(Tp,Tq,Tk)_flipped = -(Tp,Tq,Tk)_original,
P_dyadic,flipped = -P_dyadic,original.
```
Therefore neither the 369 finite ternary sign profile **nor** the complete initial *modal energies plus helicity labels* determines the instantaneous signed dyadic transfer. Any claim to infer a uniquely signed physical production **from only those phase-blind data** is false on this same cutoff. This does not rule out upper bounds for the absolute transfer, a richer phase-resolved Gram representation, or valid time-integrated cancellations.

In particular, the open 369 high-high Gram Rayleigh estimate `lambda_min(K_N(A)) >= c/N` cannot be declared proved or disproved from this triad without matching that owner's **actual same-operator** `K_N(A)` and its admissible phase constraints. The original Round369 same-solution Serrin transport still remains a conditional *consumer*, not the producer of a critical budget.

## Attribution and external comparison

The helical triad transfer/conservation mathematics is **Fabian Waleffe**, *The nature of triad interactions in homogeneous turbulence*, *Physics of Fluids A* 4 (1992), 350–363, DOI 10.1063/1.858309; first-link bibliographic source https://ntrs.nasa.gov/citations/19920038608 . An earlier primary Waleffe technical summary gives the two triplet transfer conservation constraints: https://web.stanford.edu/group/ctr/ResBriefs/1991/05_WALEFFE.pdf . The *specific arbitrary-weight secant identity and actual R734 phase-flip acceptance* are this repository's directly verified algebraic specialisation, not attributed to Waleffe as a verbatim theorem.

Gürcan, Manfredini and Morel, *Solutions of the Navier-Stokes Equation Through Affine Transformations: The Triad Triplet*, https://arxiv.org/abs/2609.20710v1 (17 September 2026), provide an independent recent affine triad-triplet/inviscid analytical donor. It does not provide the full viscous NSE regularity estimate or this R734 lemma. Biferale–Titi's helicity-decimated regularity (https://arxiv.org/abs/1303.1215) applies to a different equation. Palasek's October 2026 axisymmetric circulation criterion (https://arxiv.org/abs/2610.29012) is conditional; neither is unrestricted R734 W2.

**Formalisation/roadmap:** retain the original R92 and R734 theorem owners; this is an exact physically instantiated algebraic test and fail-closed research report. Its direct next payoff is a *phase-resolved* original high-high operator identification, or an independent signed same-solution analytic estimate that pays both intra-H+ curvature transfer and generated H- exchange. Keep the arbitrary-data middle-time W1 gap, R406 source continuum seam, A1/A2/A3 physical attachments and B7 unrestricted continuation **open**.
