# A runnable three-sector nonabelian gauge simulator: experimental protocol and validation

Date: 2026-10-25. Code:
- scripts/alexander_horned_c3_finite_SU2_gauge_simulator.py
- scripts/test_alexander_horned_C3_gauge_simulator.py
- scripts/alexander_horned_C3_three_channel_SU2_actor.py
- scripts/alexander_horned_C3_same_object_separator_atlas.py

Original mathematical provenance: Alexander 1924 and Hatcher
*Algebraic Topology*, Ex 2B.2; Klein/Hamilton binary icosahedral
unit quaternions; standard group holonomy/flat connection
correspondence. Relevant PRIOR experiments (not OUR measurements):
Sugawa et al. 2021 DOI 10.1038/s41534-021-00483-2 and
Liang et al. 2024 DOI 10.1038/s41567-024-02644-4.

## 1. Exact ideal gates and per-stage free graph

At depth n, use a programmable rose graph with
3*2^n marked loops, indexed by (sector, binary address).
This is a finite SYNTHETIC graph, not the smooth complement
of a finite tame 3-ball. The parent meridian loop is
identified under refinement with the child commutator
  x_(sector,w) -> [x_(sector,w0), x_(sector,w1)].

The executable simulator constructs all 120 unit
binary-icosahedral quaternions over Q(phi),
phi=(1+sqrt(5))/2, from their 8+16+96 coordinate
families. It explicitly checks closure and inverse.
Enumerate every commutator and choose section
  section : 2I -> 2I×2I
with comm(section(g))=g for all 120 elements.
Choose q=(1+i+j+k)/2, order 6, q³=-1. A root
pair (a,b) with [a,b]=q and <a,b>=2I exists
and is selected algorithmically. Generate depth-n
labels by evaluating section at all child nodes.
This yields an honest compatible SOURCE group map
G_A->2I at arbitrary n, and three independent
copies give G_A*G_A*G_A -> (2I)^3.

All ideal SU2 traces are computed from unit quaternions;
control noise and measurement shots alone are floating
point. A root marked loop at depth n is a freely reduced
word of length 4^n; the root-cube test therefore uses
3*4^n physical elementary gates.

## 2. Three-channel full C3 finite-unitary actor

A 2I element acts faithfully on a complex spin doublet
via its quaternion matrix
       [[a+ib, c+id],
        [-c+id, a-ib]],
a unit-determinant SU2 matrix.

Three independent channels produce a faithful representation
  (2I)^3 rtimes C3 -> U(6).
The external C3 cycles the three 2D channels; the
j-th group factor acts on the destination j-th block.
The selected root cube in the first channel has
  diag(-I2, I2, I2) != I6.
The 2026-10-25 local Python test validated all 120
unitary matrices and 300 exact-group / numeric-matrix
product comparisons plus semidirect actor associativity.
This is the directly lab-oriented analogue of the
previous 12D F7 modular actor. Do not conflate their
coefficient fields or dimensions.

## 3. Measurements and falsifiers

Use a controlled-U / reference-arm interferometer with
an effectively maximally mixed spin probe. An X-basis
ancilla readout has expectation Re Tr(U)/2, the
normalized SU2 Wilson trace. For q³=-I that is -1;
for commuting U1 transport it is +1.

Matched controls:
(A) commuting U1 gates -> all commutators I;
(B) Q8 i,j -> one-step [i,j]=-I, but Q8 cannot
    support compatible noncentral descendants because
    [Q8,Q8]={±I};
(C) full 2I recursive assignments -> q³=-I at
    each tested depth and exact compatibility;
(D) scrambled child pairs -> detect broken recursion;
(E) zero-gate-angle / identity -> control for readout drift.
Wilson trace is invariant under simultaneous global
gauge conjugation, verified in local tests.

**Readout limitation:** q and q^-1 have the SAME
SU2 Wilson trace; reversing loop orientation is
not distinguishable by that scalar trace alone.
Full gate tomography or a calibrated frame-sensitive
measurement distinguishes matrices but is not gauge
invariant in the same way. Do not advertise a
direction-sensitive Wilson-trace result.

The local stochastic model puts independent random
axis-angle perturbations on each physical gate and
samples the controlled-U readout with Bernoulli
shot noise. Exact ideal q³ remains -I for all
tested depths. For one seed, 1.5deg Gaussian gate
angle noise, 50 trials, 300 shots/trial:
 n  gates  observed halftrace
 0      3  -0.9999
 1     12  -0.9995
 2     48  -0.9955
 3    192  -0.9828
 4    768  -0.9437
 5   3072  -0.8032
These are numerical SAMPLE estimates, not a
device specification or general universal
error-scaling theorem. The knobs, PRNG seed and
trial counts are explicit and reproducible.

## 4. Geometric same-object and flat connection bridge

The paper-level geometric existence proof:
Docs/topology/AlexanderHornedC3SameObjectGluingTheorem20261025.md.
Given the original SUPPORTED Hatcher/Lippert wild
ball, the threefold boundary-connected sum through
actual collars and sphere cuts has exterior
G_A*G_A*G_A, with outer C3. The new explicit
stereographic atlas trivializes each cut overlap,
and its Python source checks the chosen same-object
round-cap/tube/sphere coordinates.

The standard flat-holonomy theorem gives a stronger
MATHEMATICAL statement: for any smooth connected
E with pi1(E)=G, a hom rho:G->SU2 is realized
by the associated FLAT principal SU2 bundle
       P_rho=(E_tilde×SU2)/G.
Its flat connection has holonomy rho. Since E
is an open subset of R3, this is an auxiliary
gauge connection, NOT the inherited Euclidean
Levi-Civita spin connection. Nontrivial flat
monodromy does NOT require a nontrivial spin
structure. Source: Goldman–Millson (1988) and
standard holonomy/reconstruction theorem.
For the three channels use SU2^3 and the
C3-permutation structure group, not a spurious
single universal 2D spin actor carrying all factors.

A finite ideal rose graph also carries the prescribed
representation, but DOES NOT establish the infinite
wild-space topology or local flatness of an
experimental condensed-matter medium. A physical
emulation of a nonabelian gauge lattice needs
independent calibrated plaquette-flatness controls.

## 5. Acceptance and current phase

COMPLETE (actual executed local Python, equivalent to
repo scripts): 120/120 exact 2I commutator sections;
q³=-1; depth 0..5 ideal SU2 consistency; noisy
Wilson readout and control comparisons; three-channel
6D complex actor; gauge conjugacy invariance and
orientation caveat; explicit Euclidean sphere
stereographic overlaps, cap collar coordinates.

CLASSICAL PAPER PROOF: an actual C3-invariant wild ball
exists via supported Alexander/Hatcher/Lippert seeds
and standard boundary-sum/relative-collar/van Kampen
theorems. The full indexed infinite coordinate
embedding and all topological maps are NOT formalized
in repo source or kernel, and are not numerically
verified by finite sampling.

NOT COMPLETE: no laboratory interferometer operated;
no physical CAD handlebody X_n fabricated in this
round; no Maxwell/Dirac self-adjoint operator on a
finite specimen; no new measured wild-topology effect.
Agda compilation and CI were deliberately not
performed at user request.

NEXT EXPERIMENTAL DEPENDENCY: actual platform choice,
2I gate compiler/calibration, detection scheme,
per-loop error budget, matched commuting and
noncommuting controls and independent flatness audit.
NEXT FORMAL GEOMETRIC DEPENDENCY: encode the supported
infinite horn maps and relative collar/sliding
homeomorphisms in the native topology development.
