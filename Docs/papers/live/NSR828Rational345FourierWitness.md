# R828: exact rational 3-4-5 finite-Fourier obstruction to universal W2 reserve

**Scope**: independent finite-mode Fourier calculation and elementary finite-ODE
continuity / quantitative enclosure. This is a negative-control test for the
proposed **auxiliary** R823 universal signed W2 payment, not a solution or
counterexample to the Navier–Stokes equations.

## 1. The genuinely physical finite Fourier field

Take the radius-four cube
\(\Lambda_4=\{k\in\mathbb Z^3: |k_j|\le4\}\setminus\{0\}\)
(728 nonzero modes) and viscosity \(\nu=1\). Set

\[
\begin{array}{ll}
u_{(3,0,0)}=(0,2+2i,-2-i),&
u_{(0,4,0)}=(2+2i,0,2+2i),\\
u_{(3,4,0)}=(6i,-9i/2,-2+2i),&
u_{-k}=\overline {u_k},
\end{array}
\]

and all other coefficients to zero. Every coefficient satisfies
\(k\cdot u_k=0\), and the field is real and mean-zero.

Define the true finite Fourier projected quadratic nonlinearity

\[
F_k(u)=-i P_k\sum_{p+q=k}(q\cdot u_p)u_q,\qquad
P_k=I-\frac{k\otimes k}{|k|^2},
\]

and the **actual real-time** polynomial ODE

\[
\dot u_k=-|k|^2 u_k+F_k(u),\quad k\in\Lambda_4.
\]

The finite ODE is locally well-posed over real time and preserves conjugate
reality and transversality. It is *not* asserted to be a nonconstant function
from connected real time into the rational field \(\mathbb Q\).

## 2. Fully expanded helicity and coherent-work normalization

On all modes that enter a nonzero evaluated term, \(|k|\) belongs to
\(\{3,4,5\}\); no \(\sqrt2\) or irrational field element is needed to
evaluate the initial snapshot. Use

\[
H_k^\pm v=\tfrac12\left(P_kv\pm
   \frac{i\,k\times v}{|k|}\right).
\]

Compute the mixed outer cell \(M_k=\sum_{p+q=k}H_p^+u_p\times H_q^-u_q\)
and the R230 signed commutator slot

\[
G_k=\sum_{p+q=k}
\left(H_p^+F_p\times H_q^-u_q-
      H_p^-F_p\times H_q^+u_q\right).
\]

The complete R692-style coherent work is
\(C_{\rm comm}=2\Re\sum_k\langle M_k,G_k\rangle\).
Use the same dyadic weight \(w_k=2^{\lceil\log_2\|k\|_\infty\rceil}\)
as the selected critical Fourier fold. The energy-production and viscous
rates are
\[
P_{\rm crit}=2\Re\sum_k w_k\langle u_k,F_k\rangle,\qquad
d=\sum_k w_k|k|^2|u_k|^2.
\]

The exact rational calculation gives

\[
C_{\rm comm}=-557627/125,\qquad
P_{\rm crit}=0,\qquad d=15834.
\]

The external product-rule version independently agrees with the commutator
work (rather than assuming that agreement by naming).

At canonical margin \(\delta=\nu=1\), the proposed R815 complete signed
rate convention reduces to

\[
\mathcal P(0)=6(12C_{\rm comm}-P_{\rm crit}+d)
   =-28273644/125<0.
\]

The sign is exact. It is stronger than the older R827 result in one
particularly important respect: the *active helical data* are rational.

## 3. Independent rational short-time certificate

For a vector component supremum bound \(\|u\|_\infty\le M=12\),
take the 728-mode conservative bounds

- Leray projection coordinate row sum <=4;
- helical projection coordinate row sum <=3;
- Fourier dot-factor <=12;
- squared mode length <=48;
- initial component supremum <=6.

These yield an explicit polynomial-ODE derivative bound
\(K=5032512\) and a Lipschitz constant for the displayed *complete
signed rate* \(L=391309593930357307785216\). Set

\[
T=\frac{226189}{3938540454339300631433585885184}>0.
\]

An exact integer/rational bootstrap then gives \(\|u(t)\|_\infty<12\)
and

\[
\mathcal P(t)\le-226189/2<0
\qquad(0\le t\le T).
\]

Therefore the ordinary real-time finite ODE solution has

\[
\boxed{\int_0^T\mathcal P(t)\,dt<0.}
\]

The proof uses no sampled numerical trajectory. The runnable, independently
checked arithmetic is
\`scripts/check_ns_r828_rational_345_fourier_witness.py\`.
The interval is deliberately extremely conservative.

**Precise boundary:** to infer failure of the Agda
R823/R815 *selected* payment, source-write/kernel-check an exact bridge
from its R692/R723 scalar to the above (explicitly defined) Fourier
scalar. Without that theorem the proven counterexample is to the
standalone Fourier signed functional, with the transfer a mathematical
claim under audit. A negative auxiliary payment does not refute NS.

## 4. Why a direct R408 Agda constructor is NOT a routine cast

The live R408/R820 specialization explicitly fixes
\`F = Rational.rationalRealField\`, and its helical projector
interface requires \`PeriodicHelicalProjectorLaws\` **for all lattice
modes**. For the genuine helical projector at (1,1,0), the normalization
requires \(\sqrt2\), not contained in \(\mathbb Q\).
Choosing a Pythagorean seed removes radicals from the *evaluated active
snapshot*, but does not construct this globally quantified rational
projector record. Moreover a nonconstant continuous physical ODE
trajectory cannot take values in \(\mathbb Q\) at every real time.

Consequently, a literal non-vacuous full R408 real-time instantiation
requires one of:

1. generalize the time-dependent exact physical stack from rational
   coefficients to a genuine ordered real scalar field, including the
   integration and differentiated trajectory, then prove the actual
   helical projector laws; or
2. extract a separate finitely supported **instantaneous** witness
   theorem at the rational physical state and transport it through a
   conventional real finite-ODE existence/continuity theorem, without
   pretending to supply the impossible global rational helical record.

Neither is completed just by adding another conditional compiler.
The highest-value next step is to certify a kernel-checked rational
*instantaneous* evaluator and its normalization against the R692/R723
source. The standalone classical real ODE continuity proof is supplied
above, subject to the identical-quantity bridge.

## 5. ABCD consequence

B: if the same-object link succeeds, the universal R823 integrated
payment is false on its advertised unrestricted initial-data class.
Change the auxiliary B proof route; preserve the exact orbit identities,
the independent W1 investigation, and the alternative earlier B1–B7
signed/resolvent routes. Do **not** call this an NS counterexample.

A: the separate Euclidean resolvent/majorant proof remains independent.

C/D: the externally attributed forced-breakdown source audits remain
independent and are not affected by an unforced periodic auxiliary
estimate failing.

Machine evidence is an aid to verification, not self-certifying
mathematical authority. No Clay completion or exact-head Agda kernel
receipt is asserted.


## 6. R829/R830 follow-through

The next tranche removes two further bookkeeping ambiguities without claiming
the remaining physical identification.

### R829 finite component certificate

`scripts/check_ns_r829_rational_345_component_certificate.py` expands the
snapshot into its exact nonzero rows.  The fixed-output coherent-work
contributions, in lexicographic output order, are

[
-48,quad
rac{322917}{250},quad
-48,quad
-rac{428272}{125},quad
-rac{428272}{125},quad
-48,quad
rac{322917}{250},quad
-48.
]

They sum exactly to

[
-rac{557627}{125}.
]

The six nonzero initial velocity modes contribute critical production

[
-128,-672,800,800,-672,-128,
]

which sums to zero, and critical dissipation

[
6425,468,1024,1024,468,6425,
]

which sums to (15834).

`NSTriadKNR650Rational345ComponentScalarRound829Exact.agda` kernel-checks
those finite scalar aggregations, and
`NSTriadKNR650Rational345SnapshotNormalizationRound829Exact.agda` derives

[
6left(12C_{m comm}-P_{m crit}+dight)
=-rac{28273644}{125}<0.
]

This closes the factor/sign/multiplicity arithmetic.  It does **not** yet prove
that each emitted vector row is definitionally the value of the live
R230/R692/R744 repository expression.

### R830 exact short-time arithmetic

`NSTriadKNR650Rational345ShortTimeRound830Exact.agda` records the exact
positive horizon and strict-negative integrated upper bound.  It deliberately
leaves real finite-dimensional ODE existence/continuity as an analytic
interface rather than manufacturing a rational-valued continuous trajectory.

Consequently the R823 decision route now has exactly two substantive leaves:

1. reify the finite component table against the actual R30/R230/R692/R744
   definitions on the selected radius-four state;
2. instantiate a genuine real-time finite Galerkin ODE and transport the same
   selected signed scalar over the certified interval.

Once both are discharged, the universal R823 reserve conjecture is refuted.
No conclusion about Navier--Stokes regularity itself follows.

## R850–R852 mathematical closure update (23 October 2026)

The prior description above of R829D as a remaining physical vector/scalar
identification has been superseded by theorem-bearing work:
- R841 constructs a *literal* rational radius-four Field30 physical snapshot,
  with actual all-mode sparse velocity and transversality.
- R844/R845/R846 evaluate the selected physical projected nonlinearity,
  mixed helicity vectors and commutator vector rows.
- R847 proves literal critical production = 0 and dissipation = 15834.
- R848 proves every **nonzero** inactive output has an empty selected
  mixed-cell fibre.
- R849 proves literal global R692 coherent work = -557627/125.
- R850 proves exact same-object identification of the three physical
  scalars and the negative initial R815 rate.
- R851 makes R845's all-mode forcing-same-object theorem unconditional for
  the selected snapshot by splitting **zero-output transverse cancellation**
  (existing R436) from **nonzero-output support emptiness** (existing R848).
  Crucially, the older R846 universal support-empty premise was **false at
  zero**: six nonzero seed pairs (p,-p) sum to zero. Their projected NS
  contributions vanish, not their incidences.
- R852 composes R851.modalSameObject, R837 full-to-active fold conversion,
  R845 mixed vectors and R846 literal commutator vectors to construct the
  exact R829D `Repository345VectorEvaluation` record, including all eight
  mixed/commutator rows and six velocity/forcing pairs.

Consequently the preferred R832 reserve decision now has one *coarse* open
mathematical leaf: R833 real finite-Galerkin ODE transport. Its finer
prerequisites remain the physical real quadratic/chart identification and
the selected R828 displacement/rate functional along a real local solution.
This is an **auxiliary R823 signed-reserve decision**, not Clay B.

Source-written new modules are NOT exact-head Agda kernel receipts. A local
independent support enumerator was run: six opposite active pairs produce
zero output and all nonzero active sums inside the radius-four cube lie in
the eight selected modes. The committed regression is
`tests/test_ns_r851_zero_output_support.py`.

Do not reopen already established R829 scalar/vector producers or impose the
impossible zero-output empty-incidence condition.


## 7. Canonical real-flow max-cut — no new RNNN encoding (2026-10-23)

**Repository archaeology:** The canonicalization effort was already completed in
merged PR #1232 (`NSCanonicalClayResidualExact.agda`; historical Round
packages are not automatically canonical proof obligations). Earlier
finite-flow analysis is already in the literal projected RHS, Round71 fixed
finite reality field / degree-two theorem, Round74 slot chart and
local-Lipschitz majorant, Picard transport, and the independent rational R828
finite-time bounds. The exact instantaneous *physical* signed observable
is now represented by the R847/R849/R850 theorem chain and the R851/R852
selected vector correspondence (the latter source-written, kernel-unchecked).

### A real mathematical theorem, without another coordinate compiler

Let `Λ` be the 728 nonzero lattice modes in the radius-four cube. Work on
the finite **real** vector space of complex Fourier coefficients, subject to
`u(-k)=conj(u(k))` and `k·u(k)=0`; the usual full real coordinate ambient
space can equivalently be used, with these conditions invariant for the
projected equation. Fix viscosity 1 and define

```text
F_k(u) = -|k|² u_k - i P_k sum_{p+q=k} (q·u_p) u_q
P_k    = I - k⊗k / |k|²
du/dt  = F(u).
```

The mode list is finite, `|k|²` is a positive integer at every retained
nonzero mode, and all coefficients in `F` are fixed real/complex numbers.
Therefore `F` is a real polynomial map of degree at most two. Standard
finite-dimensional Picard–Lindelöf yields a unique continuously
differentiable local real-time solution `u(t)` through the rational initial
seed. Fourier reality and transversality are preserved by the literal
projected nonlinearity and diagonal viscous term.

Define the **physical real-valued signed observable** `ρ(u)` using the
full real helical projectors

```text
H_k^±(v) = (P_k v ± i (k × v)/|k|)/2
```

and exactly the coherent-work, critical-production and dissipation folds
specified in Section 2, on the complete fixed cutoff. The denominator
`|k|` is well-defined for every retained nonzero `k`; some of these
values are irrational, **which is why the real scalar field is essential**.
All folds are finite; their terms are compositions of fixed real-linear
maps and polynomial operations. In particular, `ρ` is continuous (indeed
polynomial, given the finite fixed real helical coefficients).

At the selected initial state `u₀`, only active modes with lengths
3, 4 and 5 enter the nonzero helical calculations. The **same-object
initial evaluation**, if the literal real-lift conventions match the
already-proved R850/R849/critical-fold reductions, gives

```text
ρ(u₀) = 6(12·(-557627/125) - 0 + 15834)
      = -28273644/125 < 0.
```

Since `t ↦ ρ(u(t))` is continuous and strictly negative at `t=0`,
there exists a real `ε>0` such that it remains negative on
`[0,ε]`. Thus

```text
∫₀^ε ρ(u(t)) dt < 0.
```

For the stronger explicit witness, the already-proved conservative bounds
in Section 3 give `K=5032512`, `L=391309593930357307785216`, and
`T=226189/3938540454339300631433585885184`, with
`L K T = 226189/2`. The initial rate is strictly below
`-226189`, so `ρ(u(t))≤-226189/2` over `[0,T]`, and the
integral is strictly negative. No numerical integration or new analytic
PDE estimate is required for this **classical finite-dimensional result**.

### Exact remaining proof-assistant obligation

The historical R823/R831 abstraction fixes
`F=Rational.rationalRealField`, `Time→ℚ` and
`integrateTo : (Time→ℚ)→Time→ℚ`. That is **not** the above physical
real-time trajectory or its real-valued integral. Connected real time
cannot carry a nonconstant continuous rational-valued trajectory.

Thus the remaining task is **one non-round, source-specific transport**:
identify the full real, finite-mode physical signed observable at the
initial seed with R850's exact rational evaluation (via `ℚ→ℝ`);
then place the existing signed reserve = complete rate identity,
pointwise in real time, over the *same* real trajectory/integration
functional. Only then can the R831 negative-integral logic be consumed
without an illicit scalar cast.

Do not treat an Agda Boolean flag, a conditional calculus record or the
R823 rational-time authority as a replacement for this transport. Equally,
do not restart Picard existence, degree-two polynomiality, R829 scalar
arithmetic, or the old impossible zero-output empty-incidence premise.
The auxiliary universal reserve would be refuted after the exact
real-source interpretation is certified; this does not prove or disprove
the Clay unforced periodic regularity alternative.

**Verification boundary:** The real finite-ODE proof above is classical
mathematics using the displayed polynomial RHS; the same-object transfer
into the historical R823 Agda predicate is **not kernel-certified**.
The canonical A/B/C/D proof scheduler remains fail-closed.


### 2026-10-24 Lean real-scalar theorem connection

Verified the previous hidden code path: the real analytic companions are in
`dashi_lean4/NSBControl/Rational345LocalODE.lean`,
`Rational345QuadraticODE.lean`, `Rational345ShortTime.lean` and
`Rational345ReserveWitness.lean`, all included in the opt-in
`NSBCyclicOrbit` library. The earlier assertion that they could not be
located was a *wrong-path search*, not missing mathematical work.

New theorem terms in the EXISTING Lean short-time file:
`Rational345RealSource.snapshot_rate_real_exact`,
`Rational345RealSource.exists_real_negative_signed_integral` and
`Rational345RealSource.negative_real_integral_refutes_reserve`.
These compose an exact rational seed cast, real local quadratic-flow
existence, continuity-based negative real integral, and the real-valued
reserve contradiction without an unnecessary fixed-horizon bootstrap.

The remaining physical proof is the **one** exact source-instantiation
equating the literal radius-four real Fourier ODE and signed helical
observable to the Lean field/rate and equating the R823 integrated payment
to that **same real integral**. A proof that a chosen scalar is negative
at t=0 without the full real Fourier formula is insufficient. No claim of
a Lean kernel build or Agda R823 physical counterexample is made.
