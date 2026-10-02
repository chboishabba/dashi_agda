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
