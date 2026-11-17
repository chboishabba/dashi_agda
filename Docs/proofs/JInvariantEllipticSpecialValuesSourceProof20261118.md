# Analytic elliptic special values of the original normalized modular j
18 November 2026 — source proof with explicit Agda promotion boundary

## Classical theorem (not a numerical evaluation)

Let tau be in the upper half-plane. With classical normalized Eisenstein
series E4 and E6, write

  Delta(tau) = (E4(tau)^3 - E6(tau)^2)/1728
  j(tau) = E4(tau)^3 / Delta(tau).

The value 1728 refers to the standard modular j, NOT the alternative
Wolfram KleinInvariantJ=j/1728 convention.

Transformation: for gamma=(a b;c d) in SL2(Z),

  E_k(gamma tau) = (c tau+d)^k E_k(tau), k=4,6.

At tau=i, S=(0 -1;1 0) fixes i. Its factor i^6=-1, so
E6(i)=-E6(i), hence E6(i)=0 in characteristic zero.

At rho=(-1+i sqrt(3))/2, ST=(0 -1;1 1) fixes rho since
rho^2+rho+1=0. Here (rho+1)^4=rho^2 != 1, so
E4(rho)=rho^2 E4(rho), hence E4(rho)=0.

The classical product identity

  Delta(tau)=q product_{n>=1}(1-q^n)^24,
  q=exp(2*pi*i*tau), 0<|q|<1,

gives Delta(tau)!=0 throughout the upper half-plane: all factors
are nonzero, and sum |q^n| converges, so their infinite product
converges to a nonzero limit.

Therefore the original normalized function satisfies

  j(i)=1728 E4(i)^3/(E4(i)^3-0)=1728,
  j(rho)=1728*0/(0-E6(rho)^2)=0.

This establishes both special values analytically from modularity
and the discriminant product, not from truncated q-series.

## Agda carrier/source boundary

The new JInvariantEllipticFixedPointCompilerExact imports the
existing actual Eisenstein modular transformation and derives the
E6/E4 vanishing from fixedpoint/factor-cancellation witnesses.

The new JInvariantEllipticStandardJValuesCompilerExact composes
the original normalized standard-j and derives exact 1728 and 0
from these vanishing results plus field/denominator-normalization
witnesses. No desired j-value is an input field.

Their quantified witnesses are not yet inhabited on the literal
Bishop-complex parameter carrier. Outstanding:
- concrete i and rho, and S/ST fixedpoint equations;
- nontrivial scalar factors and field cancellation in the same carrier;
- explicit q-series/lattice E4/E6 same-object identification;
- original normalized Delta=eta^24, nonvanishing and 1728 binding;
- pinned Agda --safe compilation and exact import-graph acceptance.

A pinned Lean companion reportedly proves eta24=normalizedDelta,
recorded in LeanMoonshineDeltaIdentityPinnedReceiptExact. This does
not automatically become an Agda proof or identify a different carrier.

## CM discriminant -163

tau163=(1+sqrt(-163))/2 is NOT elliptic S/ST fixed.
Classical CM states j(tau163) is a root of H_-163(X), and the
class-number-one polynomial calculation is

  H_-163(X)=X+262537412640768000.

It follows j(tau163)=-640320^3. For Agda this demands a
genuine Hilbert class-polynomial construction, j(tau163) root theorem,
the exact -163 degree-one evaluation, and same-carrier identification.
Those proofs have not been supplied: a stored integer is not a proof.

## Primary source pointers

Jean-Pierre Serre, A Course in Arithmetic (1973),
DOI 10.1007/978-1-4684-9884-4.
Toshitsune Miyake, Modular Forms (2006),
DOI 10.1007/3-540-29593-3.
Tom M. Apostol, Modular Functions and Dirichlet Series in
Number Theory, eta chapter, DOI 10.1007/978-1-4612-0999-7_3.
Hilbert class polynomial reference:
https://flintlib.org/doc/acb_modular/class-polynomials.html

Local source provenance: JInvariantSourceAtlasExact,
JInvariantHomannMathematicaSourceCalibrationExact and
DeltaNormalizedWeight12SameObjectExact.
