# Yang–Mills Round 40 — multiplier locality and correlated singleton residual

Round 40 takes the exact Round-39 KKT reduction as its starting point and targets the remaining Gate-I obstruction: local control of the selected-background KKT multiplier on the plaquette constraint collar.

## Canonical sign

The repository now fixes one generated sign chain:

```text
dS(Pw) = dS(w) - dS((I-P)w)
dS(w) = Singleton + RawLocalization
dS((I-P)w) = <lambda,Lw>
```

Hence

```text
ProjectedSpillover = RawLocalization - <lambda,Lw>
Singleton = -RawLocalization + <lambda,Lw>
```

The alternative double-negative target is not silently admitted.  It would agree with the canonical target only after an additional exact cancellation of the multiplier pairing.

## Redundancy-safe multiplier pairing

For any redundant multiplier row component `r` with `L* r = 0`, finite adjointness gives

```text
<r,Lw> = <L*r,w> = 0.
```

Therefore every KKT multiplier representative gives the same physical defect pairing.  The canonical Moore–Penrose multiplier is used without deleting redundant rows.

## Constraint-collar localization

A typed collar mask and the literal row-support proof reduce the pairing exactly:

```text
<lambda,delta_(p,h)> = <chi_C(p) lambda,delta_(p,h)>.
```

A multiplier supported outside the collar annihilates the raw extractor defect.  This is an equality before any norm estimate.

## Constraint-Gram Combes–Thomas lane

The first locality target is the smaller multiplier operator

```text
K_A = L_A L_A*.
```

Round 40 reuses the existing finite Combes–Thomas conjugation and tilt-row budget to expose the exact producer obligations:

- finite interaction range for `K_A`;
- a reduced multiplier-space floor;
- a diagonal tilt and inverse tilt;
- distortion times row mass below the half-gap;
- a tilted Green-entry majorant.

These data yield off-diagonal decay of `K_A^+`.  No physical decay claim is promoted before the selected-background stencil, floor and tilt are supplied.

## Two-source Green contraction

The projector spillover is rewritten as

```text
<K_A^+ L_A g_A,L_A w_(p,h)>
  = <L_A g_A,K_A^+ L_A w_(p,h)>.
```

The exact finite double-sum expansion exposes source atoms and defect atoms simultaneously.  This is the representation on which support separation, D4 covariance and signed cancellation act.

## Pair-indexed ownership

Raw localization uses one nonempty Boolean subset `S`; the Green term uses a pair `(S,T)`.  Each pair carries:

- a D4 orbit representative;
- orientation-preserving or orientation-reversing status;
- collar displacement;
- one residual owner.

The exact-cancellation owner is erased before positive majorisation.  The four surviving owner bounds are then combined against the literal singleton budget

```text
55 / 18874368.
```

## Genuine KKT inverse and full-block constants

The complete saddle operator is no longer consumed merely through a right inverse.  Reduced coercivity on `ker L` and reduced multiplier-adjoint injectivity imply a trivial homogeneous KKT kernel, hence injectivity.  The constructed right inverse is therefore also a left inverse.

For full-block Combes–Thomas, every scalar is named:

```text
C_K,
S_H,
S_L*,
S_L,
R_KKT,
mu_KKT.
```

The exact Neumann parameter is `C_K (S_H + S_L* + S_L)`.  A half-contraction certificate gives the explicit tilted inverse majorant `2 C_K`.

## D4 covariance

Constraint and adjoint covariance imply Gram covariance.  A separate Moore–Penrose covariance producer is required before the Green contraction may be reduced by D4 orbits.  This prevents a slot permutation from being mistaken for physical covariance of the complete constrained kernel.

## Coefficient-field discipline

The selected-background constraint kernel and nonorthogonal frame are parameterized over an explicit ordered star field.  A rational frame is authorized only when every literal constraint and frame entry is exhibited as the image of a rational.  The rational finite certificate is not silently identified with the physical real/complex kernel.

## Generated optimization and fail-closed no-fit

The old balanced `27+28=55` witness remains arithmetic history, not the physical choice.  Round 40 introduces a generated optimization certificate containing:

- one admissible physical parameter assignment;
- exact raw-localization and multiplier-defect costs;
- global minimality in the declared candidate family;
- proof that the total fits the literal budget.

A dual lower-bound certificate refutes the entire estimate family when every admissible cost lies strictly above the budget.

## Terminal reducer

The corrected sign, correlated owner cancellation and owner budget now compose into

```text
RawLocalization - <L_A g_A,K_A^+ L_A w_(p,h)>
  <= (55 / 18874368) C_p(h),
```

and stationarity gives the literal singleton lower bound.  What remains physical and open is now sharply isolated: construction of the selected-background atom family and proofs of its four owner estimates, the concrete constraint-Gram stencil/floor/tilt, and the physical parameter optimization certificate.
