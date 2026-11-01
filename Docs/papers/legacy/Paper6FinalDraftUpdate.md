# Paper 6 Final Draft Update: CKM Diagnostics

Date: `2026-05-29`
Status: superseded historical synthesis; diagnostic; non-promoting

> **Superseded 2026-05-31.** This file is retained as a historical diagnostic
> snapshot.  The current Paper 6 baseline is
> [`Paper6FinalDraftOutline.md`](./Paper6FinalDraftOutline.md), backed by
> `CKMGateAbRetirementReceipt`, `KleinQuarticQMReceipt`, and
> `NSCarrierKolmogorovSerrinReceipt`.  In the current ledger, `|Vcb|`, `A`,
> `gamma`, `beta`, `alpha`, `rho`, and `eta` are not carrier predictions.
> Direct CP-angle shortcuts are retired, and Paper 6 is not a physical CKM
> promotion.

This update consolidates the Manager A CKM diagnostics for Paper 6.  The
current result is stronger than the earlier open-texture story, because the
`y13` bridge slot and the CKM diagonalisation surface are now specified as
diagnostics.  It is still not a physical CKM promotion: formal authority,
physical Yukawa normalization, certified diagonalisation, and PDG comparison
receipts remain pending.

## 1. y13 Bridge Formula

`DASHI.Physics.Closure.Y13ComplexEntryReceipt` records the p2-p5 complex
down-sector entry as the diagnostic formula

```text
(Y_d)13 = (24*pi/sqrt6) * exp(i delta_29)
```

The amplitude `24*pi/sqrt6` is recorded as the bridge-isogeny amplitude.  The
phase `delta_29` is recorded as the Hecke-character phase diagnostic at
`p=29`.  The receipt has `y13ComplexEntryRecorded = true` and
`cpPhaseFromHeckeCharacterDiagnostic = true`, but it also keeps
`y13PhysicalValue = false` and `physicalCKMPromoted = false`.

This means Paper 6 may now say that the p2-p5 bridge slot is specified as a
diagnostic complex entry.  It must not say that the entry is a physical Yukawa
value or an accepted CKM input.

## 2. Hecke p=29 Phase Diagnostic

The Hecke `p=29` phase is a candidate CP-source diagnostic, not a derived CKM
phase.  It supplies the symbol `delta_29` used in the `y13` bridge formula.
At this stage it records where a non-real phase could enter the down-sector
matrix; it does not prove a Hecke-character theorem, choose a physical branch,
or bind the result to the observed CKM phase.

The conservative wording is:

```text
The p=29 Hecke-character phase supplies a candidate delta diagnostic for the
p2-p5 y13 bridge entry; physical CP-phase authority remains absent.
```

This should be read together with
`DASHI.Physics.Closure.CKMPhaseFromCMFieldsReceipt`, which records that the
positive-real CM-period route gives phase `0`, not the physical comparison
near `1.196` radians.  The p=29 Hecke phase is therefore the live candidate
delta diagnostic, while the positive-real period route is diagnostic-negative.

## 3. Full CKM Diagonalisation Status

The full CKM diagonalisation is now specified as a diagnostic task over the
recorded down-sector texture, pending formal authority.

The matrix surface is recorded in
`DASHI.Physics.Closure.YukawaMatrixFullReceipt`:

```text
Y_d =
[ 2*pi,                 alpha1*pi*sqrt(3),                         y13 ]
[ 0,                    alpha1^2*(4*pi/3),                         alpha1^2*(14/sqrt24)*(8*pi/3) ]
[ 0,                    0,                                         alpha1^3*(8*pi/3) ]
```

with the updated diagnostic bridge

```text
y13 = (24*pi/sqrt6) * exp(i delta_29).
```

`DASHI.Physics.Closure.FullYukawaEigenbasisReceipt` records the full complex
diagonalisation diagnostic:

```text
U_d diagonalises Y_d^dagger Y_d
V = U_u^dagger U_d
current diagnostic convention: U_u = identity, so V = U_d
```

Earlier `DASHI.Physics.Closure.CKMFromYukawaEigenbasisReceipt` `y13=0`
numerical diagnostics are retained as a negative control, not as the final CKM
result.  With the complex `y13` diagnostic now specified, the current
full-matrix diagnostic is still a poor physical CKM match:

```text
|V| ~= [[0.648665,0.089765,0.755762],
       [0.749691,0.095891,0.654804],
       [0.131142,0.991336,0.007398]]
```

The remaining missing ingredients are physical Yukawa normalization, certified
eigenbasis/diagonalisation computation, and PDG/CKM authority binding.

Therefore Paper 6 may say that the CKM diagonalisation problem is fully
specified as a diagnostic pipeline.  It may not say that the physical CKM
matrix has been derived.

## 4. deg23 Faltings Route Status

The deg23 residual remains the named open arithmetic problem in the p3-p5/A
lane.  `DASHI.Physics.Closure.Deg23ResidualDiagnosticReceipt` records

```text
deg23 = |E(F5)| + |E(F7)| = 6 + 8 = 14
required diagnostic value = 14.302
residual = 0.302 / 14.302 ~= 2.1%
```

`DASHI.Physics.Closure.FaltingsHeightDeg23Receipt` records the next admissible
test route:

```text
candidate correction = exp(h_F(E_{j=0}) - h_F(E_{j=-3375}))
```

where the two CM lanes have discriminants `-3` and `-7`.
`DASHI.Physics.Closure.Deg23FaltingsComputationReceipt` now records the direct
numerical test.  Under the tested normalisation,
`14*exp(2*Delta h_F) ~= 46.479`, not `14.302`; the naive Faltings-height route
is therefore diagnostic-negative.

`DASHI.Physics.Closure.Deg23HeckeEigenvalueReceipt` records a separate tested
normalization route.  The selected eta-product gives `a5 = +1`, not the
quoted `a5 = -2`, and does not resolve the residual.

## 5. Honest Conclusion

The Paper 6 CKM conclusion should be:

- the lambda diagnostic is strong: `lambda = alpha1*pi*sqrt(3) ~= 0.224403`,
  with comparison accuracy at the `0.04%` to `0.056%` level depending on the
  lambda convention;
- the `A` diagnostic is meaningful but still within the residual envelope:
  `A = 112/(9*pi*sqrt24) ~= 0.8086`, about `2.1%` from the comparison target;
- the p3-p5 Vcb-scale diagnostic remains useful, but its deg23 arithmetic
  residual is open;
- the candidate delta diagnostic is now localized to the Hecke `p=29` phase in
  the complex `y13` bridge entry;
- full CKM diagonalisation is specified as a diagnostic pipeline over the
  recorded matrix, but formal authority and certified computation are pending;
- there is no physical CKM promotion, no accepted CP-phase derivation, no PDG
  authority binding, and no Standard Model promotion.

This is a stronger diagnostic frontier, not a phenomenological claim.  The
draft should avoid fabricated references and should cite only the receipt
modules above unless an external authority receipt is actually added.

## 6. Heegner CKM Diagnostic v2 Addendum

The next diagnostic pass adds five receipts:

- `DASHI.Physics.Closure.OSPositivityDissolvedReceipt`
- `DASHI.Physics.Closure.PhysicalMassMatrixReceipt`
- `DASHI.Physics.Closure.CKMFromPhysicalMassMatrix`
- `DASHI.Physics.Closure.Deg23RGRunningHypothesisReceipt`
- `DASHI.Physics.Closure.VubVtdFromFullCKM`

The OS/H0 blocker is now better classified. The negative H0 matrix check used
bare Yukawa entries as if they were Hamiltonian entries. The corrected physical
quark Hamiltonian is built from `M_d^dagger M_d`, with
`M_d = Y_d v/sqrt(2)`, so its mass contribution is positive semidefinite by
construction. This is a wrong-object correction, not a full OS/Wightman
promotion.

Using external PDG `v = 246.22 GeV`, the diagnostic mass eigenvalues are
approximately `[0.0134, 7.148, 59.687] GeV`, which do not match the rough
down-quark PDG comparison targets. The VEV factor rescales masses but leaves
the CKM eigenvectors unchanged, so the diagnostic CKM matrix remains a poor
physical match.

The full complex diagnostic gives `|Vub| ~= 0.7558`, `|Vtd| ~= 0.1311`, and
`J ~= -3.47e-4`, about `11.26` times the PDG-sized Jarlskog target. The one-loop
QCD running explanation for the `deg23` residual is also diagnostic-negative:
the natural `p5 -> p7` scale test gives about `4.26%`, not the required
`2.16%`; a tuned scale near `5.919 GeV` can reproduce the factor but is not a
carrier derivation.

The conclusion is unchanged: the Heegner lane machinery gives a useful
diagnostic surface, but `physicalCKMPromoted = false`,
`physicalCPPhaseDerived = false`, and `physicalMassMatchesPDG = false`.
