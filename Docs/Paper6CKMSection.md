# CKM Diagnostic Results from the Heegner Lane Assignment

> **Superseded 2026-05-31.** This section is a historical CKM diagnostic
> snapshot.  The current Paper 6 baseline is
> [`Paper6FinalDraftOutline.md`](./Paper6FinalDraftOutline.md).  Current claim
> governance demotes `|Vcb|`/`A` to open frontier rather than carrier
> prediction, retires direct `arctan(sqrt(7))` CP-angle readback, and treats
> the full CKM matrix as open pending the three-factor morphism and `Y_d`.

Final-draft consolidation: see
[`Docs/Paper6FinalDraftUpdate.md`](./Paper6FinalDraftUpdate.md) for the
Manager A update covering the `y13` bridge formula, Hecke `p=29` phase
diagnostic, full CKM diagonalisation surface, and deg23 Faltings route.

This section records the current CKM-facing diagnostics from the Heegner lane
assignment.  The results are not promoted to physical CKM authority.  They are
typed receipt targets whose value is that each positive statement has an
explicit remaining blocker.

The two clean numerical diagnostics are the Wolfenstein parameters recorded in
`DASHI.Physics.Closure.WolfensteinLambdaAFromCarrierReceipt`:

- \(\lambda = \alpha_1 \pi\sqrt{3} \simeq 0.224403\), compared against a
  PDG-sized target near \(0.22453\).
- \(A = 112/(9\pi\sqrt{24}) \simeq 0.8086\), compared against a PDG-sized
  target near \(0.826\).

Both are diagnostics.  The receipt keeps `physicalLambdaPromoted = false`,
`physicalAPromoted = false`, `physicalCKMPromotionConstructed = false`, and
`pdgAuthorityBindingPromoted = false`.

The p3-p5 lane gives the current \(|V_{cb}|\) surface:

\[
(Y_d)_{23} =
  \alpha_1^2 \cdot \frac{14}{\sqrt{24}} \cdot \frac{8\pi}{3},
\]

with the diagnostic comparison \(|V_{cb}| \simeq 0.040717\).  The value is close
to the observed scale but still carries the named deg23 residual in
`DASHI.Physics.Closure.Deg23ResidualDiagnosticReceipt`: the natural carrier
readback is \(14\), while the required diagnostic value is \(14.302\), a
relative residual of about \(2.1\%\).

`DASHI.Physics.Closure.FaltingsHeightDeg23Receipt` records the next admissible
test for that residual.  The proposed correction is the CM Faltings-height
difference between \(E_{j=0}\) of discriminant \(-3\) and \(E_{j=-3375}\) of
discriminant \(-7\):

\[
\exp(h_F(E_{j=0}) - h_F(E_{j=-3375})).
\]

`DASHI.Physics.Closure.Deg23FaltingsComputationReceipt` records the direct
numerical test of this route.  Under the tested normalisation, it gives
\(14\exp(2\Delta h_F)\simeq46.479\), not \(14.302\).  The naive
Faltings-height correction is therefore diagnostic-negative; the correct
deg23 normalisation remains open.

The full carrier down-type Yukawa matrix surface is now recorded in
`DASHI.Physics.Closure.YukawaMatrixFullReceipt`:

\[
Y_d =
\begin{pmatrix}
\alpha_1 \cdot 2\pi &
\alpha_1 \pi\sqrt{3} &
(Y_d)_{13} \\
0 &
\alpha_1^2 \cdot 4\pi/3 &
\alpha_1^2 \cdot (14/\sqrt{24}) \cdot 8\pi/3 \\
0 & 0 &
\alpha_1^3 \cdot 8\pi/3
\end{pmatrix}.
\]

The p2-p5 entry \((Y_d)_{13}\) is now specified as a diagnostic complex bridge
entry in `DASHI.Physics.Closure.Y13ComplexEntryReceipt`:

\[
(Y_d)_{13} = (24\pi/\sqrt{6}) \exp(i\delta_{29}).
\]

The amplitude \(24\pi/\sqrt{6}\) is the bridge-isogeny diagnostic amplitude,
and \(\delta_{29}\) is the Hecke-character phase diagnostic at \(p=29\).  This
records the missing slot as a candidate complex entry, but keeps
`y13PhysicalValue = false` and `physicalCKMPromoted = false`.

Consequently the full CKM diagonalisation problem is now specified as a
diagnostic pipeline, pending formal authority.  The earlier
`DASHI.Physics.Closure.CKMFromYukawaEigenbasisReceipt` keeps the `y13=0`
negative control.  The full complex convention is tracked separately in
`DASHI.Physics.Closure.FullYukawaEigenbasisReceipt`; with
\(\alpha_1^3(24\pi/\sqrt6)e^{i\delta_{29}}\), it gives
\(|V_{us}|\simeq0.0898\), \(|V_{cb}|\simeq0.655\), and
\(|V_{ub}|\simeq0.756\).  This is still a poor physical CKM match.  The complex
`y13` bridge requires physical Yukawa normalization, certified
diagonalisation, and PDG comparison authority before any physical CKM claim can
be made.

Finally, `DASHI.Physics.Closure.CKMPhaseFromCMFieldsReceipt` records a negative
CP-phase diagnostic.  With the supplied positive real CM period normalisations,
\(\arg(\Omega_{-7}/\Omega_{-4}) = 0\), not the physical CKM phase near
\(1.196\) radians.  A non-real CM embedding choice or an additional DHR phase
source is required before the CP phase can be treated as a carrier prediction.

The current honest state is therefore:

- \(\lambda\) and \(A\) are strong closed-form diagnostics.
- The deg23 residual is named; the naive Faltings-height correction is
  diagnostic-negative.
- The p2-p5 Yukawa entry is specified diagnostically by the `y13` bridge
  formula, but remains unauthorised as a physical Yukawa value.
- Full CKM diagonalisation is now a specified diagnostic pipeline; the current
  complex convention is a negative diagnostic pending physical normalisation.
- The CP phase route is diagnostic-negative under the current period convention.
- The Hecke `p=29` phase is the candidate delta diagnostic, not an accepted
  CP-phase derivation.
- No accepted CKM, PDG, or Standard Model promotion flag is asserted.
