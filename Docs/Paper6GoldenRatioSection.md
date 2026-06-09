# Golden-Ratio and Geometric-Resummation Diagnostics in the CKM Lane

This section records a diagnostic update, not a physical CKM derivation.
All promotion flags associated with physical CKM, physical \(V_{cb}\), physical
\(V_{ub}\), and CP violation remain false.

## The 2-3 Lane

The uncorrected Heegner p3-p5 diagnostic gives

\[
(Y_d)_{23}=\frac{14}{\sqrt{24}}\frac{8\pi}{3}.
\]

The geometric resummation hypothesis replaces the integer degree \(14\) by

\[
\deg_{23}^{\mathrm{geom}}=\frac{14}{1-\alpha_1/2}.
\]

With \(\alpha_1=0.041240\), this gives
\(\deg_{23}^{\mathrm{geom}}=14.294757908064284\) and a Wolfenstein-\(A\)
diagnostic \(A=0.8255982974316682\), which is within about \(0.049\%\) of the
comparison target \(A\simeq0.826\). This is a useful diagnostic for the
Wolfenstein-\(A\) lane.

It is not a physical \(V_{cb}\) derivation. Under a direct comparison to
\(|V_{cb}|\simeq0.0408\), the same factor gives
\(|V_{cb}|=0.04157450642980736\), about \(1.9\%\) high. The receipt therefore
records a resummation hypothesis, not a promotion.

## The 1-3 Lane

The bridge-isogeny diagnostic gives

\[
(Y_d)_{13}=\frac{24\pi}{\sqrt6}=30.781195923884738.
\]

Using the low \(V_{ub}\) comparison target \(0.00357\), the required effective
\((Y_d)_{13}\) magnitude is \(50.89935116926654\), a factor
\(1.6535858871477787\) above the bridge value. The golden-ratio correction
\[
\phi=\frac{1+\sqrt5}{2}
\]
would give \(\phi (Y_d)_{13}=49.805021219215234\), leaving a residual factor
of about \(1.022\). The proximity is interesting but not decisive.

The current receipt records this as a p5-lane/Rogers-Ramanujan diagnostic
hypothesis. There is no formal derivation of \(\phi\) from the carrier coupling,
and there is no physical \(V_{ub}\) promotion.

## Jarlskog Status

The current full-eigenbasis diagnostic gives a Jarlskog invariant about
\(11.26\) times the PDG-sized target. The dominant failure is the current
\((Y_d)_{13}\)/eigenbasis magnitude convention; the phase is not the main
source of the order-of-magnitude error.

The honest state is:

- `vcbGeometricResummationDiagnostic = true`
- `y13GoldenRatioFactor = true`
- `goldenRatioCarrierDerived = false`
- `physicalVcbPromoted = false`
- `physicalVubPromoted = false`
- `physicalCKMPromoted = false`

