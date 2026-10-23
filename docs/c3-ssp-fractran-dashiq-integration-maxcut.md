# C3 braid / puncture / signed SSP–FRACTRAN / dashiQ integration max-cut

## Existing machinery, exact owners
- `DASHI/Biology/SignedSSPFRACTRANWeaveExact.agda`: fifteen typed SSP/Ogg prime lanes, signed multiplicities, ternary coarse sign and orientation; a prime value does not determine the corresponding geometric fibre.
- `DASHI/Moonshine/Monster369SignedSSPTauInversionSeamExact.agda`: actual multiplicity-negation involution; product with Fricke involution and a crucial prohibition against treating them as the same physical/modular action without a map.
- `DASHI/Moonshine/JInvariant369SignedSSPFRACTRANPhaseFibreExact.agda`: signed negation intertwines spectral conjugation; explicit no-go against conflating C2 conjugation and C3 translation.
- `DASHI/Programmes/QuantumExact.agda`: dashiQ is an experiment-design/identifiability programme with physical promotion delegated to Physics Foundations, not an independent proof that a phase/colour spectrum is realised in quantum gravity.
- Existing physical prediction authority should be applied to any braid–KK observable, not inferred from formal identity.

## New direct theorem-bearing bridge
`DASHI/Foundations/C3BraidSignedSSPFRACTRANMirrorExact.agda` imports those existing owners. Its `SiteSignedState` is a product of a genuine nine-site spatial coordinate and an actual signed SSP multiplicity; `invert` reflects the column of the spatial sheet and reverses multiplicity. Proves:
1. `invertTwice` by actual mirror-square and signed-negation-square proofs, not merely a Boolean flag;
2. `spectralInversion` through the existing signed SSP spectral conjugation theorem;
3. `sampledSixStep` using the existing six-time-step mirror theorem.

Thus this is a **chosen commuting product action** and a reusable carrier bridge. It does not identify the geometric C2, spectral C2, modular Fricke C2, physical charge conjugation or Pin double cover. Those are different domains requiring a declared intertwiner and dynamical interpretation. The puncture route is also independent: the current original centre-crossing braid cannot be assigned an origin-puncture winding. A new detour must be separately proved to avoid the origin and retain noncollision.

## Next dashiQ experiment-design max-cut
Compare hypotheses with identical formal parity but different predictions:
H0: signed SSP label reversal is a pure coding/observer change, no physical KK charge change;
H1: a physically coupled reflection flips a measurable gauge charge with normal-frame transport;
H2: a puncture-dependent holonomy survives continuous centre-avoiding detours and appears as an observable phase offset.
To discriminate, specify an actual physical source, a measurement operator and instrument mapping, a gauge invariant phase/wilson loop, units/calibration, perturbation design, likelihood under each hypothesis, and failure modes. A source-written spectral symmetry identity is not data.
Do not use the numerical prime lane as a substitute for an observed charge or mass.

## Follow-on analytic geometry
Continuous C3 PL centreline no-collision has exact min squared clearance 1. Next build a centre-avoiding equivariant detour and a smooth framing, then use Pin/O2 and SSP signed transport only through a separately proved map. The KK Ricci-flat null-wave family is an available classical background, not evidence that its KK fibre is the braid normal circle.

## Acceptance
```sh
agda -i . -i /path/to/agda-stdlib DASHI/Foundations/C3BraidSignedSSPFRACTRANMirrorExact.agda
python3 scripts/check_c3_continuous_affine_mirror_clearance.py
python3 scripts/check_c3_punctured_sheet_pin_winding.py
```
No exact-head Agda kernel receipt or physical dashiQ calibration claimed.
