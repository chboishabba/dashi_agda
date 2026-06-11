# Drell-Yan t43 Provider Audit

Date: 2026-05-17

## Result

The active strict-log lane is the HEPData `t43/t44` phi-star ratio:

- ratio table: `10.17182/hepdata.115656.v1/t43`
- covariance table: `10.17182/hepdata.115656.v1/t44`
- numerator mass window: `50 <= M_ll < 76 GeV`
- denominator mass window: `76 <= M_ll < 106 GeV`
- observable: `DSIG/DPHISTAR / DSIG/DPHISTAR`
- jet condition: at least one jet is required

Local source evidence:

- `scripts/data/hepdata/ins2079374_phistar_mass_50-76_over_mass_76-106_t43.csv`
- `scripts/data/hepdata/ins2079374_Covariance_phistar_mass_50-76_over_mass_76-106_t44.csv`
- `scripts/data/hepdata/ins2079374_submission.yaml`

The CSV header for `t43` states that the measured differential cross section
in the `50 <= M_ll < 76 GeV` window is divided by the measured differential
cross section in the `76 <= M_ll < 106 GeV` window, in bins of `phi*`, and that
at least one jet is required. The `t44` covariance header states the same
observable contract for the covariance matrix.

## Provider Boundary

The current DYTurbo `xs_qt` route is not a strict-log provider for this lane.
It remains a diagnostic only because it supplies a `qT` histogram, while the
table is binned in event-level `phi*`, and because the current route does not
bind an exact CMS `>=1 jet` selection.

Promotion requires a provider that computes the table observable directly:

1. event-level `phi*` from the lepton four-momenta;
2. the exact CMS t43 at-least-one-jet selection inside the event/provider
   acceptance;
3. the same mass-window ratio `50-76 / 76-106`;
4. the HEPData `t43` binning and `t44` covariance.

## Provider Paths

Preferred path:

- Run the public Rivet analysis `CMS_2022_I2079374` on a Z+jet event generator
  and parse the resulting YODA histogram for the t43 ratio.

Fallback path:

- Extend the local DYTurbo source to book native `phi*` histograms and apply an
  exact t43 jet selection. A parton-level jet proxy would be diagnostic only
  unless it is shown to match the CMS anti-kt jet contract.

## Stop Rule

No further `qT -> phi*` remapping or EMST/CSS proxy pass is promotable for the
current strict-log lane. The W3 adjacent-ratio result remains inhabited as a
bounded shape-law receipt; full strict-log promotion waits for a commensurable
native-`phi*`, `>=1 jet` provider.
