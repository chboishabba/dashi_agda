# Yang-Mills Analytic State

Status: carrier-scale KP/Balaban surface strengthened, continuum mass gap not proved.

## What Landed

1. Diameter-1 actual KP envelope
   - Receipt: `YMActualKPLocalSumDiameter1Receipt`
   - Result: finite `p=7` diameter-1 local envelope closes as a finite bound.
   - Boundary: higher-diameter tails and global KP are still open.

2. Diameter-2 actual KP envelope
   - Receipt: `YMActualKPLocalSumDiameter2Receipt`
   - Result: finite diameter `<= 2` envelope closes as a finite bound.
   - Boundary: diameter `>= 3`, global KP, and continuum transfer remain open.

3. Conditional Balaban recurrence
   - Receipt: `YMBalabanRGInductiveStepProofReceipt`
   - Result: records the carrier recurrence `rho_{k+1} <= q rho_k + delta_k` with `q = 1/2 < 1`, conditional on the carrier beta threshold and summable correction terms.
   - Boundary: this is a carrier-scale conditional induction, not a proof for physical beta.

4. Physical beta bridge
   - Receipt: `YMPhysicalBetaBridgeOpenReceipt`
   - Result: the beta gap is recorded fail-closed with the corrected constants: `c_min = 0.242`, `p = 7`, `a = 0.5`, physical beta `6.0`, KP convergence beta `10.11`, strict absorption beta `12.97`, and strict gap `6.97`.
   - Diagnostic: at physical/lattice beta `6.0`, `r = 2.70 > 1`, so the KP comparison diverges.
   - Boundary: a rigorous nonperturbative RG bridge is still required; continuum Yang-Mills and Clay promotion remain false.

5. Perturbative bridge diagnostic
   - Receipt: `YMPhysicalBetaBridgeOpenReceipt`
   - Result: one-loop SU(2) `b0 = 11/(24*pi^2) ~= 0.0465` would require `exp(6.97 / 0.0465) ~= exp(150) ~= 1e65` scale ratio.
   - Boundary: perturbation theory is ruled out as a practical finite proof of the beta bridge.  The remaining crossover beta window is nonperturbative, `beta in [2,10.11]`.

## Diagnostic

Script: `../dashiCFD/scripts/ym_p7_polymer_enumerator_d3.py`

Output: `../dashiCFD/outputs/ym_p7_polymer_d3/ym_p7_polymer_d3.csv`

The diameter-3 enumerator produces large cumulative KP pressure in the current minimal finite model (`~1.45e4` in the smoke summary) and barely changes across the beta values. This is not KP safety evidence. It is evidence that the naive diameter-3 activity model is dominated by enumeration pressure and must be replaced or renormalized by the actual carrier action/RG measure before being consumed as a theorem.

Entropy-constant sensitivity:

- Generated file:
  `Docs/Images/clay-analytic-sprint/ym_c0_threshold_sensitivity.csv`.
- The strict absorption line is
  `beta_abs(C0) = (a + log(2 p C0)) / c_min`.
- `C0 = 0.5` gives `beta_abs = 10.10706673`; `C0 = 0.75` gives
  `11.78254238`; `C0 = 1` gives `12.97131128`; `C0 = 1.25` gives
  `13.89339207`.
- Therefore `C0` is now explicitly load-bearing for the physical beta bridge.

Monster re-2 stress:

- Artifact:
  `Docs/Images/clay-analytic-sprint/ym_monster_re2_C0_thresholds.csv`.
- Receipt:
  `DASHI/Physics/Closure/MonsterMoonshineSSPQuotientControlReceipt.agda`.
- If Monster `q^2` / second-irrep multiplicity is consumed raw as `C0`, the
  beta bridge becomes much harsher:
  `log(c2/c1)` gives `beta_abs = 19.359953`;
  square-root leakage gives about `22.65-22.67`;
  raw irrep or coefficient leakage gives about `32.33-32.36`.
- Therefore the YM lane now has an upstream quotient obligation:
  `MonsterMultiplicityQuotientControl`, meaning raw Monster representation
  multiplicity must be compressed to effective carrier orbit entropy before
  the `C0_eff ~= 1` threshold is allowed.

## Remaining YM Lemmas

1. Actual all-diameter KP tail bound from the true carrier Wilson action.
2. Physical beta bridge: prove the non-perturbative RG flow reaches the KP-safe carrier regime.
3. Monster multiplicity quotient control: prove raw `q^2` / second-irrep
   growth does not leak into the physical polymer entropy constant `C0`.
   The current positive evidence is the McKay-Thompson `T_7` compression:
   raw Monster `c2=21493760` is replaced on the `p=7` lane by
   `T_7(q^2)=204`.  The Rademacher audit gives the T7-envelope candidate
   `C0 ~= 115.543` and `beta* ~= 32.60`; the stronger `C0 = 2` target remains
   an open activity-identification lemma.  This sharpens but does not prove
   the quotient theorem.
4. Gate3 transfer: carry carrier area law through PAWOTG/Mosco/no-pollution/mass-shell.
5. OS/Wightman continuum construction remains external to the carrier receipts.

## Publication Posture

Publishable claim: finite carrier KP envelopes and the conditional RG recurrence are now precisely receipted, with the beta bridge and Gate3 transfer blocked.

Forbidden claim: Yang-Mills mass gap or Clay promotion.
