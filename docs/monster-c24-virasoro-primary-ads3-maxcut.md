# Monster c=24 graded states vs Virasoro primaries: AdS3 max-cut

## Preexisting theorem owners (attribution)
DASHI/Moonshine/MonsterGradedVOABridgeExact.agda already owns the generic exact graded trace-to-dimension obligation with genuine VOA construction explicitly a separate requirement.
DASHI/Moonshine/JCoefficientCharacterBridge.agda already proves 196884=1+196883. The new cut must not rename these old results as discoveries.

## New exact finite-series proof obligation
scripts/check_monster_c24_virasoro_primary_counts.py derives low-level formal series from E4(q)^3 / Delta(q) -744 = J(q), and uses Euler P(q)=prod_(n>=1)(1-q^n).
For c=24, assuming the standard generic nonvacuum Virasoro Verma characters and vacuum character with L_-1|0>=0:
J(q) = q^-1 (1-q)/P(q) + (sum_h N_h q^(h-1))/P(q).
Therefore sum_h N_h q^(h-1) = P(q) J(q) - q^-1(1-q).
In particular 196884 total weight-two Monster CFT states comprise one stress-tensor vacuum descendant and 196883 weight-two primaries. This is much closer to gravitational microstate counting than raw coefficient equals primary count. The finite identity by itself does not certify VOA module decomposition, absence of additional nulls, or any AdS3 gravity duality.

## Open actual physics proof gates
1. Instantiate the existing Monster graded VOA witness to the literal V^natural action, trace and conformal grading rather than an abstract record.
2. Establish exact character identities and modular S/T, with primary and descendant partitions, for all grades (not finite coefficients).
3. Select and justify the AdS3 bulk gravity action, boundary and saddles. Brown-Henneaux central charge c=3ell/(2G3)=24 requires ell/G3=16 in conventional units, but classical equality alone is not quantum duality.
4. Compare BTZ entropy and precise bulk partition function to full CFT spectrum, and evaluate anomalies, negative norm, modular-invariant completion and multi-boundary constraints.
5. Any link to KK and braid needs physical dimension reduction and a verified bundle morphism. The existing 4+1 Ricci-flat pp-wave has not been shown to reduce to negatively curved AdS3. Signed SSP/C3/Pin symmetry cannot be substituted for a CFT stress tensor.

## Acceptance
python3 scripts/check_monster_c24_virasoro_primary_counts.py
Source committed; no exact-head kernel/CI claimed.
