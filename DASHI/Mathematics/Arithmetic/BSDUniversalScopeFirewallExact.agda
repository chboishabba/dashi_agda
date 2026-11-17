module DASHI.Mathematics.Arithmetic.BSDUniversalScopeFirewallExact where

------------------------------------------------------------------------
-- Original source: BirchSwinnertonDyerBoundary.agda (DASHI authors).
-- Attribution: Wiles (CMI official statement), Rubin (CM rank-zero).
--
-- This is a SCOPE/QUANTIFIER INTERFACE, not a solution to universal BSD.
-- Clay's formally stated prize conjecture is universal rank equality.
-- The stronger all-prime Sha/leading-coefficient statement is tracked
-- separately. Rational BSDScalarData cannot itself realize real periods.
--
-- No source, global rank proof, Sha order or analytic theorem is invented.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Arithmetic.BirchSwinnertonDyerBoundary as BSD
import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as E

-- The universal Clay rank-equality carrier must range over every
-- original rational short Weierstrass curve, with its OWN data.
-- Restriction to the one selected CM example does not inhabit this.
record UniversalBSDRankInterface : Setω where
  field
    mordellWeil : (curve : E.ShortWeierstrassCurve) →
      BSD.MordellWeilData curve
    analytic : (curve : E.ShortWeierstrassCurve) →
      BSD.EllipticLFunctionData curve
    rankForEveryCurve : (curve : E.ShortWeierstrassCurve) →
      BSD.BSDRankConjecture curve
        (mordellWeil curve) (analytic curve)

-- Strong/refined conjecture is stronger than the prize's formal rank
-- statement and requires a SAME-CURVE arithmetic/analytic meaning weld.
-- This interface merely exposes missing evidence; no inhabitant built.
record UniversalBSDRefinedInterface : Setω where
  field
    prizeRank : UniversalBSDRankInterface
    scalars : (curve : E.ShortWeierstrassCurve) → BSD.BSDScalarData
    strongForEveryCurve : (curve : E.ShortWeierstrassCurve) →
      BSD.BSDLeadingCoefficientConjecture (scalars curve)

-- A two-element logical countermodel shows exactly why a selected
-- example cannot automatically discharge an unrestricted universal
-- statement. This is NOT a counterexample to BSD on an elliptic curve.
toySelectedProperty : Bool → Set
toySelectedProperty true = ⊤
toySelectedProperty false = ⊥

toySelectedTrue : toySelectedProperty true
toySelectedTrue = tt

toyUniversalFalse : (∀ curveTag → toySelectedProperty curveTag) → ⊥
toyUniversalFalse allTags = allTags false
