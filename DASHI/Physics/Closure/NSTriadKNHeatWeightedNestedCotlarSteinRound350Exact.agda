module DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedCotlarSteinRound350Exact where

------------------------------------------------------------------------
-- ROUND350 / BIDI: ONCE MASS IS SUPPLIED, COTLAR IS ALREADY DONE
--
-- R349 puts the literal heat-weighted nested shell family into the old
-- two-sided OperatorCrossShellDecay interface.  R30 already owns both the
-- cutoff-uniform row-mass record and the finite Cotlar--Stein authority.
--
-- Therefore the remaining assumed physical input at this stage is exactly a
-- `CutoffUniformCrossShellMass` for the R349 decay (or any older theorem that
-- produces it).  The squared operator estimate is then the old R30 theorem
-- verbatim.  No new almost-orthogonality compiler is introduced.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (_*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNCutoffUniformCotlarSteinRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedOperatorDecayRound349Exact as R349

nestedFsCotlarSteinSquaredBound :
  ∀ {operatorLevel shellLevel : Level}
    {Operator : Set operatorLevel}
    {Shell : Set shellLevel}
    (space : R30.FiniteOperatorSpace Operator)
    (authority : R30.FiniteCotlarSteinAuthority space)
    (shells : List Shell)
    (I : R349.NestedFsOperatorDecayInputs space shells)
    (mass : R30.CutoffUniformCrossShellMass
      (R349.nestedFsOperatorCrossShellDecay space shells I)) →
  R30.operatorNorm space
    (R30.finiteOperatorSum space
      (R30.mapOperators authority shells (R349.literalFsOperatorAt I)))
  *
  R30.operatorNorm space
    (R30.finiteOperatorSum space
      (R30.mapOperators authority shells (R349.literalFsOperatorAt I)))
  ≤
  R30.uniformLeftMass mass * R30.uniformRightMass mass
nestedFsCotlarSteinSquaredBound space authority shells I mass =
  R30.cutoffUniformCotlarSteinSquaredBound
    space authority shells (R349.literalFsOperatorAt I)
    (R349.nestedFsOperatorCrossShellDecay space shells I)
    mass

round350OldCutoffUniformCrossShellMassReused : Bool
round350OldCutoffUniformCrossShellMassReused = true

round350OldFiniteCotlarSteinAuthorityReused : Bool
round350OldFiniteCotlarSteinAuthorityReused = true

round350NoNewAlmostOrthogonalityCompiler : Bool
round350NoNewAlmostOrthogonalityCompiler = true

round350CotlarSquaredBoundClosedConditionally : Bool
round350CotlarSquaredBoundClosedConditionally = true

round350HeatSpacetimeIntegrationClosed : Bool
round350HeatSpacetimeIntegrationClosed = false

round350ResolventGramConsumptionClosed : Bool
round350ResolventGramConsumptionClosed = false

round350PackageAClosed : Bool
round350PackageAClosed = false

round350ClayPromotion : Bool
round350ClayPromotion = false

round350CotlarSquaredBoundClosedConditionallyIsTrue :
  round350CotlarSquaredBoundClosedConditionally ≡ true
round350CotlarSquaredBoundClosedConditionallyIsTrue = refl

round350PackageAClosedIsFalse : round350PackageAClosed ≡ false
round350PackageAClosedIsFalse = refl

round350ClayPromotionIsFalse : round350ClayPromotion ≡ false
round350ClayPromotionIsFalse = refl
