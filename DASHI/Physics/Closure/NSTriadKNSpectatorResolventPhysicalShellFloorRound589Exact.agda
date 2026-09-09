module DASHI.Physics.Closure.NSTriadKNSpectatorResolventPhysicalShellFloorRound589Exact where

------------------------------------------------------------------------
-- ROUND589 / PHYSICAL p-SHELL FLOOR -> LITERAL SPECTATOR RESOLVENT CEILING
--
-- The modern leaf-A carrier now uses the exact R406 spectator resolvent:
--
--   K(alpha,beta) = 1 / (lambda_alpha + lambda_beta).
--
-- To exploit that denominator we do NOT need a full equality between the
-- abstract physical radius and a canonical Nat radius.  The only geometric
-- input consumed by the scalar order argument is one positive lower floor on
-- the physical squared radius of alpha's outer forcing leg p:
--
--   0 < shellFloor <= |p_alpha|_physical^2.
--
-- Positive viscosity and R400 nonnegativity then give
--
--   nu * shellFloor
--      <= rho(p_alpha)
--      <= cellRate(alpha)
--      <= pairRate(alpha,beta).
--
-- R449's already-proved safe-reciprocal/positive-reciprocal bridge and the
-- existing positive reciprocal antitonicity theorem therefore yield
--
--   K(alpha,beta) <= 1 / (nu * shellFloor).
--
-- This is denominator algebra only.  It does not construct the physical shell
-- floor, sum any overlap family, or claim a cutoff-uniform envelope mass.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; Positive; NonNegative; _+_; _*_; _≤_; _<_; positive; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

F : C3.RealField _
F = Rational.rationalRealField

record PhysicalPShellFloor589
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (alpha : Physical.PhysicalTriadIncidence) : Set where
  constructor physical-p-shell-floor589
  field
    shellFloor589 : ℚ
    shellFloorPositive589 : 0ℚ < shellFloor589
    shellFloorBelowPhysicalPSquare589 :
      shellFloor589
      ≤ C3.normSquared
          (Field30.physicalInverseSquare physicalSystem)
          (Physical.p alpha)

open PhysicalPShellFloor589 public

module LiteralResolventFloor589
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem)) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module Swap = R538.PairSwap physicalSystem S

  nu : ℚ
  nu = Field30.viscosity physicalSystem

  shellRateFloor589 :
    {alpha : Physical.PhysicalTriadIncidence} →
    PhysicalPShellFloor589 physicalSystem alpha → ℚ
  shellRateFloor589 floor = nu * shellFloor589 floor

  shellRateFloorPositive589 :
    {alpha : Physical.PhysicalTriadIncidence} →
    (floor : PhysicalPShellFloor589 physicalSystem alpha) →
    0ℚ < shellRateFloor589 floor
  shellRateFloorPositive589 floor =
    let
      instance
        nuPositiveI : Positive nu
        nuPositiveI = viscosityPositive
        floorPositiveI : Positive (shellFloor589 floor)
        floorPositiveI = positive (shellFloorPositive589 floor)
        productPositiveI = ℚP.pos*pos⇒pos nu (shellFloor589 floor)
    in
    ℚP.positive⁻¹ (shellRateFloor589 floor)

  shellRateFloorBelowRhoP589 :
    {alpha : Physical.PhysicalTriadIncidence} →
    (floor : PhysicalPShellFloor589 physicalSystem alpha) →
    shellRateFloor589 floor
    ≤ R94.physicalDecayRate physicalSystem (Physical.p alpha)
  shellRateFloorBelowRhoP589 floor =
    let
      nuNN : 0ℚ ≤ nu
      nuNN = ℚP.<⇒≤ (ℚP.positive⁻¹ nu)
      instance nuNNI : NonNegative nu
      nuNNI = nonNegative nuNN
    in
    ℚP.*-monoˡ-≤-nonNeg nu
      (shellFloorBelowPhysicalPSquare589 floor)

  shellRateFloorBelowCellRate589 :
    {alpha : Physical.PhysicalTriadIncidence} →
    (floor : PhysicalPShellFloor589 physicalSystem alpha) →
    shellRateFloor589 floor ≤ Pair.D.Pair.cellRate alpha
  shellRateFloorBelowCellRate589 {alpha} floor =
    let
      rhoP = R94.physicalDecayRate physicalSystem (Physical.p alpha)
      rhoQ = R94.physicalDecayRate physicalSystem (Physical.q alpha)
      floorBelowP = shellRateFloorBelowRhoP589 floor
      qNN = R400.decayRateNonnegative
        physicalSystem viscosityPositive (Physical.q alpha)
      raw : shellRateFloor589 floor + 0ℚ ≤ rhoP + rhoQ
      raw = ℚP.+-mono-≤ floorBelowP qNN
    in
    subst
      (λ lower → lower ≤ Pair.D.Pair.cellRate alpha)
      (ℚP.+-identityʳ (shellRateFloor589 floor))
      raw

  shellRateFloorBelowPairRate589 :
    {alpha beta : Physical.PhysicalTriadIncidence} →
    (floor : PhysicalPShellFloor589 physicalSystem alpha) →
    shellRateFloor589 floor
    ≤ R291.pairRate (Swap.Q alpha beta)
  shellRateFloorBelowPairRate589 {alpha} {beta} floor =
    let
      alphaRate = Pair.D.Pair.cellRate alpha
      betaRate = Pair.D.Pair.cellRate beta
      floorBelowAlpha = shellRateFloorBelowCellRate589 floor
      betaPnn = R400.decayRateNonnegative
        physicalSystem viscosityPositive (Physical.p beta)
      betaQnn = R400.decayRateNonnegative
        physicalSystem viscosityPositive (Physical.q beta)
      betaNN : 0ℚ ≤ betaRate
      betaNN = ℚP.+-mono-≤ betaPnn betaQnn
      raw : shellRateFloor589 floor + 0ℚ ≤ alphaRate + betaRate
      raw = ℚP.+-mono-≤ floorBelowAlpha betaNN
    in
    subst
      (λ lower → lower ≤ R291.pairRate (Swap.Q alpha beta))
      (ℚP.+-identityʳ (shellRateFloor589 floor))
      raw

  pairRatePositiveFromShellFloor589 :
    {alpha beta : Physical.PhysicalTriadIncidence} →
    (floor : PhysicalPShellFloor589 physicalSystem alpha) →
    0ℚ < R291.pairRate (Swap.Q alpha beta)
  pairRatePositiveFromShellFloor589 floor =
    let
      floorPositive = shellRateFloorPositive589 floor
      floorBelow = shellRateFloorBelowPairRate589 floor
    in
    ℚP.<-≤-trans floorPositive floorBelow

  shellResolventCeiling589 :
    {alpha : Physical.PhysicalTriadIncidence} →
    PhysicalPShellFloor589 physicalSystem alpha → ℚ
  shellResolventCeiling589 floor =
    Quotient.positiveReciprocal
      (shellRateFloor589 floor)
      (shellRateFloorPositive589 floor)

  literalPairResolventBelowShellCeiling589 :
    {alpha beta : Physical.PhysicalTriadIncidence} →
    (floor : PhysicalPShellFloor589 physicalSystem alpha) →
    Swap.pairResolvent alpha beta ≤ shellResolventCeiling589 floor
  literalPairResolventBelowShellCeiling589 {alpha} {beta} floor =
    let
      denominator = R291.pairRate (Swap.Q alpha beta)
      denominatorPositive = pairRatePositiveFromShellFloor589 floor
      floorPositive = shellRateFloorPositive589 floor
      floorBelow = shellRateFloorBelowPairRate589 floor

      literalAsPositive :
        Swap.pairResolvent alpha beta
        ≡ Quotient.positiveReciprocal denominator denominatorPositive
      literalAsPositive =
        R449.safeReciprocalIsPositiveReciprocal
          denominator denominatorPositive

      antitone :
        Quotient.positiveReciprocal denominator denominatorPositive
        ≤ Quotient.positiveReciprocal
            (shellRateFloor589 floor) floorPositive
      antitone =
        Quotient.reciprocalAntitonePositive
          (shellRateFloor589 floor) denominator
          floorPositive denominatorPositive floorBelow
    in
    subst
      (λ selected → selected ≤ shellResolventCeiling589 floor)
      (sym literalAsPositive)
      antitone

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round589ConsumesOnlyPhysicalPShellFloor : Bool
round589ConsumesOnlyPhysicalPShellFloor = true

round589FullCanonicalRadiusEqualityRequired : Bool
round589FullCanonicalRadiusEqualityRequired = false

round589LiteralSpectatorResolventShellCeilingCompilerClosed : Bool
round589LiteralSpectatorResolventShellCeilingCompilerClosed = true

round589HeatLaplaceFactorizationRequired : Bool
round589HeatLaplaceFactorizationRequired = false

round589CutoffUniformSameOutputEnvelopeMassClosed : Bool
round589CutoffUniformSameOutputEnvelopeMassClosed = false

round589LeafAClosed : Bool
round589LeafAClosed = false

round589ClayPromotion : Bool
round589ClayPromotion = false

round589LiteralSpectatorResolventShellCeilingCompilerClosedIsTrue :
  round589LiteralSpectatorResolventShellCeilingCompilerClosed ≡ true
round589LiteralSpectatorResolventShellCeilingCompilerClosedIsTrue = refl

round589FullCanonicalRadiusEqualityRequiredIsFalse :
  round589FullCanonicalRadiusEqualityRequired ≡ false
round589FullCanonicalRadiusEqualityRequiredIsFalse = refl

round589ClayPromotionIsFalse : round589ClayPromotion ≡ false
round589ClayPromotionIsFalse = refl
