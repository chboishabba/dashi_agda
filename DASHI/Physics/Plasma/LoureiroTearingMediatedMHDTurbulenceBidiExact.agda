module DASHI.Physics.Plasma.LoureiroTearingMediatedMHDTurbulenceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Source-shaped owner for:
-- Loureiro & Boldyrev, Role of magnetic reconnection in MHD turbulence (2017)
-- arXiv:1612.07266; and Boldyrev & Loureiro, MHD turbulence mediated by reconnection
-- arXiv:1706.07139; with numerical support Walker, Boldyrev & Loureiro 2018.

data TurbulenceRegime : Set where ordinaryAlignedMHD currentSheetEddy tearingAffected reconnectionMediated : TurbulenceRegime

data ScalingCoordinate : Set where criticalThickness resistiveDissipationThickness perpendicularSpectrum alignmentAngle : ScalingCoordinate

record ScalingClaim : Set where
  constructor scaling-claim
  field
    coordinate : ScalingCoordinate
    sourceExpression : String
    asymptoticNotIdentity : Bool
    asymptoticNotIdentityIsTrue : asymptoticNotIdentity ≡ true
    sourceReference : String

open ScalingClaim public

reconnectionOnset2017 : ScalingClaim
reconnectionOnset2017 = scaling-claim criticalThickness
  "lambda_c / L ~ S_L^(-4/7)"
  true refl
  "Loureiro & Boldyrev 2017, arXiv:1612.07266"

reconnectionIntervalSpectrum2017 : ScalingClaim
reconnectionIntervalSpectrum2017 = scaling-claim perpendicularSpectrum
  "E(k_perp) ~ k_perp^(-5/2)"
  true refl
  "Loureiro & Boldyrev 2017, arXiv:1612.07266"

resistiveScale2017 : ScalingClaim
resistiveScale2017 = scaling-claim resistiveDissipationThickness
  "lambda_* ~ L_0 S_0^(-3/4)"
  true refl
  "Boldyrev & Loureiro 2017, arXiv:1706.07139"

betaZeroSpectrum2017 : ScalingClaim
betaZeroSpectrum2017 = scaling-claim perpendicularSpectrum
  "E(k_perp) ~ k_perp^(-11/5) for beta = 0"
  true refl
  "Boldyrev & Loureiro 2017, arXiv:1706.07139"

record TearingCompetition : Set where
  constructor tearing-competition
  field
    eddyTurnoverRate : String
    tearingGrowthRate : String
    transitionCriterion : String
    postTransitionInterpretation : String
    sourceReference : String

open TearingCompetition public

canonicalTearingCompetition : TearingCompetition
canonicalTearingCompetition = tearing-competition
  "nonlinear eddy turnover rate"
  "tearing instability growth rate of sheet-like eddy"
  "tearing becomes dynamically important when its growth competes with the nonlinear rate"
  "below lambda_c the cascade is altered by tearing/reconnection rather than continuing the ordinary aligned phenomenology unchanged"
  "Loureiro-Boldyrev 2017; Boldyrev-Loureiro 2017"

record LoureiroTearingBoundary : Set where
  constructor loureiro-tearing-boundary
  field
    currentSheetLikeEddyAlreadyMeansReconnected : Bool
    currentSheetLikeEddyAlreadyMeansReconnectedIsFalse : currentSheetLikeEddyAlreadyMeansReconnected ≡ false
    tearingOnsetEqualsOrdinaryResistiveDissipationScale : Bool
    tearingOnsetEqualsOrdinaryResistiveDissipationScaleIsFalse : tearingOnsetEqualsOrdinaryResistiveDissipationScale ≡ false
    spectrumExponentUniversalAcrossDissipationModels : Bool
    spectrumExponentUniversalAcrossDissipationModelsIsFalse : spectrumExponentUniversalAcrossDissipationModels ≡ false
    NSVortexStretchingIsMagneticReconnection : Bool
    NSVortexStretchingIsMagneticReconnectionIsFalse : NSVortexStretchingIsMagneticReconnection ≡ false
    tearingCanModifyInertialRangeCascadeBeforeDissipation : Bool
    tearingCanModifyInertialRangeCascadeBeforeDissipationIsTrue : tearingCanModifyInertialRangeCascadeBeforeDissipation ≡ true

canonicalLoureiroTearingBoundary : LoureiroTearingBoundary
canonicalLoureiroTearingBoundary = loureiro-tearing-boundary false refl false refl false refl false refl true refl

data TearingReverseTarget : Set where
  acquireOuterScaleLundquist
  acquireSheetAspectRatio
  acquireTearingDispersionRelation
  acquireNonlinearTurnoverRate
  acquireCriticalScaleComparison
  acquireSpectrumClosure
  acquireDissipationModel
  : TearingReverseTarget

record TearingReverseObligation : Set where
  constructor tearing-reverse-obligation
  field
    target : TearingReverseTarget
    producer : String
    promotes : String
    cannotPromote : String

open TearingReverseObligation public
