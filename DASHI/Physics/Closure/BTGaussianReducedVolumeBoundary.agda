module DASHI.Physics.Closure.BTGaussianReducedVolumeBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)

data ⊥ : Set where

------------------------------------------------------------------------
-- BT Gaussian reduced-volume boundary receipt.
--
-- This module records a constructible Bruhat-Tits / product-tree analogue
-- of Perelman's reduced-volume integrand.  It is a discrete Gaussian
-- weighting receipt:
--
--   reduced distance analogue: d^2 / (4 tau)
--   product-tree sphere growth: prefactor 8 times 42^r
--   Gaussian radial weight: exp(-r^2 / (4 tau))
--
-- The convergence flag is true for this constructible model because a
-- quadratic Gaussian exponent dominates the exponential radial growth
-- q^r, including the T3 x T2 x T7 product base 42.  The module does not
-- prove Perelman monotonicity, Ricci-flow back-reaction, smooth
-- geometrization, or any Clay claim.

data ProductTreeFactor : Set where
  T3 :
    ProductTreeFactor

  T2 :
    ProductTreeFactor

  T7 :
    ProductTreeFactor

canonicalProductTreeFactors : List ProductTreeFactor
canonicalProductTreeFactors =
  T3
  ∷ T2
  ∷ T7
  ∷ []

productT3xT2xT7Base : Nat
productT3xT2xT7Base =
  (3 * 2) * 7

productBranchingBase42 : Nat
productBranchingBase42 =
  42

productBaseComputesTo42 :
  productT3xT2xT7Base ≡ productBranchingBase42
productBaseComputesTo42 =
  refl

productSpherePrefactor8 : Nat
productSpherePrefactor8 =
  8

data RadialVariable : Set where
  r :
    RadialVariable

data ScaleVariable : Set where
  tau :
    ScaleVariable

data ReducedDistanceFormula : Set where
  dSquaredOverFourTau :
    RadialVariable →
    ScaleVariable →
    ReducedDistanceFormula

canonicalReducedDistanceFormula :
  ReducedDistanceFormula
canonicalReducedDistanceFormula =
  dSquaredOverFourTau r tau

reducedDistanceFormulaName : String
reducedDistanceFormulaName =
  "ell_BT(r,tau) = d_BT(root,x)^2 / (4 tau)"

reducedDistanceFormulaText : String
reducedDistanceFormulaText =
  "reduced distance analogue d^2/(4 tau), with d_BT specialized to radial depth r"

data GaussianWeightFormula : Set where
  gaussianExpMinusRSquaredOverFourTau :
    RadialVariable →
    ScaleVariable →
    GaussianWeightFormula

canonicalGaussianWeightFormula :
  GaussianWeightFormula
canonicalGaussianWeightFormula =
  gaussianExpMinusRSquaredOverFourTau r tau

gaussianWeightFormulaText : String
gaussianWeightFormulaText =
  "exp(-r^2/(4 tau))"

data SphereGrowthFormula : Set where
  productSphereGrowth :
    Nat →
    Nat →
    RadialVariable →
    SphereGrowthFormula

canonicalSphereGrowthFormula :
  SphereGrowthFormula
canonicalSphereGrowthFormula =
  productSphereGrowth productSpherePrefactor8 productBranchingBase42 r

sphereGrowthFormulaText : String
sphereGrowthFormulaText =
  "N(r) <= 8 * 42^r for the T3 x T2 x T7 product-tree shell count"

data ReducedVolumeSeriesFormula : Set where
  gaussianReducedVolumeSeries :
    SphereGrowthFormula →
    GaussianWeightFormula →
    ReducedVolumeSeriesFormula

canonicalGaussianReducedVolumeSeries :
  ReducedVolumeSeriesFormula
canonicalGaussianReducedVolumeSeries =
  gaussianReducedVolumeSeries
    canonicalSphereGrowthFormula
    canonicalGaussianWeightFormula

seriesFormulaText : String
seriesFormulaText =
  "sum_r N(r) * exp(-r^2/(4 tau)), with N(r) bounded by 8 * 42^r"

data ConvergenceDominanceReason : Set where
  gaussianQuadraticDominatesExponentialQPower :
    ConvergenceDominanceReason

  gaussianQuadraticDominatesProductFortyTwoPower :
    ConvergenceDominanceReason

  finitePrefactorDoesNotAffectConvergence :
    ConvergenceDominanceReason

canonicalConvergenceReasons : List ConvergenceDominanceReason
canonicalConvergenceReasons =
  gaussianQuadraticDominatesExponentialQPower
  ∷ gaussianQuadraticDominatesProductFortyTwoPower
  ∷ finitePrefactorDoesNotAffectConvergence
  ∷ []

data ConstructibleStatus : Set where
  constructibleDiscreteAnalogue :
    ConstructibleStatus

  notSmoothPerelmanTheorem :
    ConstructibleStatus

  notRicciFlowBackReaction :
    ConstructibleStatus

canonicalConstructibleStatus : List ConstructibleStatus
canonicalConstructibleStatus =
  constructibleDiscreteAnalogue
  ∷ notSmoothPerelmanTheorem
  ∷ notRicciFlowBackReaction
  ∷ []

GaussianDominatesExponentialGrowth : Bool
GaussianDominatesExponentialGrowth =
  true

GaussianDominatesProductFortyTwoGrowth : Bool
GaussianDominatesProductFortyTwoGrowth =
  true

ReducedVolumeSeriesConverges : Bool
ReducedVolumeSeriesConverges =
  true

SmoothPerelmanMonotonicityTheoremPromoted : Bool
SmoothPerelmanMonotonicityTheoremPromoted =
  false

RicciFlowBackReactionPromoted : Bool
RicciFlowBackReactionPromoted =
  false

SmoothPerelmanReducedVolumeTheoremPromoted : Bool
SmoothPerelmanReducedVolumeTheoremPromoted =
  false

RicciFlowClaimPromoted : Bool
RicciFlowClaimPromoted =
  false

GeometrizationClaimPromoted : Bool
GeometrizationClaimPromoted =
  false

ClayClaimPromoted : Bool
ClayClaimPromoted =
  false

TerminalGeometryClaimPromoted : Bool
TerminalGeometryClaimPromoted =
  false

gaussianDominanceTrue :
  GaussianDominatesExponentialGrowth ≡ true
gaussianDominanceTrue =
  refl

gaussianDominatesProductFortyTwoTrue :
  GaussianDominatesProductFortyTwoGrowth ≡ true
gaussianDominatesProductFortyTwoTrue =
  refl

reducedVolumeSeriesConvergesTrue :
  ReducedVolumeSeriesConverges ≡ true
reducedVolumeSeriesConvergesTrue =
  refl

smoothPerelmanMonotonicityPromotedFalse :
  SmoothPerelmanMonotonicityTheoremPromoted ≡ false
smoothPerelmanMonotonicityPromotedFalse =
  refl

ricciFlowBackReactionPromotedFalse :
  RicciFlowBackReactionPromoted ≡ false
ricciFlowBackReactionPromotedFalse =
  refl

smoothPerelmanReducedVolumePromotedFalse :
  SmoothPerelmanReducedVolumeTheoremPromoted ≡ false
smoothPerelmanReducedVolumePromotedFalse =
  refl

ricciFlowClaimPromotedFalse :
  RicciFlowClaimPromoted ≡ false
ricciFlowClaimPromotedFalse =
  refl

geometrizationClaimPromotedFalse :
  GeometrizationClaimPromoted ≡ false
geometrizationClaimPromotedFalse =
  refl

clayClaimPromotedFalse :
  ClayClaimPromoted ≡ false
clayClaimPromotedFalse =
  refl

terminalGeometryClaimPromotedFalse :
  TerminalGeometryClaimPromoted ≡ false
terminalGeometryClaimPromotedFalse =
  refl

data ForbiddenPromotionToken : Set where

forbiddenPromotionTokenImpossible :
  ForbiddenPromotionToken →
  ⊥
forbiddenPromotionTokenImpossible ()

record ControlCard : Set where
  field
    O :
      String

    R :
      String

    C :
      String

    S :
      String

    L :
      String

    P :
      String

    G :
      String

    F :
      String

open ControlCard public

canonicalControlCard : ControlCard
canonicalControlCard =
  record
    { O =
        "O: Worker 2 records a standalone DASHI BT/product-tree reduced-volume boundary receipt."
    ; R =
        "R: Name d^2/(4 tau), record 8 * 42^r sphere growth, Gaussian weight convergence, and keep theorem promotions false."
    ; C =
        "C: DASHI.Physics.Closure.BTGaussianReducedVolumeBoundary"
    ; S =
        "S: BTBallVolumeEntropyBoundary was not available during construction; the module is standalone."
    ; L =
        "L: formula receipt -> product T3xT2xT7 base 42 -> Gaussian dominance -> convergence flag true -> promotions false."
    ; P =
        "P: Use this only as a constructible discrete Gaussian reduced-volume analogue."
    ; G =
        "G: Agda typechecking and fail-closed false flags govern promotion."
    ; F =
        "F: No smooth monotonicity theorem, Ricci-flow back-reaction, geometrization proof, or Clay authority is supplied."
    }

record BTGaussianReducedVolumeBoundary : Set where
  field
    boundaryName :
      String

    productFactors :
      List ProductTreeFactor

    productFactorsAreCanonical :
      productFactors ≡ canonicalProductTreeFactors

    productBase :
      Nat

    productBaseIsFortyTwo :
      productBase ≡ productBranchingBase42

    productBaseComputationWitness :
      productT3xT2xT7Base ≡ productBranchingBase42

    spherePrefactor :
      Nat

    spherePrefactorIsEight :
      spherePrefactor ≡ productSpherePrefactor8

    namedReducedDistance :
      ReducedDistanceFormula

    namedReducedDistanceIsCanonical :
      namedReducedDistance ≡ canonicalReducedDistanceFormula

    sphereGrowth :
      SphereGrowthFormula

    sphereGrowthIsCanonical :
      sphereGrowth ≡ canonicalSphereGrowthFormula

    gaussianWeight :
      GaussianWeightFormula

    gaussianWeightIsCanonical :
      gaussianWeight ≡ canonicalGaussianWeightFormula

    reducedVolumeSeries :
      ReducedVolumeSeriesFormula

    reducedVolumeSeriesIsCanonical :
      reducedVolumeSeries ≡ canonicalGaussianReducedVolumeSeries

    convergenceReasons :
      List ConvergenceDominanceReason

    convergenceReasonsAreCanonical :
      convergenceReasons ≡ canonicalConvergenceReasons

    gaussianDominatesQPowerGrowth :
      Bool

    gaussianDominatesQPowerGrowthIsTrue :
      gaussianDominatesQPowerGrowth ≡ true

    gaussianDominatesProductFortyTwoPower :
      Bool

    gaussianDominatesProductFortyTwoPowerIsTrue :
      gaussianDominatesProductFortyTwoPower ≡ true

    convergenceFlag :
      Bool

    convergenceFlagIsTrue :
      convergenceFlag ≡ true

    constructibleStatus :
      List ConstructibleStatus

    constructibleStatusIsCanonical :
      constructibleStatus ≡ canonicalConstructibleStatus

    monotonicityTheoremFlag :
      Bool

    monotonicityTheoremFlagIsFalse :
      monotonicityTheoremFlag ≡ false

    backReactionFlag :
      Bool

    backReactionFlagIsFalse :
      backReactionFlag ≡ false

    smoothPerelmanReducedVolumeTheoremFlag :
      Bool

    smoothPerelmanReducedVolumeTheoremFlagIsFalse :
      smoothPerelmanReducedVolumeTheoremFlag ≡ false

    ricciFlowPromotion :
      Bool

    ricciFlowPromotionIsFalse :
      ricciFlowPromotion ≡ false

    geometrizationPromotion :
      Bool

    geometrizationPromotionIsFalse :
      geometrizationPromotion ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    terminalGeometryPromotion :
      Bool

    terminalGeometryPromotionIsFalse :
      terminalGeometryPromotion ≡ false

    forbiddenPromotionTokens :
      List ForbiddenPromotionToken

    forbiddenPromotionTokensAreEmpty :
      forbiddenPromotionTokens ≡ []

    controlCard :
      ControlCard

    formulaNotes :
      List String

open BTGaussianReducedVolumeBoundary public

canonicalBTGaussianReducedVolumeBoundary :
  BTGaussianReducedVolumeBoundary
canonicalBTGaussianReducedVolumeBoundary =
  record
    { boundaryName =
        "BT/product-tree Gaussian reduced-volume analogue boundary"
    ; productFactors =
        canonicalProductTreeFactors
    ; productFactorsAreCanonical =
        refl
    ; productBase =
        productBranchingBase42
    ; productBaseIsFortyTwo =
        refl
    ; productBaseComputationWitness =
        productBaseComputesTo42
    ; spherePrefactor =
        productSpherePrefactor8
    ; spherePrefactorIsEight =
        refl
    ; namedReducedDistance =
        canonicalReducedDistanceFormula
    ; namedReducedDistanceIsCanonical =
        refl
    ; sphereGrowth =
        canonicalSphereGrowthFormula
    ; sphereGrowthIsCanonical =
        refl
    ; gaussianWeight =
        canonicalGaussianWeightFormula
    ; gaussianWeightIsCanonical =
        refl
    ; reducedVolumeSeries =
        canonicalGaussianReducedVolumeSeries
    ; reducedVolumeSeriesIsCanonical =
        refl
    ; convergenceReasons =
        canonicalConvergenceReasons
    ; convergenceReasonsAreCanonical =
        refl
    ; gaussianDominatesQPowerGrowth =
        GaussianDominatesExponentialGrowth
    ; gaussianDominatesQPowerGrowthIsTrue =
        gaussianDominanceTrue
    ; gaussianDominatesProductFortyTwoPower =
        GaussianDominatesProductFortyTwoGrowth
    ; gaussianDominatesProductFortyTwoPowerIsTrue =
        gaussianDominatesProductFortyTwoTrue
    ; convergenceFlag =
        ReducedVolumeSeriesConverges
    ; convergenceFlagIsTrue =
        reducedVolumeSeriesConvergesTrue
    ; constructibleStatus =
        canonicalConstructibleStatus
    ; constructibleStatusIsCanonical =
        refl
    ; monotonicityTheoremFlag =
        SmoothPerelmanMonotonicityTheoremPromoted
    ; monotonicityTheoremFlagIsFalse =
        smoothPerelmanMonotonicityPromotedFalse
    ; backReactionFlag =
        RicciFlowBackReactionPromoted
    ; backReactionFlagIsFalse =
        ricciFlowBackReactionPromotedFalse
    ; smoothPerelmanReducedVolumeTheoremFlag =
        SmoothPerelmanReducedVolumeTheoremPromoted
    ; smoothPerelmanReducedVolumeTheoremFlagIsFalse =
        smoothPerelmanReducedVolumePromotedFalse
    ; ricciFlowPromotion =
        RicciFlowClaimPromoted
    ; ricciFlowPromotionIsFalse =
        ricciFlowClaimPromotedFalse
    ; geometrizationPromotion =
        GeometrizationClaimPromoted
    ; geometrizationPromotionIsFalse =
        geometrizationClaimPromotedFalse
    ; clayPromotion =
        ClayClaimPromoted
    ; clayPromotionIsFalse =
        clayClaimPromotedFalse
    ; terminalGeometryPromotion =
        TerminalGeometryClaimPromoted
    ; terminalGeometryPromotionIsFalse =
        terminalGeometryClaimPromotedFalse
    ; forbiddenPromotionTokens =
        []
    ; forbiddenPromotionTokensAreEmpty =
        refl
    ; controlCard =
        canonicalControlCard
    ; formulaNotes =
        reducedDistanceFormulaText
        ∷ sphereGrowthFormulaText
        ∷ gaussianWeightFormulaText
        ∷ seriesFormulaText
        ∷ "convergenceFlag=true because exp(-r^2/(4 tau)) dominates q^r and in particular 42^r"
        ∷ "SmoothPerelmanMonotonicityTheoremPromoted=false and RicciFlowBackReactionPromoted=false"
        ∷ "RicciFlowClaimPromoted=false, GeometrizationClaimPromoted=false, ClayClaimPromoted=false"
        ∷ []
    }

canonicalReducedDistanceFormulaRecorded :
  namedReducedDistance canonicalBTGaussianReducedVolumeBoundary
  ≡
  canonicalReducedDistanceFormula
canonicalReducedDistanceFormulaRecorded =
  refl

canonicalProductBaseFortyTwoRecorded :
  productBase canonicalBTGaussianReducedVolumeBoundary
  ≡
  42
canonicalProductBaseFortyTwoRecorded =
  refl

canonicalSpherePrefactorEightRecorded :
  spherePrefactor canonicalBTGaussianReducedVolumeBoundary
  ≡
  8
canonicalSpherePrefactorEightRecorded =
  refl

canonicalConvergenceFlagTrue :
  convergenceFlag canonicalBTGaussianReducedVolumeBoundary
  ≡
  true
canonicalConvergenceFlagTrue =
  refl

canonicalMonotonicityFlagFalse :
  monotonicityTheoremFlag canonicalBTGaussianReducedVolumeBoundary
  ≡
  false
canonicalMonotonicityFlagFalse =
  refl

canonicalBackReactionFlagFalse :
  backReactionFlag canonicalBTGaussianReducedVolumeBoundary
  ≡
  false
canonicalBackReactionFlagFalse =
  refl

canonicalSmoothPerelmanReducedVolumeFlagFalse :
  smoothPerelmanReducedVolumeTheoremFlag
    canonicalBTGaussianReducedVolumeBoundary
  ≡
  false
canonicalSmoothPerelmanReducedVolumeFlagFalse =
  refl

canonicalRicciFlowPromotionFalse :
  ricciFlowPromotion canonicalBTGaussianReducedVolumeBoundary
  ≡
  false
canonicalRicciFlowPromotionFalse =
  refl

canonicalGeometrizationPromotionFalse :
  geometrizationPromotion canonicalBTGaussianReducedVolumeBoundary
  ≡
  false
canonicalGeometrizationPromotionFalse =
  refl

canonicalClayPromotionFalse :
  clayPromotion canonicalBTGaussianReducedVolumeBoundary
  ≡
  false
canonicalClayPromotionFalse =
  refl

canonicalForbiddenPromotionTokensEmpty :
  forbiddenPromotionTokens canonicalBTGaussianReducedVolumeBoundary
  ≡
  []
canonicalForbiddenPromotionTokensEmpty =
  refl
