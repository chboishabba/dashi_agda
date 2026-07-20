module DASHI.Physics.Closure.ShiftFixedPointRGCFTHandoff where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as Envelope
open import DASHI.Physics.Closure.FixedPointAnalyticRGTargets as Analytic
open import DASHI.Physics.Closure.FixedPointCFTBoundary as Boundary
open import DASHI.Physics.Closure.ShiftFiniteLocalOPECrossing as OPE
open import DASHI.Physics.Closure.ShiftFiniteNormedTangent as Normed
open import DASHI.Physics.Closure.ShiftFiniteScalingFusionWard as Finite
open import DASHI.Physics.Closure.ShiftFiniteTangentSemigroup as Tangent

------------------------------------------------------------------------
-- Integrated finite RG/CFT precursor handoff.
--
-- The current branch now closes stronger finite algebraic versions of the
-- tangent, norm, semigroup, scaling, OPE, crossing, correlation, and Ward
-- lanes.  The actual analytic/continuum theorem remains represented by the
-- explicit FixedPointAnalyticRGCFTRoute target below.

data ShiftRGCFTRemainingGate : Set where
  vectorSpaceAndBanachTangentRequired : ShiftRGCFTRemainingGate
  frechetDerivativeAndAnalyticGeneratorRequired : ShiftRGCFTRemainingGate
  physicalScalingDimensionsRequired : ShiftRGCFTRemainingGate
  analyticLocalOPECoefficientsRequired : ShiftRGCFTRemainingGate
  inhabitedContinuousDepthEnvelopeRequired : ShiftRGCFTRemainingGate
  renormalizationCompatibilityAcrossDepthRequired : ShiftRGCFTRemainingGate
  stressTensorAndConformalWardRequired : ShiftRGCFTRemainingGate

data ShiftRGCFTRemainingPromotion : Set where

shiftRGCFTPromotionImpossibleHere :
  ShiftRGCFTRemainingPromotion →
  ⊥
shiftRGCFTPromotionImpossibleHere ()

record ShiftFixedPointRGCFTHandoff : Setω where
  field
    priorBoundary : Boundary.FixedPointCFTBoundary
    tangentSemigroup : Tangent.ShiftFiniteTangentSemigroup
    finiteNormedTangent : Normed.ShiftFiniteNormedTangent
    scalingFusionWard : Finite.ShiftFiniteScalingFusionWard
    finiteLocalOPECrossing : OPE.ShiftFiniteLocalOPECrossing

    finiteTangentCarrierConstructed : Bool
    finiteTangentCarrierConstructedIsTrue :
      finiteTangentCarrierConstructed ≡ true

    finiteDerivativeSemigroupConstructed : Bool
    finiteDerivativeSemigroupConstructedIsTrue :
      finiteDerivativeSemigroupConstructed ≡ true

    finiteAdditiveNormedStructureConstructed : Bool
    finiteAdditiveNormedStructureConstructedIsTrue :
      finiteAdditiveNormedStructureConstructed ≡ true

    finiteScalingSpectrumConstructed : Bool
    finiteScalingSpectrumConstructedIsTrue :
      finiteScalingSpectrumConstructed ≡ true

    finiteFusionLawConstructed : Bool
    finiteFusionLawConstructedIsTrue :
      finiteFusionLawConstructed ≡ true

    finiteLocalOPECoefficientsConstructed : Bool
    finiteLocalOPECoefficientsConstructedIsTrue :
      finiteLocalOPECoefficientsConstructed ≡ true

    finiteCrossingConstructed : Bool
    finiteCrossingConstructedIsTrue :
      finiteCrossingConstructed ≡ true

    finiteCorrelationWardConstructed : Bool
    finiteCorrelationWardConstructedIsTrue :
      finiteCorrelationWardConstructed ≡ true

    analyticRouteTarget : Setω
    analyticRouteTargetIsCanonical :
      analyticRouteTarget ≡ Analytic.FixedPointAnalyticRGCFTRoute

    depthKernelModelTarget : Set₁
    depthKernelModelTargetIsCanonical :
      depthKernelModelTarget ≡ Envelope.DepthKernelModel

    continuousEnvelopeTarget :
      Envelope.DepthKernelModel →
      Set₁
    continuousEnvelopeTargetIsCanonical :
      continuousEnvelopeTarget ≡ Envelope.ContinuousDepthEnvelope

    continuousEnvelopeInhabitedHere : Bool
    continuousEnvelopeInhabitedHereIsFalse :
      continuousEnvelopeInhabitedHere ≡ false

    analyticFrechetGeneratorConstructed : Bool
    analyticFrechetGeneratorConstructedIsFalse :
      analyticFrechetGeneratorConstructed ≡ false

    physicalScalingSpectrumConstructed : Bool
    physicalScalingSpectrumConstructedIsFalse :
      physicalScalingSpectrumConstructed ≡ false

    analyticLocalOPEConstructed : Bool
    analyticLocalOPEConstructedIsFalse :
      analyticLocalOPEConstructed ≡ false

    continuumRGControlConstructed : Bool
    continuumRGControlConstructedIsFalse :
      continuumRGControlConstructed ≡ false

    continuumConformalWardConstructed : Bool
    continuumConformalWardConstructedIsFalse :
      continuumConformalWardConstructed ≡ false

    cftPromoted : Bool
    cftPromotedIsFalse : cftPromoted ≡ false

    remainingGates : List ShiftRGCFTRemainingGate
    promotions : List ShiftRGCFTRemainingPromotion
    promotionsAreEmpty : promotions ≡ []
    noPromotionPossibleHere : ShiftRGCFTRemainingPromotion → ⊥

    boundary : List String

open ShiftFixedPointRGCFTHandoff public

canonicalShiftRGCFTRemainingGates :
  List ShiftRGCFTRemainingGate
canonicalShiftRGCFTRemainingGates =
  vectorSpaceAndBanachTangentRequired
  ∷ frechetDerivativeAndAnalyticGeneratorRequired
  ∷ physicalScalingDimensionsRequired
  ∷ analyticLocalOPECoefficientsRequired
  ∷ inhabitedContinuousDepthEnvelopeRequired
  ∷ renormalizationCompatibilityAcrossDepthRequired
  ∷ stressTensorAndConformalWardRequired
  ∷ []

canonicalShiftFixedPointRGCFTHandoff :
  ShiftFixedPointRGCFTHandoff
canonicalShiftFixedPointRGCFTHandoff =
  record
    { priorBoundary = Boundary.canonicalFixedPointCFTBoundary
    ; tangentSemigroup = Tangent.canonicalShiftFiniteTangentSemigroup
    ; finiteNormedTangent = Normed.canonicalShiftFiniteNormedTangent
    ; scalingFusionWard = Finite.canonicalShiftFiniteScalingFusionWard
    ; finiteLocalOPECrossing = OPE.canonicalShiftFiniteLocalOPECrossing
    ; finiteTangentCarrierConstructed = true
    ; finiteTangentCarrierConstructedIsTrue = refl
    ; finiteDerivativeSemigroupConstructed = true
    ; finiteDerivativeSemigroupConstructedIsTrue = refl
    ; finiteAdditiveNormedStructureConstructed = true
    ; finiteAdditiveNormedStructureConstructedIsTrue = refl
    ; finiteScalingSpectrumConstructed = true
    ; finiteScalingSpectrumConstructedIsTrue = refl
    ; finiteFusionLawConstructed = true
    ; finiteFusionLawConstructedIsTrue = refl
    ; finiteLocalOPECoefficientsConstructed = true
    ; finiteLocalOPECoefficientsConstructedIsTrue = refl
    ; finiteCrossingConstructed = true
    ; finiteCrossingConstructedIsTrue = refl
    ; finiteCorrelationWardConstructed = true
    ; finiteCorrelationWardConstructedIsTrue = refl
    ; analyticRouteTarget = Analytic.FixedPointAnalyticRGCFTRoute
    ; analyticRouteTargetIsCanonical = refl
    ; depthKernelModelTarget = Envelope.DepthKernelModel
    ; depthKernelModelTargetIsCanonical = refl
    ; continuousEnvelopeTarget = Envelope.ContinuousDepthEnvelope
    ; continuousEnvelopeTargetIsCanonical = refl
    ; continuousEnvelopeInhabitedHere = false
    ; continuousEnvelopeInhabitedHereIsFalse = refl
    ; analyticFrechetGeneratorConstructed = false
    ; analyticFrechetGeneratorConstructedIsFalse = refl
    ; physicalScalingSpectrumConstructed = false
    ; physicalScalingSpectrumConstructedIsFalse = refl
    ; analyticLocalOPEConstructed = false
    ; analyticLocalOPEConstructedIsFalse = refl
    ; continuumRGControlConstructed = false
    ; continuumRGControlConstructedIsFalse = refl
    ; continuumConformalWardConstructed = false
    ; continuumConformalWardConstructedIsFalse = refl
    ; cftPromoted = false
    ; cftPromotedIsFalse = refl
    ; remainingGates = canonicalShiftRGCFTRemainingGates
    ; promotions = []
    ; promotionsAreEmpty = refl
    ; noPromotionPossibleHere = shiftRGCFTPromotionImpossibleHere
    ; boundary =
        "The finite shift lane now has a pointed perturbation semigroup and an exact normed idempotent additive algebra"
        ∷ "the finite derivative preserves addition and is norm non-increasing"
        ∷ "the finite 2,1,0 spectrum is inherited from the established held-potential/collapse-depth rank"
        ∷ "the finite operator algebra now has proof-relevant OPE coefficients, exchange locality, and associative crossing"
        ∷ "the finite correlation and held-insertion Ward analogues remain attached"
        ∷ "FixedPointAnalyticRGCFTRoute names the exact stronger analytic objects still required"
        ∷ "the current additive tangent is not a vector/Banach space and the finite derivative is not a Frechet derivative"
        ∷ "the finite OPE has no singular position dependence, analytic coefficient functions, or conformal blocks"
        ∷ "an inhabited analytic envelope, RG-depth compatibility, physical dimensions, analytic OPE, stress tensor, and conformal Ward identities remain open"
        ∷ "No continuum RG fixed point or CFT is promoted"
        ∷ []
    }
