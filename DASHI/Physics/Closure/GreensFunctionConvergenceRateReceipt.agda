module DASHI.Physics.Closure.GreensFunctionConvergenceRateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Green's-function convergence-rate heuristic receipt.
--
-- This receipt records only the symbolic wave-pool heuristic:
-- N-caisson/carrier approximants suggest an inverse-power rate with shape
-- N^-((k-s)/dim).  Smooth Yang-Mills vacuum data are marked favorable at
-- heuristic scope, while Navier-Stokes at s = k = 11/8 is recorded as the
-- boundary case with no finite-rate gain.  No formal analytic convergence
-- bound, Gate 3 promotion, or Clay promotion is produced here.

data ClaimScope : Set where
  computed :
    ClaimScope

  heuristic :
    ClaimScope

  formalBoundRequired :
    ClaimScope

data WavePoolApproximantFamily : Set where
  nCaissonCarrierApproximants :
    WavePoolApproximantFamily

data SmoothnessTag : Set where
  elevenOverEight :
    SmoothnessTag

  smoothYangMillsVacuumTag :
    SmoothnessTag

data DimensionTag : Set where
  carrierDimension :
    Nat →
    DimensionTag

data RateShape : Set where
  nPowerMinusKMinusSOverDim :
    SmoothnessTag →
    SmoothnessTag →
    DimensionTag →
    RateShape

data ConvergenceRateClass : Set where
  positiveFinitePowerHeuristic :
    ConvergenceRateClass

  superpolynomialHeuristic :
    ConvergenceRateClass

  boundaryNoFiniteRateGain :
    ConvergenceRateClass

  openFormalAnalyticBound :
    ConvergenceRateClass

data PhysicalRegime : Set where
  smoothYangMillsVacuum :
    PhysicalRegime

  navierStokesElevenOverEightBoundary :
    PhysicalRegime

computedRateScope : ClaimScope
computedRateScope =
  computed

heuristicRateScope : ClaimScope
heuristicRateScope =
  heuristic

formalBoundScope : ClaimScope
formalBoundScope =
  formalBoundRequired

canonicalWavePoolDimension : DimensionTag
canonicalWavePoolDimension =
  carrierDimension (suc (suc (suc zero)))

canonicalYMRateShape : RateShape
canonicalYMRateShape =
  nPowerMinusKMinusSOverDim
    smoothYangMillsVacuumTag
    elevenOverEight
    canonicalWavePoolDimension

canonicalNSBoundaryRateShape : RateShape
canonicalNSBoundaryRateShape =
  nPowerMinusKMinusSOverDim
    elevenOverEight
    elevenOverEight
    canonicalWavePoolDimension

rateClassForRegime : PhysicalRegime → ConvergenceRateClass
rateClassForRegime smoothYangMillsVacuum =
  superpolynomialHeuristic
rateClassForRegime navierStokesElevenOverEightBoundary =
  boundaryNoFiniteRateGain

finiteRateGainRecorded : PhysicalRegime → Bool
finiteRateGainRecorded smoothYangMillsVacuum =
  true
finiteRateGainRecorded navierStokesElevenOverEightBoundary =
  false

formalAnalyticBoundProvedHere : PhysicalRegime → Bool
formalAnalyticBoundProvedHere smoothYangMillsVacuum =
  false
formalAnalyticBoundProvedHere navierStokesElevenOverEightBoundary =
  false

data GreensFunctionPromotion : Set where

greensFunctionPromotionImpossibleHere :
  GreensFunctionPromotion →
  ClaimScope
greensFunctionPromotionImpossibleHere ()

greenFunctionRateBoundaryStatement : String
greenFunctionRateBoundaryStatement =
  "Green's-function convergence is recorded as a symbolic wave-pool heuristic with N-caisson/carrier approximants and rate shape N^-((k-s)/dim); a formal analytic bound remains open."

smoothYMVacuumBoundaryStatement : String
smoothYMVacuumBoundaryStatement =
  "Smooth Yang-Mills vacuum input is favorable only at heuristic scope and is recorded as superpolynomial-shaped, not as a proved continuum mass-gap or Clay result."

navierStokesBoundaryStatement : String
navierStokesBoundaryStatement =
  "Navier-Stokes at s = k = 11/8 is the boundary case: the symbolic exponent has no positive finite-rate gain, and the analytic bound is still required."

record GreensFunctionConvergenceRateReceipt : Setω where
  field
    approximantFamily :
      WavePoolApproximantFamily

    approximantFamilyIsCanonical :
      approximantFamily ≡ nCaissonCarrierApproximants

    rateShapeScope :
      ClaimScope

    rateShapeScopeIsComputed :
      rateShapeScope ≡ computed

    ymRegime :
      PhysicalRegime

    ymRegimeIsSmoothVacuum :
      ymRegime ≡ smoothYangMillsVacuum

    ymRateShape :
      RateShape

    ymRateShapeIsCanonical :
      ymRateShape ≡ canonicalYMRateShape

    ymRateClass :
      ConvergenceRateClass

    ymRateClassIsSuperpolynomialHeuristic :
      ymRateClass ≡ rateClassForRegime ymRegime

    ymHeuristicScope :
      ClaimScope

    ymHeuristicScopeIsHeuristic :
      ymHeuristicScope ≡ heuristic

    ymSmoothVacuumFavorableHeuristic :
      Bool

    ymSmoothVacuumFavorableHeuristicIsTrue :
      ymSmoothVacuumFavorableHeuristic ≡ true

    ymFormalAnalyticBoundProvedHere :
      Bool

    ymFormalAnalyticBoundProvedHereIsFalse :
      ymFormalAnalyticBoundProvedHere ≡ false

    nsRegime :
      PhysicalRegime

    nsRegimeIsElevenOverEightBoundary :
      nsRegime ≡ navierStokesElevenOverEightBoundary

    nsRateShape :
      RateShape

    nsRateShapeIsBoundaryShape :
      nsRateShape ≡ canonicalNSBoundaryRateShape

    nsRateClass :
      ConvergenceRateClass

    nsRateClassIsBoundaryNoFiniteGain :
      nsRateClass ≡ rateClassForRegime nsRegime

    nsFiniteRateGain :
      Bool

    nsFiniteRateGainIsFalse :
      nsFiniteRateGain ≡ finiteRateGainRecorded nsRegime

    nsBoundaryScope :
      ClaimScope

    nsBoundaryScopeIsComputed :
      nsBoundaryScope ≡ computed

    formalBoundScopeField :
      ClaimScope

    formalBoundScopeIsRequired :
      formalBoundScopeField ≡ formalBoundRequired

    formalAnalyticBoundRequired :
      Bool

    formalAnalyticBoundRequiredIsTrue :
      formalAnalyticBoundRequired ≡ true

    ymFormalAnalyticBoundProvedHereMatchesRegime :
      ymFormalAnalyticBoundProvedHere ≡ formalAnalyticBoundProvedHere ymRegime

    nsFormalAnalyticBoundProvedHere :
      Bool

    nsFormalAnalyticBoundProvedHereMatchesRegime :
      nsFormalAnalyticBoundProvedHere ≡ formalAnalyticBoundProvedHere nsRegime

    nsFormalAnalyticBoundProvedHereIsFalse :
      nsFormalAnalyticBoundProvedHere ≡ false

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotionFlags :
      List GreensFunctionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open GreensFunctionConvergenceRateReceipt public

canonicalGreensFunctionConvergenceRateReceipt :
  GreensFunctionConvergenceRateReceipt
canonicalGreensFunctionConvergenceRateReceipt =
  record
    { approximantFamily =
        nCaissonCarrierApproximants
    ; approximantFamilyIsCanonical =
        refl
    ; rateShapeScope =
        computedRateScope
    ; rateShapeScopeIsComputed =
        refl
    ; ymRegime =
        smoothYangMillsVacuum
    ; ymRegimeIsSmoothVacuum =
        refl
    ; ymRateShape =
        canonicalYMRateShape
    ; ymRateShapeIsCanonical =
        refl
    ; ymRateClass =
        superpolynomialHeuristic
    ; ymRateClassIsSuperpolynomialHeuristic =
        refl
    ; ymHeuristicScope =
        heuristicRateScope
    ; ymHeuristicScopeIsHeuristic =
        refl
    ; ymSmoothVacuumFavorableHeuristic =
        true
    ; ymSmoothVacuumFavorableHeuristicIsTrue =
        refl
    ; ymFormalAnalyticBoundProvedHere =
        false
    ; ymFormalAnalyticBoundProvedHereIsFalse =
        refl
    ; nsRegime =
        navierStokesElevenOverEightBoundary
    ; nsRegimeIsElevenOverEightBoundary =
        refl
    ; nsRateShape =
        canonicalNSBoundaryRateShape
    ; nsRateShapeIsBoundaryShape =
        refl
    ; nsRateClass =
        boundaryNoFiniteRateGain
    ; nsRateClassIsBoundaryNoFiniteGain =
        refl
    ; nsFiniteRateGain =
        false
    ; nsFiniteRateGainIsFalse =
        refl
    ; nsBoundaryScope =
        computedRateScope
    ; nsBoundaryScopeIsComputed =
        refl
    ; formalBoundScopeField =
        formalBoundScope
    ; formalBoundScopeIsRequired =
        refl
    ; formalAnalyticBoundRequired =
        true
    ; formalAnalyticBoundRequiredIsTrue =
        refl
    ; ymFormalAnalyticBoundProvedHereMatchesRegime =
        refl
    ; nsFormalAnalyticBoundProvedHere =
        false
    ; nsFormalAnalyticBoundProvedHereMatchesRegime =
        refl
    ; nsFormalAnalyticBoundProvedHereIsFalse =
        refl
    ; gate3Promoted =
        false
    ; gate3PromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        greenFunctionRateBoundaryStatement
        ∷ smoothYMVacuumBoundaryStatement
        ∷ navierStokesBoundaryStatement
        ∷ []
    }
