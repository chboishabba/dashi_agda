module DASHI.Physics.Closure.NSTailFluxAbsorptionMarginReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes tail-flux absorption margin receipt.
--
-- This is a symbolic, conditional receipt.  It records the sharpened
-- invariant surface:
--
--   TailCarry_K decreases if Flux_K is absorbed by Diss_K with margin theta
--   and theta < 1.
--
-- The tail-flux identity is recorded only for a fixed shell cutoff K during
-- differentiation:
--
--   d/dt TailEnergy_K = - Diss_K + Flux_K.
--
-- The danger shell and theta argmax are separate diagnostics computed after
-- the fixed-K profile is available.  This receipt does not provide a moving
-- cutoff theorem.
--
-- The hard analytic inhabitant is not supplied here.  In particular this
-- file does not prove NonlinearFlux <= ViscousDissipation, does not construct
-- a real-valued theta estimate from Navier-Stokes analysis, does not prove
-- theta monotonicity, does not identify theta with BKM, and does not promote
-- Clay/regularity closure.

data TailCarry_K : Nat → Set where
  tailCarry :
    (K : Nat) →
    TailCarry_K K

data Flux_K : Nat → Set where
  nonlinearFlux :
    (K : Nat) →
    Flux_K K

data Diss_K : Nat → Set where
  viscousDissipation :
    (K : Nat) →
    Diss_K K

data TailEnergyDerivative_K : Nat → Set where
  derivativeOfFixedCutoffTailEnergy :
    (K : Nat) →
    TailEnergyDerivative_K K

data FixedCutoffDifferentiationStatus : Set where
  shellCutoffKFixedDuringDifferentiation :
    FixedCutoffDifferentiationStatus

data FixedKSemantics : Set where
  fixedKSelectedBeforeDifferentiation :
    FixedKSemantics

  noKDependenceIntroducedInsideDerivative :
    FixedKSemantics

canonicalFixedKSemantics :
  List FixedKSemantics
canonicalFixedKSemantics =
  fixedKSelectedBeforeDifferentiation
  ∷ noKDependenceIntroducedInsideDerivative
  ∷ []

data TailFluxIdentity_K : Nat → Set where
  fixedCutoffTailFluxIdentity :
    (K : Nat) →
    TailEnergyDerivative_K K →
    Diss_K K →
    Flux_K K →
    TailFluxIdentity_K K

data DangerShellThetaArgmaxStatus : Set where
  dangerShellThetaArgmaxComputedAfterFixedKProfile :
    DangerShellThetaArgmaxStatus

data ThetaProfileComputabilityStatus : Set where
  thetaProfileComputableAfterFixedKFluxDissProfile :
    ThetaProfileComputabilityStatus

data MovingCutoffTheoremStatus : Set where
  noMovingCutoffTheoremProvided :
    MovingCutoffTheoremStatus

data Theta : Set where
  symbolicTheta :
    Theta

data ThetaLessThanOne : Theta → Set where
  symbolicThetaLessThanOne :
    ThetaLessThanOne symbolicTheta

data TailFluxAbsorptionMargin : Nat → Set where
  tailFluxAbsorptionMargin :
    (K : Nat) →
    (theta : Theta) →
    ThetaLessThanOne theta →
    TailCarry_K K →
    Flux_K K →
    Diss_K K →
    TailFluxAbsorptionMargin K

canonicalTailFluxAbsorptionMargin :
  (K : Nat) →
  TailFluxAbsorptionMargin K
canonicalTailFluxAbsorptionMargin K =
  tailFluxAbsorptionMargin
    K
    symbolicTheta
    symbolicThetaLessThanOne
    (tailCarry K)
    (nonlinearFlux K)
    (viscousDissipation K)

canonicalTailFluxIdentity :
  (K : Nat) →
  TailFluxIdentity_K K
canonicalTailFluxIdentity K =
  fixedCutoffTailFluxIdentity
    K
    (derivativeOfFixedCutoffTailEnergy K)
    (viscousDissipation K)
    (nonlinearFlux K)

tailFluxAbsorptionTheta :
  {K : Nat} →
  TailFluxAbsorptionMargin K →
  Theta
tailFluxAbsorptionTheta
  (tailFluxAbsorptionMargin K theta theta<1 carry flux diss) =
  theta

tailFluxAbsorptionThetaLessThanOne :
  {K : Nat} →
  (margin : TailFluxAbsorptionMargin K) →
  ThetaLessThanOne (tailFluxAbsorptionTheta margin)
tailFluxAbsorptionThetaLessThanOne
  (tailFluxAbsorptionMargin K theta theta<1 carry flux diss) =
  theta<1

data TailCarryDecreaseConclusion : Nat → Set where
  tailCarryDecreasesUnderAbsorptionMargin :
    (K : Nat) →
    TailCarryDecreaseConclusion K

data TailDecayConclusion : Nat → Set where
  tailDecayFollowsConditionallyFromThetaAbsorptionMargin :
    (K : Nat) →
    TailDecayConclusion K

tailCarryDecreases :
  {K : Nat} →
  TailFluxAbsorptionMargin K →
  TailCarryDecreaseConclusion K
tailCarryDecreases {K} margin =
  tailCarryDecreasesUnderAbsorptionMargin K

thetaLessThanOneImpliesTailDecayConditionally :
  {K : Nat} →
  TailFluxAbsorptionMargin K →
  TailDecayConclusion K
thetaLessThanOneImpliesTailDecayConditionally {K} margin =
  tailDecayFollowsConditionallyFromThetaAbsorptionMargin K

data NSMarginInvariantScope : Set where
  tailCarryKSymbolicData :
    NSMarginInvariantScope

  fluxKSymbolicData :
    NSMarginInvariantScope

  dissKSymbolicData :
    NSMarginInvariantScope

  fixedCutoffKDuringDifferentiation :
    NSMarginInvariantScope

  fixedKSelectedBeforeDifferentiationScope :
    NSMarginInvariantScope

  exactTailFluxIdentityForFixedK :
    NSMarginInvariantScope

  thetaProfileComputableAfterFixedKProfile :
    NSMarginInvariantScope

  dangerShellThetaArgmaxComputedSeparately :
    NSMarginInvariantScope

  thetaAndThetaLessThanOneMarginWitness :
    NSMarginInvariantScope

  tailCarryDecreaseConditionalOnMargin :
    NSMarginInvariantScope

  thetaLessThanOneTailDecayConditionalScope :
    NSMarginInvariantScope

  thetaTailAbsorptionConditionalScope :
    NSMarginInvariantScope

  thetaContinuationConditionalScope :
    NSMarginInvariantScope

  thetaBKMEquivalenceNotProvedScope :
    NSMarginInvariantScope

canonicalNSMarginInvariantScope :
  List NSMarginInvariantScope
canonicalNSMarginInvariantScope =
  tailCarryKSymbolicData
  ∷ fluxKSymbolicData
  ∷ dissKSymbolicData
  ∷ fixedCutoffKDuringDifferentiation
  ∷ fixedKSelectedBeforeDifferentiationScope
  ∷ exactTailFluxIdentityForFixedK
  ∷ thetaProfileComputableAfterFixedKProfile
  ∷ dangerShellThetaArgmaxComputedSeparately
  ∷ thetaAndThetaLessThanOneMarginWitness
  ∷ tailCarryDecreaseConditionalOnMargin
  ∷ thetaLessThanOneTailDecayConditionalScope
  ∷ thetaTailAbsorptionConditionalScope
  ∷ thetaContinuationConditionalScope
  ∷ thetaBKMEquivalenceNotProvedScope
  ∷ []

data NSMarginAnalyticMissingInhabitant : Set where
  nonlinearFluxLeViscousDissipation :
    NSMarginAnalyticMissingInhabitant

  thetaLessThanOneFromAnalyticEstimate :
    NSMarginAnalyticMissingInhabitant

  thetaHighShellDecay :
    NSMarginAnalyticMissingInhabitant

  thetaBKMEquivalence :
    NSMarginAnalyticMissingInhabitant

canonicalNSMarginAnalyticMissingInhabitants :
  List NSMarginAnalyticMissingInhabitant
canonicalNSMarginAnalyticMissingInhabitants =
  nonlinearFluxLeViscousDissipation
  ∷ thetaLessThanOneFromAnalyticEstimate
  ∷ thetaHighShellDecay
  ∷ thetaBKMEquivalence
  ∷ []

data NSMarginBoundary : Set where
  conditionalReceiptOnly :
    NSMarginBoundary

  nonlinearFluxViscousDissipationHardAnalyticGap :
    NSMarginBoundary

  thetaLessThanOneHardAnalyticGap :
    NSMarginBoundary

  thetaHighShellDecayOpenBoundary :
    NSMarginBoundary

  thetaObservationsNotNSRegularity :
    NSMarginBoundary

  thetaBKMEquivalenceNotProved :
    NSMarginBoundary

  noMovingCutoffTheorem :
    NSMarginBoundary

  noNavierStokesRegularityPromotion :
    NSMarginBoundary

  noClayPromotion :
    NSMarginBoundary

canonicalNSMarginBoundaries :
  List NSMarginBoundary
canonicalNSMarginBoundaries =
  conditionalReceiptOnly
  ∷ nonlinearFluxViscousDissipationHardAnalyticGap
  ∷ thetaLessThanOneHardAnalyticGap
  ∷ thetaHighShellDecayOpenBoundary
  ∷ thetaObservationsNotNSRegularity
  ∷ thetaBKMEquivalenceNotProved
  ∷ noMovingCutoffTheorem
  ∷ noNavierStokesRegularityPromotion
  ∷ noClayPromotion
  ∷ []

data NSTailFluxAbsorptionMarginPromotion : Set where

nsTailFluxAbsorptionMarginPromotionImpossibleHere :
  NSTailFluxAbsorptionMarginPromotion →
  ⊥
nsTailFluxAbsorptionMarginPromotionImpossibleHere ()

nsTailFluxAbsorptionMarginStatement : String
nsTailFluxAbsorptionMarginStatement =
  "TailCarry_K, Flux_K, Diss_K, and d/dt TailEnergy_K are symbolic fixed-cutoff data. The receipt records d/dt TailEnergy_K = -Diss_K + Flux_K only with shell cutoff K fixed during differentiation. Danger shell/theta argmax is computed separately from the fixed-K profile. No moving-cutoff theorem, Navier-Stokes regularity, Clay, or terminal promotion is made."

fixedKSemanticsStatement :
  String
fixedKSemanticsStatement =
  "Fixed-K semantics: K is selected before differentiating TailEnergy_K, and no moving cutoff or K(t) dependence is introduced inside d/dt."

tailFluxIdentityStatement :
  String
tailFluxIdentityStatement =
  "Fixed-cutoff identity: for each fixed shell cutoff K during differentiation, d/dt TailEnergy_K decomposes exactly as -Diss_K + Flux_K."

thetaProfileComputabilityStatement :
  String
thetaProfileComputabilityStatement =
  "Theta profile computability is a post-fixed-K diagnostic: compute Flux_K and Diss_K over the selected fixed-K profile, then compute theta and the danger-shell argmax separately."

thetaTailDecayStatement :
  String
thetaTailDecayStatement =
  "Within this symbolic receipt only, theta<1 plus the recorded absorption-margin witness yields a conditional tail-decay conclusion; the analytic proof that real NS data supplies that witness remains open."

thetaDangerShellStatement :
  String
thetaDangerShellStatement =
  "Danger shell and theta argmax are runtime/profile diagnostics computed after the fixed-K tail-flux profile; they are not part of differentiating a moving cutoff."

thetaObservationNonPromotionStatement :
  String
thetaObservationNonPromotionStatement =
  "Theta observations, theta profiles, danger shells, and theta<1 diagnostics are not promoted to Navier-Stokes regularity, BKM closure, or Clay."

record NSTailFluxAbsorptionMarginReceipt : Setω where
  field
    witnessK :
      Nat

    witnessKIsCanonical :
      witnessK ≡ zero

    tailCarryWitness :
      TailCarry_K witnessK

    tailCarryWitnessIsCanonical :
      tailCarryWitness ≡ tailCarry witnessK

    fluxWitness :
      Flux_K witnessK

    fluxWitnessIsCanonical :
      fluxWitness ≡ nonlinearFlux witnessK

    dissWitness :
      Diss_K witnessK

    dissWitnessIsCanonical :
      dissWitness ≡ viscousDissipation witnessK

    derivativeWitness :
      TailEnergyDerivative_K witnessK

    derivativeWitnessIsCanonical :
      derivativeWitness ≡ derivativeOfFixedCutoffTailEnergy witnessK

    fixedCutoffStatus :
      FixedCutoffDifferentiationStatus

    fixedCutoffStatusIsCanonical :
      fixedCutoffStatus ≡ shellCutoffKFixedDuringDifferentiation

    fixedKSemantics :
      List FixedKSemantics

    fixedKSemanticsIsCanonical :
      fixedKSemantics ≡ canonicalFixedKSemantics

    tailFluxIdentity :
      TailFluxIdentity_K witnessK

    tailFluxIdentityIsCanonical :
      tailFluxIdentity ≡ canonicalTailFluxIdentity witnessK

    fixedCutoffDuringDifferentiation :
      Bool

    fixedCutoffDuringDifferentiationIsTrue :
      fixedCutoffDuringDifferentiation ≡ true

    exactTailFluxDecompositionRecorded :
      Bool

    exactTailFluxDecompositionRecordedIsTrue :
      exactTailFluxDecompositionRecorded ≡ true

    dangerShellThetaArgmaxStatus :
      DangerShellThetaArgmaxStatus

    dangerShellThetaArgmaxSeparate :
      dangerShellThetaArgmaxStatus ≡
      dangerShellThetaArgmaxComputedAfterFixedKProfile

    thetaProfileComputabilityStatus :
      ThetaProfileComputabilityStatus

    thetaProfileComputabilityStatusIsCanonical :
      thetaProfileComputabilityStatus
      ≡
      thetaProfileComputableAfterFixedKFluxDissProfile

    thetaProfileComputable :
      Bool

    thetaProfileComputableIsTrue :
      thetaProfileComputable ≡ true

    movingCutoffTheoremStatus :
      MovingCutoffTheoremStatus

    movingCutoffTheoremStatusIsNoTheorem :
      movingCutoffTheoremStatus ≡ noMovingCutoffTheoremProvided

    movingCutoffTheoremProvedHere :
      Bool

    movingCutoffTheoremProvedHereIsFalse :
      movingCutoffTheoremProvedHere ≡ false

    theta :
      Theta

    thetaIsSymbolic :
      theta ≡ symbolicTheta

    theta<1 :
      ThetaLessThanOne theta

    margin :
      TailFluxAbsorptionMargin witnessK

    marginIsCanonical :
      margin ≡ canonicalTailFluxAbsorptionMargin witnessK

    theoremSurface :
      TailCarryDecreaseConclusion witnessK

    theoremSurfaceIsConditional :
      theoremSurface ≡ tailCarryDecreases margin

    tailDecayConclusion :
      TailDecayConclusion witnessK

    tailDecayConclusionIsConditional :
      tailDecayConclusion
      ≡
      thetaLessThanOneImpliesTailDecayConditionally margin

    thetaTailAbsorptionConditionalFlag :
      Bool

    thetaTailAbsorptionConditionalFlagIsTrue :
      thetaTailAbsorptionConditionalFlag ≡ true

    thetaContinuationConditionalFlag :
      Bool

    thetaContinuationConditionalFlagIsTrue :
      thetaContinuationConditionalFlag ≡ true

    thetaHighShellDecayOpenConditionalFlag :
      Bool

    thetaHighShellDecayOpenConditionalFlagIsTrue :
      thetaHighShellDecayOpenConditionalFlag ≡ true

    thetaMonotoneClaimed :
      Bool

    thetaMonotoneClaimedIsFalse :
      thetaMonotoneClaimed ≡ false

    thetaBKMEquivalenceProved :
      Bool

    thetaBKMEquivalenceProvedIsFalse :
      thetaBKMEquivalenceProved ≡ false

    thetaObservationPromotedToNSRegularity :
      Bool

    thetaObservationPromotedToNSRegularityIsFalse :
      thetaObservationPromotedToNSRegularity ≡ false

    invariantScope :
      List NSMarginInvariantScope

    invariantScopeIsCanonical :
      invariantScope ≡ canonicalNSMarginInvariantScope

    missingAnalyticInhabitants :
      List NSMarginAnalyticMissingInhabitant

    missingAnalyticInhabitantsAreCanonical :
      missingAnalyticInhabitants ≡ canonicalNSMarginAnalyticMissingInhabitants

    boundaries :
      List NSMarginBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalNSMarginBoundaries

    receiptIsConditional :
      Bool

    receiptIsConditionalIsTrue :
      receiptIsConditional ≡ true

    nonlinearFluxLeViscousDissipationProvedHere :
      Bool

    nonlinearFluxLeViscousDissipationProvedHereIsFalse :
      nonlinearFluxLeViscousDissipationProvedHere ≡ false

    thetaLessThanOneAnalyticEstimateProvedHere :
      Bool

    thetaLessThanOneAnalyticEstimateProvedHereIsFalse :
      thetaLessThanOneAnalyticEstimateProvedHere ≡ false

    nsRegularityPromoted :
      Bool

    nsRegularityPromotedIsFalse :
      nsRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsTailFluxAbsorptionMarginStatement

    fixedKSemanticsBoundary :
      String

    fixedKSemanticsBoundaryIsCanonical :
      fixedKSemanticsBoundary ≡ fixedKSemanticsStatement

    tailFluxIdentityBoundary :
      String

    tailFluxIdentityBoundaryIsCanonical :
      tailFluxIdentityBoundary ≡ tailFluxIdentityStatement

    thetaProfileComputabilityBoundary :
      String

    thetaProfileComputabilityBoundaryIsCanonical :
      thetaProfileComputabilityBoundary
      ≡
      thetaProfileComputabilityStatement

    thetaTailDecayBoundary :
      String

    thetaTailDecayBoundaryIsCanonical :
      thetaTailDecayBoundary ≡ thetaTailDecayStatement

    thetaDangerShellBoundary :
      String

    thetaDangerShellBoundaryIsCanonical :
      thetaDangerShellBoundary ≡ thetaDangerShellStatement

    thetaObservationNonPromotionBoundary :
      String

    thetaObservationNonPromotionBoundaryIsCanonical :
      thetaObservationNonPromotionBoundary
      ≡
      thetaObservationNonPromotionStatement

    promotionFlags :
      List NSTailFluxAbsorptionMarginPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSTailFluxAbsorptionMarginReceipt public

canonicalNSTailFluxAbsorptionMarginReceipt :
  NSTailFluxAbsorptionMarginReceipt
canonicalNSTailFluxAbsorptionMarginReceipt =
  record
    { witnessK =
        zero
    ; witnessKIsCanonical =
        refl
    ; tailCarryWitness =
        tailCarry zero
    ; tailCarryWitnessIsCanonical =
        refl
    ; fluxWitness =
        nonlinearFlux zero
    ; fluxWitnessIsCanonical =
        refl
    ; dissWitness =
        viscousDissipation zero
    ; dissWitnessIsCanonical =
        refl
    ; derivativeWitness =
        derivativeOfFixedCutoffTailEnergy zero
    ; derivativeWitnessIsCanonical =
        refl
    ; fixedCutoffStatus =
        shellCutoffKFixedDuringDifferentiation
    ; fixedCutoffStatusIsCanonical =
        refl
    ; fixedKSemantics =
        canonicalFixedKSemantics
    ; fixedKSemanticsIsCanonical =
        refl
    ; tailFluxIdentity =
        canonicalTailFluxIdentity zero
    ; tailFluxIdentityIsCanonical =
        refl
    ; fixedCutoffDuringDifferentiation =
        true
    ; fixedCutoffDuringDifferentiationIsTrue =
        refl
    ; exactTailFluxDecompositionRecorded =
        true
    ; exactTailFluxDecompositionRecordedIsTrue =
        refl
    ; dangerShellThetaArgmaxStatus =
        dangerShellThetaArgmaxComputedAfterFixedKProfile
    ; dangerShellThetaArgmaxSeparate =
        refl
    ; thetaProfileComputabilityStatus =
        thetaProfileComputableAfterFixedKFluxDissProfile
    ; thetaProfileComputabilityStatusIsCanonical =
        refl
    ; thetaProfileComputable =
        true
    ; thetaProfileComputableIsTrue =
        refl
    ; movingCutoffTheoremStatus =
        noMovingCutoffTheoremProvided
    ; movingCutoffTheoremStatusIsNoTheorem =
        refl
    ; movingCutoffTheoremProvedHere =
        false
    ; movingCutoffTheoremProvedHereIsFalse =
        refl
    ; theta =
        symbolicTheta
    ; thetaIsSymbolic =
        refl
    ; theta<1 =
        symbolicThetaLessThanOne
    ; margin =
        canonicalTailFluxAbsorptionMargin zero
    ; marginIsCanonical =
        refl
    ; theoremSurface =
        tailCarryDecreases (canonicalTailFluxAbsorptionMargin zero)
    ; theoremSurfaceIsConditional =
        refl
    ; tailDecayConclusion =
        thetaLessThanOneImpliesTailDecayConditionally
          (canonicalTailFluxAbsorptionMargin zero)
    ; tailDecayConclusionIsConditional =
        refl
    ; thetaTailAbsorptionConditionalFlag =
        true
    ; thetaTailAbsorptionConditionalFlagIsTrue =
        refl
    ; thetaContinuationConditionalFlag =
        true
    ; thetaContinuationConditionalFlagIsTrue =
        refl
    ; thetaHighShellDecayOpenConditionalFlag =
        true
    ; thetaHighShellDecayOpenConditionalFlagIsTrue =
        refl
    ; thetaMonotoneClaimed =
        false
    ; thetaMonotoneClaimedIsFalse =
        refl
    ; thetaBKMEquivalenceProved =
        false
    ; thetaBKMEquivalenceProvedIsFalse =
        refl
    ; thetaObservationPromotedToNSRegularity =
        false
    ; thetaObservationPromotedToNSRegularityIsFalse =
        refl
    ; invariantScope =
        canonicalNSMarginInvariantScope
    ; invariantScopeIsCanonical =
        refl
    ; missingAnalyticInhabitants =
        canonicalNSMarginAnalyticMissingInhabitants
    ; missingAnalyticInhabitantsAreCanonical =
        refl
    ; boundaries =
        canonicalNSMarginBoundaries
    ; boundariesAreCanonical =
        refl
    ; receiptIsConditional =
        true
    ; receiptIsConditionalIsTrue =
        refl
    ; nonlinearFluxLeViscousDissipationProvedHere =
        false
    ; nonlinearFluxLeViscousDissipationProvedHereIsFalse =
        refl
    ; thetaLessThanOneAnalyticEstimateProvedHere =
        false
    ; thetaLessThanOneAnalyticEstimateProvedHereIsFalse =
        refl
    ; nsRegularityPromoted =
        false
    ; nsRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; statement =
        nsTailFluxAbsorptionMarginStatement
    ; statementIsCanonical =
        refl
    ; fixedKSemanticsBoundary =
        fixedKSemanticsStatement
    ; fixedKSemanticsBoundaryIsCanonical =
        refl
    ; tailFluxIdentityBoundary =
        tailFluxIdentityStatement
    ; tailFluxIdentityBoundaryIsCanonical =
        refl
    ; thetaProfileComputabilityBoundary =
        thetaProfileComputabilityStatement
    ; thetaProfileComputabilityBoundaryIsCanonical =
        refl
    ; thetaTailDecayBoundary =
        thetaTailDecayStatement
    ; thetaTailDecayBoundaryIsCanonical =
        refl
    ; thetaDangerShellBoundary =
        thetaDangerShellStatement
    ; thetaDangerShellBoundaryIsCanonical =
        refl
    ; thetaObservationNonPromotionBoundary =
        thetaObservationNonPromotionStatement
    ; thetaObservationNonPromotionBoundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "conditional receipt only"
        ∷ "fixed shell cutoff K is held fixed during differentiation"
        ∷ "records exact fixed-K decomposition d/dt TailEnergy_K = -Diss_K + Flux_K"
        ∷ "danger shell and theta argmax are computed separately from the fixed-K profile"
        ∷ "no moving cutoff theorem is supplied"
        ∷ "NonlinearFlux<=ViscousDissipation/Theta<1 is the hard analytic missing inhabitant"
        ∷ "theta<1=>tail absorption is conditional, not a theorem promoted here"
        ∷ "theta<1=>continuation is conditional, not a theorem promoted here"
        ∷ "theta high-shell decay remains open/conditional"
        ∷ "theta<=>BKM is not proved"
        ∷ "tailCarryDecreases is conditional on TailFluxAbsorptionMargin"
        ∷ "no Navier-Stokes regularity or Clay promotion"
        ∷ []
    }

nsTailFluxAbsorptionMarginReceiptConditional :
  NSTailFluxAbsorptionMarginReceipt.receiptIsConditional
    canonicalNSTailFluxAbsorptionMarginReceipt
  ≡ true
nsTailFluxAbsorptionMarginReceiptConditional =
  refl

nsTailFluxAbsorptionMarginNoClayPromotion :
  NSTailFluxAbsorptionMarginReceipt.clayNavierStokesPromoted
    canonicalNSTailFluxAbsorptionMarginReceipt
  ≡ false
nsTailFluxAbsorptionMarginNoClayPromotion =
  refl

nsTailFluxAbsorptionMarginPromotionFlagsEmpty :
  NSTailFluxAbsorptionMarginReceipt.promotionFlags
    canonicalNSTailFluxAbsorptionMarginReceipt
  ≡ []
nsTailFluxAbsorptionMarginPromotionFlagsEmpty =
  refl
