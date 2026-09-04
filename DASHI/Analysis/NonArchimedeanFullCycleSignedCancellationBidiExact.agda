module DASHI.Analysis.NonArchimedeanFullCycleSignedCancellationBidiExact where

------------------------------------------------------------------------
-- FULL-CYCLE SIGN / PHASE BOUNDARY
--
-- Located source theorems establish:
--   * W1 * W2 = 2 for a supplied odd partition;
--   * normSq(W_C) = 2 for a supplied valid x3 orbit C;
--   * full-cycle odd fixed-point trace = the sum of monomial weights.
--
-- They do NOT, in the located Lean source, export the stronger phase claims
-- advertised in prose:
--
--   W1 = + i sqrt(2),  W2 = - i sqrt(2),
--   W1 + W2 = 0,
--   W1^2 = W2^2 = -2.
--
-- Magnitude/product data alone cannot manufacture those signs.  This owner
-- makes the phase producer explicit because it is exactly what first-return
-- trace cancellation and doubled-return -2I require.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data ReturnClaim : Set where
  orbitMagnitudeSquaredTwo : ReturnClaim
  pairedOrbitProductTwo : ReturnClaim
  firstReturnSignedCancellation : ReturnClaim
  eachOrbitSquareMinusTwo : ReturnClaim
  doubledReturnMonomialMinusTwoIdentity : ReturnClaim
  doubledReturnSpatialMinusTwoIdentity : ReturnClaim


data ReturnProducer : Set where
  canonicalOddOrbitPartition : ReturnProducer
  conditionalOrbitMagnitudeTheorem : ReturnProducer
  conditionalPairedProductTheorem : ReturnProducer
  explicitOrbitPhaseOrSignTheorem : ReturnProducer
  monomialPowerCompiler : ReturnProducer
  concreteDFTMonomialSameObjectWeld : ReturnProducer

returnCutset : ReturnClaim → List ReturnProducer
returnCutset orbitMagnitudeSquaredTwo =
  canonicalOddOrbitPartition ∷
  conditionalOrbitMagnitudeTheorem ∷
  []
returnCutset pairedOrbitProductTwo =
  canonicalOddOrbitPartition ∷
  conditionalPairedProductTheorem ∷
  []
returnCutset firstReturnSignedCancellation =
  canonicalOddOrbitPartition ∷
  explicitOrbitPhaseOrSignTheorem ∷
  []
returnCutset eachOrbitSquareMinusTwo =
  canonicalOddOrbitPartition ∷
  explicitOrbitPhaseOrSignTheorem ∷
  []
returnCutset doubledReturnMonomialMinusTwoIdentity =
  canonicalOddOrbitPartition ∷
  explicitOrbitPhaseOrSignTheorem ∷
  monomialPowerCompiler ∷
  []
returnCutset doubledReturnSpatialMinusTwoIdentity =
  canonicalOddOrbitPartition ∷
  explicitOrbitPhaseOrSignTheorem ∷
  monomialPowerCompiler ∷
  concreteDFTMonomialSameObjectWeld ∷
  []

record LocatedReturnStrength : Set where
  constructor locatedReturnStrength
  field
    pairedProductTwoLocated : Bool
    conditionalOrbitNormSquaredTwoLocated : Bool
    canonicalOrbitPackageLocated : Bool
    explicitPlusIMinusISqrtTwoLocated : Bool
    explicitFirstReturnCancellationLocated : Bool
    explicitOrbitSquareMinusTwoLocated : Bool
    genericMonomialPowerCompilerLocated : Bool
    concreteSpatialMinusTwoIdentityDerived : Bool

canonicalLocatedReturnStrength : LocatedReturnStrength
canonicalLocatedReturnStrength =
  locatedReturnStrength
    true true false false false false true false

record PhaseFirewall : Set where
  constructor phaseFirewall
  field
    magnitudeDeterminesPhase : Bool
    productTwoDeterminesIndividualSigns : Bool
    conjugateMagnitudeDeterminesPureImaginary : Bool
    normBeforeSignedPairingPreservesCancellationAutomatically : Bool

canonicalPhaseFirewall : PhaseFirewall
canonicalPhaseFirewall =
  phaseFirewall false false false false

phaseStillLive :
  LocatedReturnStrength.explicitOrbitSquareMinusTwoLocated
    canonicalLocatedReturnStrength
  ≡ false
phaseStillLive = refl

spatialMinusTwoStillDownstream :
  LocatedReturnStrength.concreteSpatialMinusTwoIdentityDerived
    canonicalLocatedReturnStrength
  ≡ false
spatialMinusTwoStillDownstream = refl
