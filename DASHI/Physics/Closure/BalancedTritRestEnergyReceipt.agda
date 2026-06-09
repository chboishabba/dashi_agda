module DASHI.Physics.Closure.BalancedTritRestEnergyReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty as Empty using (⊥)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; _∷_; [])
open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)

import DASHI.Physics.Closure.KnownLimitsCompleteLocalRegimeTheorem as KLCLR
import DASHI.Physics.Closure.KnownLimitsLocalCausalEffectivePropagationTheorem as KLCEPT
import DASHI.Physics.Closure.KnownLimitsLocalCausalGeometryCoherenceTheorem as KLCGCT
import DASHI.Physics.Closure.MinkowskiLimitReceipt as ML
import DASHI.Physics.Closure.TSFVCandidate256CalibrationLawDiagnostic as TSFV
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as W4External
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
import Ontology.DNA.ChemistryQuotient as CDQ
import Ontology.GodelLattice as GL
import Ontology.Hecke.FactorVecInstances as FVI

------------------------------------------------------------------------
-- Flat-sector rest-energy receipt from the balanced-trit carrier.
--
-- This module packages the internal DASHI receipt bundle:
--
--   balanced trit T-involution
--   -> v3/depth invariance
--   -> CDQ strength weight and 3^weight address magnitude
--   -> flat SFGC d^2 = 0 and vacuum flatness
--   -> known-limits causal propagation/coherence
--   -> symbolic quadratic seed / rest-energy readoff.
--
-- It does not construct W4 physical-unit calibration, non-flat Yang-Mills,
-- sourced GR, Standard Model closure, Clay authority, or terminal promotion.

squareNat :
  Nat →
  Nat
squareNat n =
  n * n

massTimesCSquared :
  Nat →
  Nat →
  Nat
massTimesCSquared mass c =
  mass * squareNat c

record BalancedTritDialecticalCarrierStage : Setω where
  field
    quotientT :
      CDQ.ChemistryFeature →
      CDQ.ChemistryFeature

    quotientTIsCandidate256QuotientT :
      quotientT ≡ TSFV.candidate256QuotientT

    quotientTInvolutive :
      (q : CDQ.ChemistryFeature) →
      quotientT (quotientT q) ≡ q

    integerAddress :
      CDQ.ChemistryFeature →
      TSFV.TSFVIntegerAddress

    integerAddressIsCandidate256IntegerAddress :
      integerAddress ≡ TSFV.candidate256IntegerAddress

    addressNegationCompatibility :
      (q : CDQ.ChemistryFeature) →
      integerAddress (quotientT q)
      ≡
      TSFV.addressNegation (integerAddress q)

    tritDepthMap :
      CDQ.ChemistryFeature →
      TSFV.TSFVDiagnosticPhysicalUnitCarrier

    tritDepthMapIsCandidate256Map :
      tritDepthMap ≡ TSFV.candidate256TritQuotientCalibrationMap

    depthInvariantUnderT :
      (q : CDQ.ChemistryFeature) →
      tritDepthMap (quotientT q) ≡ tritDepthMap q

    stageBoundary :
      List String

open BalancedTritDialecticalCarrierStage public

canonicalBalancedTritDialecticalCarrierStage :
  BalancedTritDialecticalCarrierStage
canonicalBalancedTritDialecticalCarrierStage =
  record
    { quotientT =
        TSFV.candidate256QuotientT
    ; quotientTIsCandidate256QuotientT =
        refl
    ; quotientTInvolutive =
        TSFV.candidate256QuotientTInvolutive
    ; integerAddress =
        TSFV.candidate256IntegerAddress
    ; integerAddressIsCandidate256IntegerAddress =
        refl
    ; addressNegationCompatibility =
        TSFV.candidate256AddressNegationCompatibility
    ; tritDepthMap =
        TSFV.candidate256TritQuotientCalibrationMap
    ; tritDepthMapIsCandidate256Map =
        refl
    ; depthInvariantUnderT =
        TSFV.candidate256TritDimensionalInvarianceUnderT
    ; stageBoundary =
        "T is candidate256QuotientT"
        ∷ "T is involutive"
        ∷ "candidate256IntegerAddress transports T to addressNegation"
        ∷ "candidate256TritQuotientCalibrationMap is invariant under T"
        ∷ []
    }

record CDQStrengthWeightNormStage : Setω where
  field
    carrierStage :
      BalancedTritDialecticalCarrierStage

    strengthWeight :
      CDQ.FeatureU →
      Nat

    strengthWeightIsCountStrongButLast :
      strengthWeight ≡ TSFV.countStrongButLast

    pow3 :
      Nat →
      Nat

    pow3IsTSFVPow3 :
      pow3 ≡ TSFV.pow3

    integerAddressUsesPow3Weight :
      (strengths : CDQ.FeatureU) →
      (purines : CDQ.FeatureV) →
      BalancedTritDialecticalCarrierStage.integerAddress carrierStage
        (CDQ.chemistryFeature strengths purines)
      ≡
      TSFV.tsfvIntegerAddress
        (pow3 (strengthWeight strengths))
        (TSFV.lastStrengthSign strengths)

    normMagnitude :
      CDQ.FeatureU →
      Nat

    normMagnitudeIsPow3Weight :
      (strengths : CDQ.FeatureU) →
      normMagnitude strengths ≡ pow3 (strengthWeight strengths)

    stageBoundary :
      List String

open CDQStrengthWeightNormStage public

canonicalCDQStrengthWeightNormStage :
  CDQStrengthWeightNormStage
canonicalCDQStrengthWeightNormStage =
  record
    { carrierStage =
        canonicalBalancedTritDialecticalCarrierStage
    ; strengthWeight =
        TSFV.countStrongButLast
    ; strengthWeightIsCountStrongButLast =
        refl
    ; pow3 =
        TSFV.pow3
    ; pow3IsTSFVPow3 =
        refl
    ; integerAddressUsesPow3Weight =
        λ _ _ →
          refl
    ; normMagnitude =
        λ strengths →
          TSFV.pow3 (TSFV.countStrongButLast strengths)
    ; normMagnitudeIsPow3Weight =
        λ _ →
          refl
    ; stageBoundary =
        "CDQ strength weight is countStrongButLast"
        ∷ "candidate256IntegerAddress is 3^weight paired with lastStrengthSign"
        ∷ "The bounded norm magnitude recorded here is pow3 weight"
        ∷ []
    }

record FlatClosureQuadraticDispersionSeedStage : Setω where
  field
    strengthNormStage :
      CDQStrengthWeightNormStage

    exteriorBoundaryOfBoundaryZero :
      (f : SFGC.SFGCSite2DDiscrete0Form) →
      (base : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEvaluate2
        (SFGC.sfgcSite2Dδ₁ (SFGC.sfgcSite2Dδ₀ f))
        (SFGC.sfgcSite2DPlaquetteAt base)
      ≡
      SPTI4.φ0

    vacuumWilsonLoopFlatness :
      (base : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEvaluate2
        (SFGC.sfgcSite2Dδ₁
          (SFGC.sfgcSite2DConnectionTo1Form SFGC.vacuumGaugeField))
        (SFGC.sfgcSite2DPlaquetteAt base)
      ≡
      SPTI4.φ0

    localCausalEffectivePropagation :
      KLCEPT.KnownLimitsLocalCausalEffectivePropagationTheorem

    localCausalGeometryCoherence :
      KLCGCT.KnownLimitsLocalCausalGeometryCoherenceTheorem

    completeLocalRegime :
      KLCLR.KnownLimitsCompleteLocalRegimeTheorem

    minkowskiLimit :
      ML.CarrierQuadraticIsMinkowski

    minkowskiQuadratic :
      ML.MinkowskiCarrier →
      ℤ

    minkowskiQuadraticIsCanonical :
      minkowskiQuadratic ≡ ML.minkowskiQuadratic

    quadraticDispersionSeedAvailable :
      Bool

    quadraticDispersionSeedAvailableIsTrue :
      quadraticDispersionSeedAvailable ≡ true

    stageBoundary :
      List String

open FlatClosureQuadraticDispersionSeedStage public

canonicalFlatClosureQuadraticDispersionSeedStage :
  FlatClosureQuadraticDispersionSeedStage
canonicalFlatClosureQuadraticDispersionSeedStage =
  record
    { strengthNormStage =
        canonicalCDQStrengthWeightNormStage
    ; exteriorBoundaryOfBoundaryZero =
        SFGC.sfgcSite2DP2P3BoundaryOfBoundaryZero
    ; vacuumWilsonLoopFlatness =
        SFGC.sfgcSite2DVacuumWilsonLoopFlatness
    ; localCausalEffectivePropagation =
        KLCEPT.canonicalKnownLimitsLocalCausalEffectivePropagationTheorem
    ; localCausalGeometryCoherence =
        KLCGCT.canonicalKnownLimitsLocalCausalGeometryCoherenceTheorem
    ; completeLocalRegime =
        KLCLR.canonicalKnownLimitsCompleteLocalRegimeTheorem
    ; minkowskiLimit =
        ML.minkowskiLimitReceipt
    ; minkowskiQuadratic =
        ML.minkowskiQuadratic
    ; minkowskiQuadraticIsCanonical =
        refl
    ; quadraticDispersionSeedAvailable =
        true
    ; quadraticDispersionSeedAvailableIsTrue =
        refl
    ; stageBoundary =
        "SFGC p2/p3 plaquette has selected exterior d^2 = 0"
        ∷ "vacuumGaugeField has flat Wilson-loop curvature on the selected plaquette"
        ∷ "Known-limits causal propagation and geometry coherence are imported"
        ∷ "MinkowskiLimitReceipt supplies the flat Lorentzian quadratic"
        ∷ "This is a flat-sector quadratic seed, not non-flat Yang-Mills or sourced GR"
        ∷ []
    }

factorVecLaneWeight :
  SSP →
  GL.FactorVec →
  Nat
factorVecLaneWeight p2 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e2
factorVecLaneWeight p3 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e3
factorVecLaneWeight p5 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e5
factorVecLaneWeight p7 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e7
factorVecLaneWeight p11 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e11
factorVecLaneWeight p13 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e13
factorVecLaneWeight p17 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e17
factorVecLaneWeight p19 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e19
factorVecLaneWeight p23 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e23
factorVecLaneWeight p29 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e29
factorVecLaneWeight p31 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e31
factorVecLaneWeight p41 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e41
factorVecLaneWeight p47 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e47
factorVecLaneWeight p59 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e59
factorVecLaneWeight p71 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e71

factorVecLaneWeightAfterPrimeBump :
  (lane : SSP) →
  (base : GL.FactorVec) →
  factorVecLaneWeight lane (FVI.primeBump lane base)
  ≡
  suc (factorVecLaneWeight lane base)
factorVecLaneWeightAfterPrimeBump p2 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p3 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p5 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p7 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p11 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p13 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p17 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p19 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p23 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p29 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p31 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p41 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p47 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p59 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl
factorVecLaneWeightAfterPrimeBump p71 (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl

factorVecPrimeBumpWeightedMomentumSquared :
  GL.FactorVec →
  GL.FactorVec →
  Nat
factorVecPrimeBumpWeightedMomentumSquared base weights =
  squareNat (factorVecLaneWeight p2 (FVI.primeBump p2 base)) * factorVecLaneWeight p2 weights
  + squareNat (factorVecLaneWeight p3 (FVI.primeBump p3 base)) * factorVecLaneWeight p3 weights
  + squareNat (factorVecLaneWeight p5 (FVI.primeBump p5 base)) * factorVecLaneWeight p5 weights
  + squareNat (factorVecLaneWeight p7 (FVI.primeBump p7 base)) * factorVecLaneWeight p7 weights
  + squareNat (factorVecLaneWeight p11 (FVI.primeBump p11 base)) * factorVecLaneWeight p11 weights
  + squareNat (factorVecLaneWeight p13 (FVI.primeBump p13 base)) * factorVecLaneWeight p13 weights
  + squareNat (factorVecLaneWeight p17 (FVI.primeBump p17 base)) * factorVecLaneWeight p17 weights
  + squareNat (factorVecLaneWeight p19 (FVI.primeBump p19 base)) * factorVecLaneWeight p19 weights
  + squareNat (factorVecLaneWeight p23 (FVI.primeBump p23 base)) * factorVecLaneWeight p23 weights
  + squareNat (factorVecLaneWeight p29 (FVI.primeBump p29 base)) * factorVecLaneWeight p29 weights
  + squareNat (factorVecLaneWeight p31 (FVI.primeBump p31 base)) * factorVecLaneWeight p31 weights
  + squareNat (factorVecLaneWeight p41 (FVI.primeBump p41 base)) * factorVecLaneWeight p41 weights
  + squareNat (factorVecLaneWeight p47 (FVI.primeBump p47 base)) * factorVecLaneWeight p47 weights
  + squareNat (factorVecLaneWeight p59 (FVI.primeBump p59 base)) * factorVecLaneWeight p59 weights
  + squareNat (factorVecLaneWeight p71 (FVI.primeBump p71 base)) * factorVecLaneWeight p71 weights

record FactorVecPrimeBumpMomentumMagnitudeTheorem
  (base : GL.FactorVec)
  (weights : GL.FactorVec) :
  Set where
  field
    momentumMagnitudeSquared :
      Nat

    momentumMagnitudeSquaredIsWeightedPrimeBumpSum :
      momentumMagnitudeSquared
      ≡
      factorVecPrimeBumpWeightedMomentumSquared base weights

    p2PrimeBumpSuccessor :
      factorVecLaneWeight p2 (FVI.primeBump p2 base)
      ≡
      suc (factorVecLaneWeight p2 base)

    p3PrimeBumpSuccessor :
      factorVecLaneWeight p3 (FVI.primeBump p3 base)
      ≡
      suc (factorVecLaneWeight p3 base)

    p5PrimeBumpSuccessor :
      factorVecLaneWeight p5 (FVI.primeBump p5 base)
      ≡
      suc (factorVecLaneWeight p5 base)

    p7PrimeBumpSuccessor :
      factorVecLaneWeight p7 (FVI.primeBump p7 base)
      ≡
      suc (factorVecLaneWeight p7 base)

    allLanePrimeBumpSuccessorsRecorded :
      Bool

    allLanePrimeBumpSuccessorsRecordedIsTrue :
      allLanePrimeBumpSuccessorsRecorded ≡ true

    theoremBoundary :
      List String

open FactorVecPrimeBumpMomentumMagnitudeTheorem public

factorVecPrimeBumpMomentumMagnitudeTheorem :
  (base : GL.FactorVec) →
  (weights : GL.FactorVec) →
  FactorVecPrimeBumpMomentumMagnitudeTheorem base weights
factorVecPrimeBumpMomentumMagnitudeTheorem base weights =
  record
    { momentumMagnitudeSquared =
        factorVecPrimeBumpWeightedMomentumSquared base weights
    ; momentumMagnitudeSquaredIsWeightedPrimeBumpSum =
        refl
    ; p2PrimeBumpSuccessor =
        factorVecLaneWeightAfterPrimeBump p2 base
    ; p3PrimeBumpSuccessor =
        factorVecLaneWeightAfterPrimeBump p3 base
    ; p5PrimeBumpSuccessor =
        factorVecLaneWeightAfterPrimeBump p5 base
    ; p7PrimeBumpSuccessor =
        factorVecLaneWeightAfterPrimeBump p7 base
    ; allLanePrimeBumpSuccessorsRecorded =
        true
    ; allLanePrimeBumpSuccessorsRecordedIsTrue =
        refl
    ; theoremBoundary =
        "Typed formal momentum magnitude theorem: |p|^2 is the 15-lane sum of primeBump_i^2 times w_i"
        ∷ "Each primeBump_i successor law is supplied by factorVecLaneWeightAfterPrimeBump"
        ∷ "This remains a Nat-valued symbolic carrier formula and does not choose physical units"
        ∷ []
    }

symbolicMomentumMagnitude :
  Nat →
  Nat →
  Nat
symbolicMomentumMagnitude pow3Weight primeBumpWeight =
  pow3Weight * primeBumpWeight

symbolicMomentumMagnitudeSquared :
  Nat →
  Nat →
  Nat
symbolicMomentumMagnitudeSquared pow3Weight primeBumpWeight =
  squareNat (symbolicMomentumMagnitude pow3Weight primeBumpWeight)

record Candidate256Pow3PrimeBumpMomentumBridge
  (strengths : CDQ.FeatureU)
  (purines : CDQ.FeatureV)
  (base : GL.FactorVec)
  (lane : SSP) :
  Set where
  field
    address :
      TSFV.TSFVIntegerAddress

    addressIsCandidate256IntegerAddress :
      address
      ≡
      TSFV.candidate256IntegerAddress (CDQ.chemistryFeature strengths purines)

    pow3Weight :
      Nat

    pow3WeightIsCandidate256AddressMagnitude :
      pow3Weight
      ≡
      TSFV.addressAbs
        (TSFV.candidate256IntegerAddress (CDQ.chemistryFeature strengths purines))

    pow3WeightIsStrengthWeight :
      pow3Weight
      ≡
      TSFV.pow3 (TSFV.countStrongButLast strengths)

    primeBumpWeight :
      Nat

    primeBumpWeightIsLaneWeightAfterPrimeBump :
      primeBumpWeight
      ≡
      factorVecLaneWeight lane (FVI.primeBump lane base)

    primeBumpWeightSuccessorLaw :
      primeBumpWeight
      ≡
      suc (factorVecLaneWeight lane base)

    momentumMagnitudeSquared :
      Nat

    momentumMagnitudeSquaredIsPow3PrimeBumpSquared :
      momentumMagnitudeSquared
      ≡
      symbolicMomentumMagnitudeSquared pow3Weight primeBumpWeight

    momentumMagnitudeSquaredName :
      String

    nonPromotingDimensionlessBridge :
      Bool

    nonPromotingDimensionlessBridgeIsTrue :
      nonPromotingDimensionlessBridge ≡ true

    bridgeBoundary :
      List String

open Candidate256Pow3PrimeBumpMomentumBridge public

candidate256Pow3PrimeBumpMomentumBridge :
  (strengths : CDQ.FeatureU) →
  (purines : CDQ.FeatureV) →
  (base : GL.FactorVec) →
  (lane : SSP) →
  Candidate256Pow3PrimeBumpMomentumBridge strengths purines base lane
candidate256Pow3PrimeBumpMomentumBridge strengths purines base lane =
  record
    { address =
        TSFV.candidate256IntegerAddress
          (CDQ.chemistryFeature strengths purines)
    ; addressIsCandidate256IntegerAddress =
        refl
    ; pow3Weight =
        TSFV.pow3 (TSFV.countStrongButLast strengths)
    ; pow3WeightIsCandidate256AddressMagnitude =
        refl
    ; pow3WeightIsStrengthWeight =
        refl
    ; primeBumpWeight =
        factorVecLaneWeight lane (FVI.primeBump lane base)
    ; primeBumpWeightIsLaneWeightAfterPrimeBump =
        refl
    ; primeBumpWeightSuccessorLaw =
        factorVecLaneWeightAfterPrimeBump lane base
    ; momentumMagnitudeSquared =
        symbolicMomentumMagnitudeSquared
          (TSFV.pow3 (TSFV.countStrongButLast strengths))
          (factorVecLaneWeight lane (FVI.primeBump lane base))
    ; momentumMagnitudeSquaredIsPow3PrimeBumpSquared =
        refl
    ; momentumMagnitudeSquaredName =
        "|p|^2"
    ; nonPromotingDimensionlessBridge =
        true
    ; nonPromotingDimensionlessBridgeIsTrue =
        refl
    ; bridgeBoundary =
        "candidate256IntegerAddress supplies the signed pow3 address magnitude"
        ∷ "pow3(countStrongButLast strengths) remains a dimensionless symbolic weight"
        ∷ "FVI.primeBump supplies the selected prime-lane successor weight"
        ∷ "|p|^2 is recorded as the square of pow3 weight times prime-bump weight"
        ∷ "No physical unit carrier, calibration map, or dimensional preservation law is constructed"
        ∷ []
    }

dispersionEnergySquared :
  Nat →
  Nat →
  Nat →
  Nat
dispersionEnergySquared c momentumSquared restEnergy =
  squareNat c * momentumSquared + squareNat restEnergy

record SymbolicDispersionBridge
  (momentumSquared : Nat)
  (c : Nat)
  (restEnergy : Nat) :
  Set where
  field
    energySquared :
      Nat

    energySquaredIsRelativisticDispersion :
      energySquared
      ≡
      dispersionEnergySquared c momentumSquared restEnergy

    dispersionEquationName :
      String

    dispersionBoundary :
      List String

open SymbolicDispersionBridge public

symbolicDispersionBridge :
  (momentumSquared : Nat) →
  (c : Nat) →
  (restEnergy : Nat) →
  SymbolicDispersionBridge momentumSquared c restEnergy
symbolicDispersionBridge momentumSquared c restEnergy =
  record
    { energySquared =
        dispersionEnergySquared c momentumSquared restEnergy
    ; energySquaredIsRelativisticDispersion =
        refl
    ; dispersionEquationName =
        "E^2 = c^2 |p|^2 + E0^2"
    ; dispersionBoundary =
        "This is a symbolic Nat-valued dispersion target"
        ∷ "It consumes |p|^2 from the non-promoting Candidate256/pow3/primeBump bridge"
        ∷ "It does not assert real-valued positivity, square-root existence, or physical-unit calibration"
        ∷ []
    }

data SqrtTaylorTargetStatus : Set where
  targetSurfaceOnlyAwaitingRealAnalysisAndCalibration :
    SqrtTaylorTargetStatus

record SqrtTaylorKineticTargetSurface
  (mass : Nat)
  (c : Nat)
  (restEnergy : Nat)
  (momentumSquared : Nat) :
  Set where
  field
    status :
      SqrtTaylorTargetStatus

    dispersionBridge :
      SymbolicDispersionBridge momentumSquared c restEnergy

    restEnergyTarget :
      Nat

    restEnergyTargetIsMC2 :
      restEnergyTarget ≡ massTimesCSquared mass c

    kineticMatchingTarget :
      String

    sqrtTaylorTarget :
      String

    sqrtTaylorRemainderTarget :
      String

    firstRemainingBlocker :
      String

    noPhysicalUnitPromotion :
      Bool

    noPhysicalUnitPromotionIsTrue :
      noPhysicalUnitPromotion ≡ true

    targetBoundary :
      List String

open SqrtTaylorKineticTargetSurface public

sqrtTaylorKineticTargetSurface :
  (mass : Nat) →
  (c : Nat) →
  (momentumSquared : Nat) →
  SqrtTaylorKineticTargetSurface
    mass
    c
    (massTimesCSquared mass c)
    momentumSquared
sqrtTaylorKineticTargetSurface mass c momentumSquared =
  record
    { status =
        targetSurfaceOnlyAwaitingRealAnalysisAndCalibration
    ; dispersionBridge =
        symbolicDispersionBridge
          momentumSquared
          c
          (massTimesCSquared mass c)
    ; restEnergyTarget =
        massTimesCSquared mass c
    ; restEnergyTargetIsMC2 =
        refl
    ; kineticMatchingTarget =
        "c^2 / (2 E0) = 1 / (2 m) => E0 = m c^2"
    ; sqrtTaylorTarget =
        "sqrt(E0^2 + c^2 |p|^2) = E0 + |p|^2 / (2 m) + higher-order remainder"
    ; sqrtTaylorRemainderTarget =
        "O(|p|^4 / E0^3)"
    ; firstRemainingBlocker =
        "Candidate256PhysicalCalibrationExternalReceipt"
    ; noPhysicalUnitPromotion =
        true
    ; noPhysicalUnitPromotionIsTrue =
        refl
    ; targetBoundary =
        "The kinetic matching target records the algebraic rest-energy target E0 = m c^2"
        ∷ "The sqrt/Taylor expansion remains a target surface, not an analytic theorem"
        ∷ "The explicit remainder target is O(|p|^4 / E0^3)"
        ∷ "The first remaining blocker is Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "No physical units are promoted from the Nat surrogate in this surface"
        ∷ []
    }

record FormalE0EqualsMC2DispersionTheoremSurface
  (mass : Nat)
  (c : Nat)
  (momentumSquared : Nat) :
  Set where
  field
    restEnergy :
      Nat

    restEnergyIsMassTimesCSquared :
      restEnergy ≡ massTimesCSquared mass c

    dispersionBridge :
      SymbolicDispersionBridge momentumSquared c restEnergy

    formalDispersionEnergySquared :
      Nat

    formalDispersionEnergySquaredIsCanonical :
      formalDispersionEnergySquared
      ≡
      dispersionEnergySquared
        c
        momentumSquared
        restEnergy

    e0EqualsMC2TheoremSurfaceRecorded :
      Bool

    e0EqualsMC2TheoremSurfaceRecordedIsTrue :
      e0EqualsMC2TheoremSurfaceRecorded ≡ true

    sqrtTaylorTheoremPromoted :
      Bool

    sqrtTaylorTheoremPromotedIsFalse :
      sqrtTaylorTheoremPromoted ≡ false

    physicalUnitCalibrationPromoted :
      Bool

    physicalUnitCalibrationPromotedIsFalse :
      physicalUnitCalibrationPromoted ≡ false

    theoremBoundary :
      List String

open FormalE0EqualsMC2DispersionTheoremSurface public

formalE0EqualsMC2DispersionTheoremSurface :
  (mass : Nat) →
  (c : Nat) →
  (momentumSquared : Nat) →
  FormalE0EqualsMC2DispersionTheoremSurface mass c momentumSquared
formalE0EqualsMC2DispersionTheoremSurface mass c momentumSquared =
  record
    { restEnergy =
        massTimesCSquared mass c
    ; restEnergyIsMassTimesCSquared =
        refl
    ; dispersionBridge =
        symbolicDispersionBridge
          momentumSquared
          c
          (massTimesCSquared mass c)
    ; formalDispersionEnergySquared =
        dispersionEnergySquared
          c
          momentumSquared
          (massTimesCSquared mass c)
    ; formalDispersionEnergySquaredIsCanonical =
        refl
    ; e0EqualsMC2TheoremSurfaceRecorded =
        true
    ; e0EqualsMC2TheoremSurfaceRecordedIsTrue =
        refl
    ; sqrtTaylorTheoremPromoted =
        false
    ; sqrtTaylorTheoremPromotedIsFalse =
        refl
    ; physicalUnitCalibrationPromoted =
        false
    ; physicalUnitCalibrationPromotedIsFalse =
        refl
    ; theoremBoundary =
        "Formal theorem surface: E0 is definitionally mass * c^2 on the Nat carrier"
        ∷ "The associated dispersion bridge records E^2 = c^2 |p|^2 + E0^2"
        ∷ "The square-root/Taylor expansion remains a target surface rather than an analytic theorem"
        ∷ "No physical-unit calibration or cStar authority is constructed"
        ∷ []
    }

record FormalTaylorKineticMatchingReceipt
  (mass : Nat)
  (c : Nat)
  (momentumSquared : Nat) :
  Set where
  field
    dispersionSurface :
      FormalE0EqualsMC2DispersionTheoremSurface mass c momentumSquared

    sqrtTaylorTargetSurface :
      SqrtTaylorKineticTargetSurface
        mass
        c
        (massTimesCSquared mass c)
        momentumSquared

    restEnergy :
      Nat

    restEnergyIsMC2 :
      restEnergy ≡ massTimesCSquared mass c

    firstTaylorCorrectionNumerator :
      Nat

    firstTaylorCorrectionNumeratorIsC2P2 :
      firstTaylorCorrectionNumerator
      ≡
      squareNat c * momentumSquared

    firstTaylorCorrectionDenominator :
      Nat

    firstTaylorCorrectionDenominatorIs2E0 :
      firstTaylorCorrectionDenominator
      ≡
      2 * restEnergy

    kineticTermNumerator :
      Nat

    kineticTermNumeratorIsP2 :
      kineticTermNumerator
      ≡
      momentumSquared

    kineticTermDenominator :
      Nat

    kineticTermDenominatorIs2M :
      kineticTermDenominator
      ≡
      2 * mass

    kineticMatchingConditionName :
      String

    matchingRequiresE0EqualsMC2 :
      Bool

    matchingRequiresE0EqualsMC2IsTrue :
      matchingRequiresE0EqualsMC2 ≡ true

    analyticTaylorTheoremPromoted :
      Bool

    analyticTaylorTheoremPromotedIsFalse :
      analyticTaylorTheoremPromoted ≡ false

    physicalUnitCalibrationPromoted :
      Bool

    physicalUnitCalibrationPromotedIsFalse :
      physicalUnitCalibrationPromoted ≡ false

    receiptBoundary :
      List String

open FormalTaylorKineticMatchingReceipt public

formalTaylorKineticMatchingReceipt :
  (mass : Nat) →
  (c : Nat) →
  (momentumSquared : Nat) →
  FormalTaylorKineticMatchingReceipt mass c momentumSquared
formalTaylorKineticMatchingReceipt mass c momentumSquared =
  record
    { dispersionSurface =
        formalE0EqualsMC2DispersionTheoremSurface mass c momentumSquared
    ; sqrtTaylorTargetSurface =
        sqrtTaylorKineticTargetSurface mass c momentumSquared
    ; restEnergy =
        massTimesCSquared mass c
    ; restEnergyIsMC2 =
        refl
    ; firstTaylorCorrectionNumerator =
        squareNat c * momentumSquared
    ; firstTaylorCorrectionNumeratorIsC2P2 =
        refl
    ; firstTaylorCorrectionDenominator =
        2 * massTimesCSquared mass c
    ; firstTaylorCorrectionDenominatorIs2E0 =
        refl
    ; kineticTermNumerator =
        momentumSquared
    ; kineticTermNumeratorIsP2 =
        refl
    ; kineticTermDenominator =
        2 * mass
    ; kineticTermDenominatorIs2M =
        refl
    ; kineticMatchingConditionName =
        "first Taylor correction c^2 |p|^2 / (2 E0) matches |p|^2 / (2 m) when E0 = m c^2"
    ; matchingRequiresE0EqualsMC2 =
        true
    ; matchingRequiresE0EqualsMC2IsTrue =
        refl
    ; analyticTaylorTheoremPromoted =
        false
    ; analyticTaylorTheoremPromotedIsFalse =
        refl
    ; physicalUnitCalibrationPromoted =
        false
    ; physicalUnitCalibrationPromotedIsFalse =
        refl
    ; receiptBoundary =
        "The first symbolic Taylor correction is recorded as c^2 |p|^2 over 2 E0"
        ∷ "The kinetic target is recorded as |p|^2 over 2 m"
        ∷ "The matching condition is the definitional Nat rest-energy surface E0 = m c^2"
        ∷ "This is not a real-analysis square-root/Taylor theorem"
        ∷ "Physical-unit calibration remains gated by Candidate256PhysicalCalibrationExternalReceipt"
        ∷ []
    }

record Candidate256NaturalUnitsCalibrationReceipt : Setω where
  field
    naturalSpeedOfLight :
      Nat

    naturalSpeedOfLightIsOne :
      naturalSpeedOfLight ≡ 1

    massUnit :
      String

    energyUnit :
      String

    massUnitIsCandidate256Norm :
      massUnit ≡ "candidate256NormUnit"

    energyUnitIsCandidate256Norm :
      energyUnit ≡ "candidate256NormUnit"

    naturalUnitsPromoted :
      Bool

    naturalUnitsPromotedIsTrue :
      naturalUnitsPromoted ≡ true

    siUnitsPromoted :
      Bool

    siUnitsPromotedIsFalse :
      siUnitsPromoted ≡ false

    candidate256PhysicalCalibrationStillExternal :
      W4External.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

    receiptBoundary :
      List String

open Candidate256NaturalUnitsCalibrationReceipt public

candidate256NaturalUnitsCalibrationReceipt :
  Candidate256NaturalUnitsCalibrationReceipt
candidate256NaturalUnitsCalibrationReceipt =
  record
    { naturalSpeedOfLight =
        1
    ; naturalSpeedOfLightIsOne =
        refl
    ; massUnit =
        "candidate256NormUnit"
    ; energyUnit =
        "candidate256NormUnit"
    ; massUnitIsCandidate256Norm =
        refl
    ; energyUnitIsCandidate256Norm =
        refl
    ; naturalUnitsPromoted =
        true
    ; naturalUnitsPromotedIsTrue =
        refl
    ; siUnitsPromoted =
        false
    ; siUnitsPromotedIsFalse =
        refl
    ; candidate256PhysicalCalibrationStillExternal =
        W4External.candidate256PhysicalCalibrationExternalReceiptImpossibleWithoutExternalAuthority
    ; receiptBoundary =
        "Option A natural-units receipt: c is definitionally 1"
        ∷ "massUnit and energyUnit are both candidate256NormUnit"
        ∷ "This promotes only a definitional natural-unit convention"
        ∷ "SI/GeV promotion remains gated on Candidate256PhysicalCalibrationExternalReceipt"
        ∷ []
    }

record SymbolicRestEnergyReadoff
  (mass : Nat)
  (c : Nat) :
  Set where
  field
    restEnergy :
      Nat

    restEnergyEqualsMassTimesCSquared :
      restEnergy ≡ massTimesCSquared mass c

    nonRelativisticKineticMatchingNarrativeRecorded :
      Bool

    nonRelativisticKineticMatchingNarrativeRecordedIsTrue :
      nonRelativisticKineticMatchingNarrativeRecorded ≡ true

    ultraRelativisticMasslessLimitNarrativeRecorded :
      Bool

    ultraRelativisticMasslessLimitNarrativeRecordedIsTrue :
      ultraRelativisticMasslessLimitNarrativeRecorded ≡ true

    readoffBoundary :
      List String

open SymbolicRestEnergyReadoff public

symbolicRestEnergyReadoff :
  (mass : Nat) →
  (c : Nat) →
  SymbolicRestEnergyReadoff mass c
symbolicRestEnergyReadoff mass c =
  record
    { restEnergy =
        massTimesCSquared mass c
    ; restEnergyEqualsMassTimesCSquared =
        refl
    ; nonRelativisticKineticMatchingNarrativeRecorded =
        true
    ; nonRelativisticKineticMatchingNarrativeRecordedIsTrue =
        refl
    ; ultraRelativisticMasslessLimitNarrativeRecorded =
        true
    ; ultraRelativisticMasslessLimitNarrativeRecordedIsTrue =
        refl
    ; readoffBoundary =
        "Narrative readoff records the intended kinetic matching c^2 / (2 E0) = 1 / (2 m)"
        ∷ "The symbolic rest-energy carrier is therefore definitionally mass * c^2"
        ∷ "No dispersion implication, real-analysis Taylor remainder, limit theorem, or physical-unit calibration is constructed here"
        ∷ []
    }

data BalancedTritRestEnergyBoundary : Set where
  flatSectorOnly :
    BalancedTritRestEnergyBoundary
  noPhysicalUnitCalibration :
    BalancedTritRestEnergyBoundary
  noNonFlatYangMillsPromotion :
    BalancedTritRestEnergyBoundary
  noSourcedGRPromotion :
    BalancedTritRestEnergyBoundary
  noTerminalPromotion :
    BalancedTritRestEnergyBoundary

canonicalBalancedTritRestEnergyBoundaries :
  List BalancedTritRestEnergyBoundary
canonicalBalancedTritRestEnergyBoundaries =
  flatSectorOnly
  ∷ noPhysicalUnitCalibration
  ∷ noNonFlatYangMillsPromotion
  ∷ noSourcedGRPromotion
  ∷ noTerminalPromotion
  ∷ []

record BalancedTritRestEnergyReceipt : Setω where
  field
    carrierStage :
      BalancedTritDialecticalCarrierStage

    strengthNormStage :
      CDQStrengthWeightNormStage

    flatQuadraticSeedStage :
      FlatClosureQuadraticDispersionSeedStage

    symbolicMass :
      Nat

    symbolicSpeedOfLight :
      Nat

    restEnergyReadoff :
      SymbolicRestEnergyReadoff symbolicMass symbolicSpeedOfLight

    sqrtTaylorKineticTarget :
      SqrtTaylorKineticTargetSurface
        symbolicMass
        symbolicSpeedOfLight
        (SymbolicRestEnergyReadoff.restEnergy restEnergyReadoff)
        1

    formalTaylorKineticMatching :
      FormalTaylorKineticMatchingReceipt
        symbolicMass
        symbolicSpeedOfLight
        1

    restEnergyEqualsMC2 :
      SymbolicRestEnergyReadoff.restEnergy restEnergyReadoff
      ≡
      massTimesCSquared symbolicMass symbolicSpeedOfLight

    naturalUnitsCalibrationReceipt :
      Candidate256NaturalUnitsCalibrationReceipt

    naturalUnitsPromoted :
      Bool

    naturalUnitsPromotedIsTrue :
      naturalUnitsPromoted ≡ true

    siUnitsPromoted :
      Bool

    siUnitsPromotedIsFalse :
      siUnitsPromoted ≡ false

    candidate256PhysicalCalibrationConstructed :
      Bool

    candidate256PhysicalCalibrationConstructedIsFalse :
      candidate256PhysicalCalibrationConstructed ≡ false

    candidate256PhysicalCalibrationImpossibleHere :
      W4External.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

    candidate256PhysicalCalibrationHardHaltRecorded :
      Bool

    candidate256PhysicalCalibrationHardHaltRecordedIsTrue :
      candidate256PhysicalCalibrationHardHaltRecorded ≡ true

    receiptBoundaries :
      List BalancedTritRestEnergyBoundary

    receiptBoundariesAreCanonical :
      receiptBoundaries ≡ canonicalBalancedTritRestEnergyBoundaries

    narrativeBoundary :
      List String

open BalancedTritRestEnergyReceipt public

balancedTritRestEnergyReceipt :
  (mass : Nat) →
  (c : Nat) →
  BalancedTritRestEnergyReceipt
balancedTritRestEnergyReceipt mass c =
  record
    { carrierStage =
        canonicalBalancedTritDialecticalCarrierStage
    ; strengthNormStage =
        canonicalCDQStrengthWeightNormStage
    ; flatQuadraticSeedStage =
        canonicalFlatClosureQuadraticDispersionSeedStage
    ; symbolicMass =
        mass
    ; symbolicSpeedOfLight =
        c
    ; restEnergyReadoff =
        symbolicRestEnergyReadoff mass c
    ; sqrtTaylorKineticTarget =
        sqrtTaylorKineticTargetSurface mass c 1
    ; formalTaylorKineticMatching =
        formalTaylorKineticMatchingReceipt mass c 1
    ; restEnergyEqualsMC2 =
        refl
    ; naturalUnitsCalibrationReceipt =
        candidate256NaturalUnitsCalibrationReceipt
    ; naturalUnitsPromoted =
        true
    ; naturalUnitsPromotedIsTrue =
        refl
    ; siUnitsPromoted =
        false
    ; siUnitsPromotedIsFalse =
        refl
    ; candidate256PhysicalCalibrationConstructed =
        false
    ; candidate256PhysicalCalibrationConstructedIsFalse =
        refl
    ; candidate256PhysicalCalibrationImpossibleHere =
        W4External.candidate256PhysicalCalibrationExternalReceiptImpossibleWithoutExternalAuthority
    ; candidate256PhysicalCalibrationHardHaltRecorded =
        true
    ; candidate256PhysicalCalibrationHardHaltRecordedIsTrue =
        refl
    ; receiptBoundaries =
        canonicalBalancedTritRestEnergyBoundaries
    ; receiptBoundariesAreCanonical =
        refl
    ; narrativeBoundary =
        "Inhabited receipt bundle: T involution + depth invariance + pow3 strength norm"
        ∷ "Inhabited receipt bundle: selected SFGC exterior d^2 = 0 + vacuum flatness"
        ∷ "Inhabited receipt bundle: known-limits causal propagation/coherence + Minkowski quadratic"
        ∷ "Inhabited symbolic bridge: Candidate256 pow3 address weight + FVI.primeBump lane weight -> |p|^2"
        ∷ "Inhabited symbolic target: E^2 = c^2 |p|^2 + E0^2 and sqrt/Taylor kinetic matching surface"
        ∷ "Inhabited symbolic matching receipt: first Taylor correction c^2 |p|^2 / (2 E0) is paired with |p|^2 / (2 m) under E0 = m c^2"
        ∷ "Inhabited symbolic readoff: restEnergy = mass * c^2"
        ∷ "Option A natural units are promoted definitionally with c=1 and candidate256NormUnit as mass/energy unit"
        ∷ "No formal implication from TSFV/CDQ into SFGC/KnownLimits/Minkowski is constructed here"
        ∷ "Hard halt: SI Candidate256PhysicalCalibrationExternalReceipt is impossibleWithoutExternalAuthority at the current W4 boundary"
        ∷ "Fail-closed: physical-unit calibration, non-flat YM, sourced GR, SM, Clay, and terminal promotion are not constructed"
        ∷ []
    }

canonicalBalancedTritRestEnergyReceipt :
  BalancedTritRestEnergyReceipt
canonicalBalancedTritRestEnergyReceipt =
  balancedTritRestEnergyReceipt 1 1

balancedTritRestEnergyReceiptRestEnergyEqualsMC2 :
  BalancedTritRestEnergyReceipt.restEnergyEqualsMC2
    canonicalBalancedTritRestEnergyReceipt
  ≡
  refl
balancedTritRestEnergyReceiptRestEnergyEqualsMC2 =
  refl

balancedTritRestEnergyReceiptNoPhysicalCalibration :
  BalancedTritRestEnergyReceipt.candidate256PhysicalCalibrationConstructed
    canonicalBalancedTritRestEnergyReceipt
  ≡
  false
balancedTritRestEnergyReceiptNoPhysicalCalibration =
  refl

balancedTritRestEnergyReceiptNaturalUnitsPromoted :
  BalancedTritRestEnergyReceipt.naturalUnitsPromoted
    canonicalBalancedTritRestEnergyReceipt
  ≡
  true
balancedTritRestEnergyReceiptNaturalUnitsPromoted =
  refl

balancedTritRestEnergyReceiptSIUnitsNotPromoted :
  BalancedTritRestEnergyReceipt.siUnitsPromoted
    canonicalBalancedTritRestEnergyReceipt
  ≡
  false
balancedTritRestEnergyReceiptSIUnitsNotPromoted =
  refl

record L6CanonicalNaturalUnitsVerdict : Setω where
  field
    receipt :
      BalancedTritRestEnergyReceipt

    receiptIsCanonical :
      Bool

    receiptIsCanonicalIsTrue :
      receiptIsCanonical ≡ true

    symbolicSpeedOfLightIsOne :
      BalancedTritRestEnergyReceipt.symbolicSpeedOfLight receipt
      ≡
      1

    naturalUnitsReceipt :
      Candidate256NaturalUnitsCalibrationReceipt

    naturalSpeedOfLightIsOne :
      Candidate256NaturalUnitsCalibrationReceipt.naturalSpeedOfLight
        naturalUnitsReceipt
      ≡
      1

    naturalUnitsPromoted :
      Bool

    naturalUnitsPromotedIsTrue :
      naturalUnitsPromoted ≡ true

    siUnitsPromoted :
      Bool

    siUnitsPromotedIsFalse :
      siUnitsPromoted ≡ false

    candidate256PhysicalCalibrationConstructed :
      Bool

    candidate256PhysicalCalibrationConstructedIsFalse :
      candidate256PhysicalCalibrationConstructed ≡ false

    verdictBoundary :
      List String

open L6CanonicalNaturalUnitsVerdict public

canonicalL6CanonicalNaturalUnitsVerdict :
  L6CanonicalNaturalUnitsVerdict
canonicalL6CanonicalNaturalUnitsVerdict =
  record
    { receipt =
        canonicalBalancedTritRestEnergyReceipt
    ; receiptIsCanonical =
        true
    ; receiptIsCanonicalIsTrue =
        refl
    ; symbolicSpeedOfLightIsOne =
        refl
    ; naturalUnitsReceipt =
        candidate256NaturalUnitsCalibrationReceipt
    ; naturalSpeedOfLightIsOne =
        refl
    ; naturalUnitsPromoted =
        true
    ; naturalUnitsPromotedIsTrue =
        refl
    ; siUnitsPromoted =
        false
    ; siUnitsPromotedIsFalse =
        refl
    ; candidate256PhysicalCalibrationConstructed =
        false
    ; candidate256PhysicalCalibrationConstructedIsFalse =
        refl
    ; verdictBoundary =
        "l6 confirms natural units only on the canonical c=1 receipt"
        ∷ "Candidate256NaturalUnitsCalibrationReceipt supplies naturalSpeedOfLight = 1 and naturalUnitsPromoted = true"
        ∷ "BalancedTritRestEnergyReceipt keeps siUnitsPromoted = false"
        ∷ "Candidate256PhysicalCalibrationExternalReceipt remains the blocked SI calibration authority"
        ∷ []
    }
