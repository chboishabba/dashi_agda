module DASHI.Physics.Closure.Depth9ConnectionAndCurvature where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.Closure.YangMillsGate3DiscreteGeometryReceipt as Gate3
import DASHI.Physics.QFT.W3ToM3Iso as W3
import DASHI.Physics.SFGC.NonAbelian.DepthQuotientIsoSU3 as SU3
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftFiniteMatrixSymmetry as SFMS
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4

------------------------------------------------------------------------
-- Depth-9 connection and curvature surface.
--
-- This module does not claim a strict non-flat Yang-Mills promotion.  It
-- re-exports the concrete Gate 3 depth-9 connection witness and records the
-- exact fail-closed blocker chain from the Yang-Mills obstruction layer.

record Depth9ConnectionAndCurvatureReceipt : Setω where
  field
    connectionOnDepth9 :
      Gate3.ConnectionOnDepth9

    connectionOnDepth9IsCanonical :
      connectionOnDepth9 ≡ Gate3.canonicalConnectionOnDepth9

    curvatureNonFlat :
      Gate3.CurvatureNonFlat

    curvatureNonFlatIsCanonical :
      curvatureNonFlat ≡ Gate3.canonicalCurvatureNonFlat

    finiteNonzeroCurvatureComponent :
      Gate3.FiniteNonzeroCurvatureComponent

    finiteNonzeroCurvatureComponentIsCanonical :
      finiteNonzeroCurvatureComponent
      ≡
      Gate3.canonicalFiniteNonzeroCurvatureComponent

    finiteNonzeroCurvatureComponentNotPromoted :
      Gate3.FiniteNonzeroCurvatureComponent.promotedToStrictRealSU3HodgeYM
        finiteNonzeroCurvatureComponent
      ≡
      false

    finiteAlgebraAndOperatorWiring :
      Gate3.FiniteAlgebraAndOperatorWiring

    finiteAlgebraAndOperatorWiringIsCanonical :
      finiteAlgebraAndOperatorWiring
      ≡
      Gate3.canonicalFiniteAlgebraAndOperatorWiring

    localFiniteBracketAntisymmetryIsCanonical :
      Gate3.FiniteAlgebraAndOperatorWiring.localFiniteBracketAntisymmetry
        finiteAlgebraAndOperatorWiring
      ≡
      YMObs.localFiniteLie3BracketAntisymmetry

    localFiniteJacobiWitnessIsCanonical :
      Gate3.FiniteAlgebraAndOperatorWiring.localFiniteJacobiWitness
        finiteAlgebraAndOperatorWiring
      ≡
      YMObs.localFiniteLie3JacobiWitness

    localFiniteDASquaredEqualsBracketFIsCanonical :
      Gate3.FiniteAlgebraAndOperatorWiring.upper6DASquaredBracketStrictReceipt
        finiteAlgebraAndOperatorWiring
      ≡
      YMObs.canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt

    firstStrictNonFlatBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictNonFlatBlockerIsExact :
      firstStrictNonFlatBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    transportBlocker :
      YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    transportBlockerIsExact :
      transportBlocker
      ≡
      YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    variationBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    variationBlockerIsExact :
      variationBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    gate3NonFlatPromotionClaimed :
      Bool

    gate3NonFlatPromotionClaimedIsFalse :
      gate3NonFlatPromotionClaimed ≡ false

    boundary :
      List String

canonicalDepth9ConnectionAndCurvatureReceipt :
  Depth9ConnectionAndCurvatureReceipt
canonicalDepth9ConnectionAndCurvatureReceipt =
  record
    { connectionOnDepth9 =
        Gate3.canonicalConnectionOnDepth9
    ; connectionOnDepth9IsCanonical =
        refl
    ; curvatureNonFlat =
        Gate3.canonicalCurvatureNonFlat
    ; curvatureNonFlatIsCanonical =
        refl
    ; finiteNonzeroCurvatureComponent =
        Gate3.canonicalFiniteNonzeroCurvatureComponent
    ; finiteNonzeroCurvatureComponentIsCanonical =
        refl
    ; finiteNonzeroCurvatureComponentNotPromoted =
        refl
    ; finiteAlgebraAndOperatorWiring =
        Gate3.canonicalFiniteAlgebraAndOperatorWiring
    ; finiteAlgebraAndOperatorWiringIsCanonical =
        refl
    ; localFiniteBracketAntisymmetryIsCanonical =
        refl
    ; localFiniteJacobiWitnessIsCanonical =
        refl
    ; localFiniteDASquaredEqualsBracketFIsCanonical =
        refl
    ; firstStrictNonFlatBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; firstStrictNonFlatBlockerIsExact =
        refl
    ; transportBlocker =
        YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; transportBlockerIsExact =
        refl
    ; variationBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; variationBlockerIsExact =
        refl
    ; gate3NonFlatPromotionClaimed =
        false
    ; gate3NonFlatPromotionClaimedIsFalse =
        refl
    ; boundary =
        "Depth-9 reuses the existing Gate 3 connection witness and curvature witness without inventing a new non-flat theorem"
        ∷ "Depth-9 now also threads the finite nonzero SFGCSite2D component: reference curvature evaluates to φ1 and remains unpromoted"
        ∷ "Depth-9 also reuses the concrete local finite bracket antisymmetry, Jacobi, and D_A^2=[F_A,_] witnesses from Gate 3"
        ∷ "The first strict non-flat blocker remains missingNonFlatSFGCSite2DConnectionCurvature"
        ∷ "The downstream transport-action blocker remains missingFieldStrengthTransportActionOnSelectedGaugeBundle"
        ∷ "The variation-pairing blocker remains missingVariationPairingForSelectedHodgeStar"
        ∷ "No non-flat promotion is claimed by this surface"
        ∷ []
    }

connectionOnDepth9 :
  Gate3.ConnectionOnDepth9
connectionOnDepth9 =
  Depth9ConnectionAndCurvatureReceipt.connectionOnDepth9
    canonicalDepth9ConnectionAndCurvatureReceipt

curvatureNonFlat :
  Gate3.CurvatureNonFlat
curvatureNonFlat =
  Depth9ConnectionAndCurvatureReceipt.curvatureNonFlat
    canonicalDepth9ConnectionAndCurvatureReceipt

------------------------------------------------------------------------
-- Depth-9 finite carrier curvature 2-form over all available 2-cells.
--
-- The available depth-9 2-cells in this lane are exactly the finite
-- SFGCSite2D plaquettes.  A 2-form is therefore a total evaluator on every
-- `SFGCSite2DPlaquette`, not just the reference plaquette.  The reference
-- plaquette is retained only as the inhabited non-vacuum component.

record Depth9FiniteCarrierCurvature2Form : Set₁ where
  field
    twoCellCarrier :
      Set

    twoCellCarrierIsSFGCSite2DPlaquette :
      twoCellCarrier ≡ SFGC.SFGCSite2DPlaquette

    phaseCarrier :
      Set

    phaseCarrierIsPhase4 :
      phaseCarrier ≡ SPTI4.Phase4

    finiteMatrixSymmetry :
      SFMS.ShiftFiniteMatrixSymmetry

    finiteMatrixSymmetryIsCanonical :
      finiteMatrixSymmetry ≡ SFMS.shiftFiniteMatrixSymmetry

    localFiniteLieCarrier :
      Set

    localFiniteLieCarrierIsLie3 :
      localFiniteLieCarrier ≡ YMObs.YMSFGCLocalFiniteLie3Carrier

    localFiniteCommutator :
      YMObs.YMSFGCLocalFiniteLie3Carrier →
      YMObs.YMSFGCLocalFiniteLie3Carrier →
      YMObs.YMSFGCLocalFiniteLie3Carrier

    localFiniteCommutatorIsCanonical :
      localFiniteCommutator ≡ YMObs.localFiniteLie3Bracket

    localFiniteCommutatorAntisymmetry :
      (x y : YMObs.YMSFGCLocalFiniteLie3Carrier) →
      YMObs.localFiniteLie3Bracket x y
      ≡
      YMObs.localFiniteLie3Neg (YMObs.localFiniteLie3Bracket y x)

    localFiniteCommutatorAntisymmetryIsCanonical :
      localFiniteCommutatorAntisymmetry
      ≡
      YMObs.localFiniteLie3BracketAntisymmetry

    localFiniteJacobiWitness :
      (x y z : YMObs.YMSFGCLocalFiniteLie3Carrier) →
      YMObs.localFiniteLie3JacobiAdd
        (YMObs.localFiniteLie3JacobiAdd
          (YMObs.localFiniteLie3Bracket x
            (YMObs.localFiniteLie3Bracket y z))
          (YMObs.localFiniteLie3Bracket y
            (YMObs.localFiniteLie3Bracket z x)))
        (YMObs.localFiniteLie3Bracket z
          (YMObs.localFiniteLie3Bracket x y))
      ≡
      YMObs.lieZero

    localFiniteJacobiWitnessIsCanonical :
      localFiniteJacobiWitness
      ≡
      YMObs.localFiniteLie3JacobiWitness

    referenceConnection :
      SFGC.SFGCSite2DDiscrete1Form

    referenceConnectionIsCanonical :
      referenceConnection ≡ YMObs.sfgcReferenceNonFlat1Form

    curvature2Form :
      SFGC.SFGCSite2DDiscrete2Form

    curvature2FormIsReference :
      curvature2Form ≡ YMObs.sfgcReferenceNonFlatCurvature2Form

    curvature2FormIsDelta1ReferenceConnection :
      curvature2Form ≡ SFGC.sfgcSite2Dδ₁ referenceConnection

    curvatureComponent :
      SFGC.SFGCSite2DPlaquette →
      SPTI4.Phase4

    curvatureComponentIsEvaluation :
      curvatureComponent ≡ SFGC.sfgcSite2DEvaluate2 curvature2Form

    curvatureComponentCoversEveryAvailable2Cell :
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      curvatureComponent plaquette
      ≡
      SFGC.sfgcSite2DEvaluate2 curvature2Form plaquette

    fieldStrength :
      SFGC.SFGCSite2DFieldStrengthBridge

    fieldStrengthIsFromCurvature :
      fieldStrength ≡ SFGC.sfgcSite2DFieldStrengthFromCurvature curvature2Form

    fieldStrengthCoversEveryAvailable2Cell :
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        fieldStrength
        plaquette
      ≡
      curvatureComponent plaquette

    referencePlaquette :
      SFGC.SFGCSite2DPlaquette

    referencePlaquetteIsCanonical :
      referencePlaquette ≡ YMObs.sfgcReferencePlaquette

    referencePlaquetteComponentIsPhi1 :
      curvatureComponent referencePlaquette
      ≡
      SPTI4.φ1

    referencePlaquetteComponentNotVacuum :
      curvatureComponent referencePlaquette
      ≡
      SPTI4.φ0 →
      YMObs.YMSFGCEmpty

    finiteCarrierPromotedToStrictRealSU3HodgeYM :
      Bool

    finiteCarrierPromotedToStrictRealSU3HodgeYMIsFalse :
      finiteCarrierPromotedToStrictRealSU3HodgeYM ≡ false

    finiteCarrierBoundary :
      List String

canonicalDepth9FiniteCarrierCurvature2Form :
  Depth9FiniteCarrierCurvature2Form
canonicalDepth9FiniteCarrierCurvature2Form =
  record
    { twoCellCarrier =
        SFGC.SFGCSite2DPlaquette
    ; twoCellCarrierIsSFGCSite2DPlaquette =
        refl
    ; phaseCarrier =
        SPTI4.Phase4
    ; phaseCarrierIsPhase4 =
        refl
    ; finiteMatrixSymmetry =
        SFMS.shiftFiniteMatrixSymmetry
    ; finiteMatrixSymmetryIsCanonical =
        refl
    ; localFiniteLieCarrier =
        YMObs.YMSFGCLocalFiniteLie3Carrier
    ; localFiniteLieCarrierIsLie3 =
        refl
    ; localFiniteCommutator =
        YMObs.localFiniteLie3Bracket
    ; localFiniteCommutatorIsCanonical =
        refl
    ; localFiniteCommutatorAntisymmetry =
        YMObs.localFiniteLie3BracketAntisymmetry
    ; localFiniteCommutatorAntisymmetryIsCanonical =
        refl
    ; localFiniteJacobiWitness =
        YMObs.localFiniteLie3JacobiWitness
    ; localFiniteJacobiWitnessIsCanonical =
        refl
    ; referenceConnection =
        YMObs.sfgcReferenceNonFlat1Form
    ; referenceConnectionIsCanonical =
        refl
    ; curvature2Form =
        YMObs.sfgcReferenceNonFlatCurvature2Form
    ; curvature2FormIsReference =
        refl
    ; curvature2FormIsDelta1ReferenceConnection =
        refl
    ; curvatureComponent =
        SFGC.sfgcSite2DEvaluate2 YMObs.sfgcReferenceNonFlatCurvature2Form
    ; curvatureComponentIsEvaluation =
        refl
    ; curvatureComponentCoversEveryAvailable2Cell =
        λ plaquette → refl
    ; fieldStrength =
        YMObs.sfgcReferenceNonFlatFieldStrengthBridge
    ; fieldStrengthIsFromCurvature =
        refl
    ; fieldStrengthCoversEveryAvailable2Cell =
        λ plaquette → refl
    ; referencePlaquette =
        YMObs.sfgcReferencePlaquette
    ; referencePlaquetteIsCanonical =
        refl
    ; referencePlaquetteComponentIsPhi1 =
        YMObs.sfgcReferenceNonFlatCurvatureAtReference
    ; referencePlaquetteComponentNotVacuum =
        YMObs.sfgcReferenceNonFlatCurvatureAtReferenceNotVacuum
    ; finiteCarrierPromotedToStrictRealSU3HodgeYM =
        false
    ; finiteCarrierPromotedToStrictRealSU3HodgeYMIsFalse =
        refl
    ; finiteCarrierBoundary =
        "Depth-9 finite carrier 2-cells are SFGCSite2DPlaquette values, and curvatureComponent evaluates the 2-form on every available plaquette"
        ∷ "The finite 2-form is the existing δ1 reference curvature, not a new continuum or strict SU(3) curvature theorem"
        ∷ "The reference plaquette remains the inhabited non-vacuum component: curvatureComponent referencePlaquette = φ1 and φ1 is constructor-separated from φ0"
        ∷ "Finite matrix evidence is the existing ShiftFiniteMatrixSymmetry package; local commutator evidence is the existing finite Lie3 bracket with antisymmetry and Jacobi witnesses"
        ∷ "No strict real SU(3), Hodge-star, Yang-Mills equation, Clay mass-gap, or continuum promotion is claimed"
        ∷ []
    }

depth9FiniteCurvatureComponent :
  SFGC.SFGCSite2DPlaquette →
  SPTI4.Phase4
depth9FiniteCurvatureComponent =
  Depth9FiniteCarrierCurvature2Form.curvatureComponent
    canonicalDepth9FiniteCarrierCurvature2Form

depth9FiniteCurvatureComponentCoversEveryAvailable2Cell :
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  depth9FiniteCurvatureComponent plaquette
  ≡
  SFGC.sfgcSite2DEvaluate2
    YMObs.sfgcReferenceNonFlatCurvature2Form
    plaquette
depth9FiniteCurvatureComponentCoversEveryAvailable2Cell =
  Depth9FiniteCarrierCurvature2Form.curvatureComponentCoversEveryAvailable2Cell
    canonicalDepth9FiniteCarrierCurvature2Form

depth9FiniteCurvatureAtReference :
  depth9FiniteCurvatureComponent YMObs.sfgcReferencePlaquette
  ≡
  SPTI4.φ1
depth9FiniteCurvatureAtReference =
  Depth9FiniteCarrierCurvature2Form.referencePlaquetteComponentIsPhi1
    canonicalDepth9FiniteCarrierCurvature2Form

------------------------------------------------------------------------
-- Chain B1 explicit finite nonzero curvature computation.
--
-- This is the public finite computation surface for the current B1 route.
-- It does not alter the older flat YM.F_A surface; instead it records the
-- already checked SFGCSite2D/Phase4 field-strength component used by Gate 3.

record ChainB1ExplicitNonzeroYMCurvatureFiniteComputation : Setω where
  field
    finiteComponent :
      Gate3.FiniteNonzeroCurvatureComponent

    finiteComponentIsCanonical :
      finiteComponent
      ≡
      Gate3.canonicalFiniteNonzeroCurvatureComponent

    referenceConnection :
      SFGC.SFGCSite2DDiscrete1Form

    referenceConnectionIsCanonical :
      referenceConnection
      ≡
      YMObs.sfgcReferenceNonFlat1Form

    referenceCurvature :
      SFGC.SFGCSite2DDiscrete2Form

    referenceCurvatureIsCanonical :
      referenceCurvature
      ≡
      YMObs.sfgcReferenceNonFlatCurvature2Form

    referenceFieldStrength :
      SFGC.SFGCSite2DFieldStrengthBridge

    referenceFieldStrengthIsCanonical :
      referenceFieldStrength
      ≡
      YMObs.sfgcReferenceNonFlatFieldStrengthBridge

    referencePlaquette :
      SFGC.SFGCSite2DPlaquette

    referencePlaquetteIsCanonical :
      referencePlaquette
      ≡
      YMObs.sfgcReferencePlaquette

    finiteCurvatureComputesPhi1 :
      SFGC.sfgcSite2DEvaluate2 referenceCurvature referencePlaquette
      ≡
      SPTI4.φ1

    finiteFieldStrengthComputesPhi1 :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        referenceFieldStrength
        referencePlaquette
      ≡
      SPTI4.φ1

    finiteCurvatureNotVacuum :
      SFGC.sfgcSite2DEvaluate2 referenceCurvature referencePlaquette
      ≡
      SPTI4.φ0 →
      YMObs.YMSFGCEmpty

    w3ClockShiftBridge :
      W3.W3ToM3Iso

    w3ClockShiftBridgeIsCanonical :
      w3ClockShiftBridge
      ≡
      W3.canonicalW3ToM3Iso

    su3DepthQuotientBridge :
      SU3.DepthQuotientIsoSU3Witness

    su3DepthQuotientBridgeIsCanonical :
      su3DepthQuotientBridge
      ≡
      SU3.canonicalDepthQuotientIsoSU3Witness

    inhabitedFiniteFANonzero :
      SFGC.sfgcSite2DEvaluate2 referenceCurvature referencePlaquette
      ≡
      SPTI4.φ1

    strictRealSU3HodgeYMPromoted :
      Bool

    strictRealSU3HodgeYMPromotedIsFalse :
      strictRealSU3HodgeYMPromoted
      ≡
      false

    chainB1Boundary :
      List String

canonicalChainB1ExplicitNonzeroYMCurvatureFiniteComputation :
  ChainB1ExplicitNonzeroYMCurvatureFiniteComputation
canonicalChainB1ExplicitNonzeroYMCurvatureFiniteComputation =
  record
    { finiteComponent =
        Gate3.canonicalFiniteNonzeroCurvatureComponent
    ; finiteComponentIsCanonical =
        refl
    ; referenceConnection =
        YMObs.sfgcReferenceNonFlat1Form
    ; referenceConnectionIsCanonical =
        refl
    ; referenceCurvature =
        YMObs.sfgcReferenceNonFlatCurvature2Form
    ; referenceCurvatureIsCanonical =
        refl
    ; referenceFieldStrength =
        YMObs.sfgcReferenceNonFlatFieldStrengthBridge
    ; referenceFieldStrengthIsCanonical =
        refl
    ; referencePlaquette =
        YMObs.sfgcReferencePlaquette
    ; referencePlaquetteIsCanonical =
        refl
    ; finiteCurvatureComputesPhi1 =
        YMObs.sfgcReferenceNonFlatCurvatureAtReference
    ; finiteFieldStrengthComputesPhi1 =
        YMObs.sfgcReferenceNonFlatFieldStrengthAtReference
    ; finiteCurvatureNotVacuum =
        YMObs.sfgcReferenceNonFlatCurvatureAtReferenceNotVacuum
    ; w3ClockShiftBridge =
        W3.canonicalW3ToM3Iso
    ; w3ClockShiftBridgeIsCanonical =
        refl
    ; su3DepthQuotientBridge =
        SU3.canonicalDepthQuotientIsoSU3Witness
    ; su3DepthQuotientBridgeIsCanonical =
        refl
    ; inhabitedFiniteFANonzero =
        YMObs.sfgcReferenceNonFlatCurvatureAtReference
    ; strictRealSU3HodgeYMPromoted =
        false
    ; strictRealSU3HodgeYMPromotedIsFalse =
        refl
    ; chainB1Boundary =
        "Chain B1 finite computation: the reference SFGCSite2D connection has δ1 curvature φ1 at the reference plaquette"
        ∷ "The field-strength bridge computes the same φ1 Wilson-loop phase at that plaquette"
        ∷ "Nonzero is inhabited finitely by φ1 together with the constructor-separation witness φ1-not-φ0"
        ∷ "The computation consumes the existing W3-to-M3 and DepthQuotientIsoSU3 surfaces"
        ∷ "This is not a strict real SU3 Hodge/Yang-Mills promotion; that flag remains false"
        ∷ []
    }

chainB1FiniteFANonzeroAtReference :
  SFGC.sfgcSite2DEvaluate2
    YMObs.sfgcReferenceNonFlatCurvature2Form
    YMObs.sfgcReferencePlaquette
  ≡
  SPTI4.φ1
chainB1FiniteFANonzeroAtReference =
  ChainB1ExplicitNonzeroYMCurvatureFiniteComputation.inhabitedFiniteFANonzero
    canonicalChainB1ExplicitNonzeroYMCurvatureFiniteComputation

chainB1FiniteFANotVacuumAtReference :
  SFGC.sfgcSite2DEvaluate2
    YMObs.sfgcReferenceNonFlatCurvature2Form
    YMObs.sfgcReferencePlaquette
  ≡
  SPTI4.φ0 →
  YMObs.YMSFGCEmpty
chainB1FiniteFANotVacuumAtReference =
  ChainB1ExplicitNonzeroYMCurvatureFiniteComputation.finiteCurvatureNotVacuum
    canonicalChainB1ExplicitNonzeroYMCurvatureFiniteComputation
