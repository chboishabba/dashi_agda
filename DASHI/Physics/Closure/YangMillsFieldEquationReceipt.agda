module DASHI.Physics.Closure.YangMillsFieldEquationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ)
open import Data.Integer using () renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Algebra.Trit as Trit
import DASHI.Physics.Closure.DiscreteBianchiIdentityReceipt as Bianchi
import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface as YMGap
import DASHI.Physics.Closure.ContinuumClayMassGapReceiptObligation as Clay
import DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT as DCRT
import DASHI.Physics.Closure.DiscreteStokesBianchiObstruction as StokesObs
import DASHI.Physics.Closure.G2DiscreteCurvatureCarrier as G2DCC
import DASHI.Physics.Closure.G2NondegeneratePlaquetteSchema as G2NP
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.YM.CovariantDerivative as YM_CD
import DASHI.Physics.YM.FieldStrength as YM_FS
import DASHI.Physics.YM.SU2LieAlgebra as YM_SU2
import DASHI.Physics.YM.YangMillsAction as YM_YM
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4

------------------------------------------------------------------------
-- Yang-Mills field-equation receipt surface.
--
-- This module records the minimal target shape for a Yang-Mills field
-- equation receipt: connection, curvature, covariant derivative, D * F = J,
-- and the Bianchi identity.  It consumes only existing candidate/obligation
-- surfaces, including the selected SFGCSite2D exterior d^2 = 0 witness, and
-- deliberately constructs no Yang-Mills equation proof, no mass gap result, no
-- Clay problem result, and no spectral-gap theorem.

data YangMillsFieldEquationReceiptStatus : Set where
  obligationTargetOnly :
    YangMillsFieldEquationReceiptStatus

data YangMillsFieldEquationFirstMissing : Set where
  missingDiscreteCurvatureCarrierForSFGCGaugeField :
    YangMillsFieldEquationFirstMissing

  missingCovariantDerivativeHodgeCurrentPackage :
    YangMillsFieldEquationFirstMissing

  missingDStarFEqualsJLaw :
    YangMillsFieldEquationFirstMissing

  missingYangMillsBianchiDFEqualsZeroLaw :
    YangMillsFieldEquationFirstMissing

data YangMillsFieldEquationTargetObligation : Set where
  connectionTarget :
    YangMillsFieldEquationTargetObligation
  curvatureTarget :
    YangMillsFieldEquationTargetObligation
  covariantDerivativeTarget :
    YangMillsFieldEquationTargetObligation
  dStarFEqualsJTarget :
    YangMillsFieldEquationTargetObligation
  bianchiIdentityTarget :
    YangMillsFieldEquationTargetObligation

canonicalYangMillsFieldEquationTargetObligations :
  List YangMillsFieldEquationTargetObligation
canonicalYangMillsFieldEquationTargetObligations =
  connectionTarget
  ∷ curvatureTarget
  ∷ covariantDerivativeTarget
  ∷ dStarFEqualsJTarget
  ∷ bianchiIdentityTarget
  ∷ []

data YangMillsFieldEquationUnsupportedClaim : Set where
  unsupportedYangMillsClosureClaim :
    YangMillsFieldEquationUnsupportedClaim
  unsupportedMaxwellClosureClaim :
    YangMillsFieldEquationUnsupportedClaim
  unsupportedMassGapClaim :
    YangMillsFieldEquationUnsupportedClaim
  unsupportedClayProblemClaim :
    YangMillsFieldEquationUnsupportedClaim
  unsupportedSpectralGapClaim :
    YangMillsFieldEquationUnsupportedClaim

canonicalYangMillsFieldEquationUnsupportedClaims :
  List YangMillsFieldEquationUnsupportedClaim
canonicalYangMillsFieldEquationUnsupportedClaims =
  unsupportedYangMillsClosureClaim
  ∷ unsupportedMaxwellClosureClaim
  ∷ unsupportedMassGapClaim
  ∷ unsupportedClayProblemClaim
  ∷ unsupportedSpectralGapClaim
  ∷ []

record YangMillsFieldEquationTarget : Set₂ where
  field
    ConnectionCarrier :
      Set₁

    CurvatureCarrier :
      Set₁

    DualCurvatureCarrier :
      Set

    CurrentCarrier :
      Set

    connectionToCurvature :
      ConnectionCarrier →
      CurvatureCarrier

    hodgeDual :
      CurvatureCarrier →
      DualCurvatureCarrier

    covariantDerivative :
      Set →
      Set

    dStarFEqualsJ :
      Set

    bianchiIdentity :
      Set

private
  ObligationConnectionCarrier :
    Set₁
  ObligationConnectionCarrier =
    DCRT.DiscreteConnectionCandidateFromCRT

  ObligationCurvatureCarrier :
    Set₁
  ObligationCurvatureCarrier =
    G2DCC.G2ShiftGaugeDiscreteCurvatureCarrierObligation

  ObligationDualCurvatureCarrier :
    Set
  ObligationDualCurvatureCarrier =
    YangMillsFieldEquationTargetObligation

  ObligationCurrentCarrier :
    Set
  ObligationCurrentCarrier =
    YangMillsFieldEquationTargetObligation

  obligationConnectionToCurvature :
    ObligationConnectionCarrier →
    ObligationCurvatureCarrier
  obligationConnectionToCurvature _ =
    G2DCC.canonicalSFGCGaugeDiscreteCurvatureCarrierObligation

  obligationHodgeDual :
    ObligationCurvatureCarrier →
    ObligationDualCurvatureCarrier
  obligationHodgeDual _ =
    dStarFEqualsJTarget

  obligationCovariantDerivative :
    Set →
    Set
  obligationCovariantDerivative target =
    target

canonicalYangMillsFieldEquationTarget :
  YangMillsFieldEquationTarget
canonicalYangMillsFieldEquationTarget =
  record
    { ConnectionCarrier =
        ObligationConnectionCarrier
    ; CurvatureCarrier =
        ObligationCurvatureCarrier
    ; DualCurvatureCarrier =
        ObligationDualCurvatureCarrier
    ; CurrentCarrier =
        ObligationCurrentCarrier
    ; connectionToCurvature =
        obligationConnectionToCurvature
    ; hodgeDual =
        obligationHodgeDual
    ; covariantDerivative =
        obligationCovariantDerivative
    ; dStarFEqualsJ =
        YangMillsFieldEquationTargetObligation
    ; bianchiIdentity =
        YangMillsFieldEquationTargetObligation
    }

routeBLowerHodgeStar :
  SFGC.SFGCSite2DFieldStrengthBridge →
  Bool
routeBLowerHodgeStar _ =
  false

routeBLowerCovariantDerivativeOnFieldStrength :
  SFGC.GaugeField →
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2DFieldStrengthBridge
routeBLowerCovariantDerivativeOnFieldStrength _ fieldStrength =
  fieldStrength

routeBLowerCovariantDerivativeOnDualCurvature :
  SFGC.GaugeField →
  Bool →
  Bool
routeBLowerCovariantDerivativeOnDualCurvature _ _ =
  false

routeBLowerCurrentSource :
  SFGC.GaugeField →
  Bool
routeBLowerCurrentSource _ =
  false

routeBLowerDStarFEqualsJLaw :
  (A : SFGC.GaugeField) →
  routeBLowerCovariantDerivativeOnDualCurvature
    A
    (routeBLowerHodgeStar
      (SFGC.sfgcSite2DFieldStrengthFromCurvature
        (SFGC.sfgcSite2Dδ₁
          (SFGC.sfgcSite2DConnectionTo1Form A))))
  ≡
  routeBLowerCurrentSource A
routeBLowerDStarFEqualsJLaw A =
  refl

routeBLowerCovariantBianchiTarget :
  SFGC.GaugeField →
  Set
routeBLowerCovariantBianchiTarget _ =
  YMObs.YangMillsBianchiMissingPrimitive

canonicalRouteBLowerDiscreteHodgeCovariantDerivativeSupply :
  YMObs.YMSFGCDiscreteHodgeCovariantDerivativePrimitiveSupply
canonicalRouteBLowerDiscreteHodgeCovariantDerivativeSupply =
  record
    { DualCurvatureCarrier =
        Bool
    ; CurrentCarrier =
        Bool
    ; hodgeStar =
        routeBLowerHodgeStar
    ; covariantDerivativeOnFieldStrength =
        routeBLowerCovariantDerivativeOnFieldStrength
    ; covariantDerivativeOnDualCurvature =
        routeBLowerCovariantDerivativeOnDualCurvature
    ; currentSource =
        routeBLowerCurrentSource
    ; dStarFEqualsJLaw =
        routeBLowerDStarFEqualsJLaw
    ; covariantBianchiTarget =
        routeBLowerCovariantBianchiTarget
    ; supplyBoundary =
        "Lower Route B Hodge/current carrier only: Bool dual curvature and Bool current collapse to false"
        ∷ "The inhabited D * F = J law is a definitional false == false equality, not a sourced Yang-Mills Euler-Lagrange equation"
        ∷ "The real selected Hodge star, current coupling, covariant derivative on dual curvature, and variation pairing remain requested primitives"
        ∷ []
    }

routeBSelectedHodgeStar :
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2DFieldStrengthBridge
routeBSelectedHodgeStar =
  YMObs.sfgcSelectedHodgeStarLowerCandidate

routeBSelectedCovariantDerivativeOnFieldStrength :
  SFGC.GaugeField →
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2DFieldStrengthBridge
routeBSelectedCovariantDerivativeOnFieldStrength _ fieldStrength =
  fieldStrength

routeBSelectedCovariantDerivativeOnDualCurvature :
  SFGC.GaugeField →
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2DFieldStrengthBridge
routeBSelectedCovariantDerivativeOnDualCurvature _ dualCurvature =
  dualCurvature

routeBSelectedCurrentSource :
  SFGC.GaugeField →
  SFGC.SFGCSite2DFieldStrengthBridge
routeBSelectedCurrentSource A =
  SFGC.sfgcSite2DFieldStrengthFromCurvature
    (SFGC.sfgcSite2Dδ₁
      (SFGC.sfgcSite2DConnectionTo1Form A))

routeBSelectedDStarFEqualsJLaw :
  (A : SFGC.GaugeField) →
  routeBSelectedCovariantDerivativeOnDualCurvature
    A
    (routeBSelectedHodgeStar
      (SFGC.sfgcSite2DFieldStrengthFromCurvature
        (SFGC.sfgcSite2Dδ₁
          (SFGC.sfgcSite2DConnectionTo1Form A))))
  ≡
  routeBSelectedCurrentSource A
routeBSelectedDStarFEqualsJLaw A =
  refl

canonicalRouteBSelectedDiscreteHodgeCovariantDerivativeSupply :
  YMObs.YMSFGCDiscreteHodgeCovariantDerivativePrimitiveSupply
canonicalRouteBSelectedDiscreteHodgeCovariantDerivativeSupply =
  record
    { DualCurvatureCarrier =
        SFGC.SFGCSite2DFieldStrengthBridge
    ; CurrentCarrier =
        SFGC.SFGCSite2DFieldStrengthBridge
    ; hodgeStar =
        routeBSelectedHodgeStar
    ; covariantDerivativeOnFieldStrength =
        routeBSelectedCovariantDerivativeOnFieldStrength
    ; covariantDerivativeOnDualCurvature =
        routeBSelectedCovariantDerivativeOnDualCurvature
    ; currentSource =
        routeBSelectedCurrentSource
    ; dStarFEqualsJLaw =
        routeBSelectedDStarFEqualsJLaw
    ; covariantBianchiTarget =
        routeBLowerCovariantBianchiTarget
    ; supplyBoundary =
        "Route B selected lower supply: hodgeStar is the m1/m2 identity endomap on SFGCSite2DFieldStrengthBridge"
        ∷ "covariantDerivativeOnDualCurvature is the identity probe on the same selected field-strength bridge carrier"
        ∷ "currentSource is the selected curvature field-strength bridge of A, so D * F = J closes definitionally"
        ∷ "This is still a lower selected-field-strength receipt, not a metric Hodge star, matter current, or variational Yang-Mills equation"
        ∷ []
    }

canonicalRouteBZeroDiscreteVariationIBPPrimitiveSupply :
  YMObs.YMSFGCDiscreteVariationIBPPrimitiveSupply
canonicalRouteBZeroDiscreteVariationIBPPrimitiveSupply =
  record
    { VariationCarrier =
        Bool
    ; ActionScalar =
        Bool
    ; combineActionScalar =
        λ _ _ → false
    ; action =
        λ _ → false
    ; variationOfAction =
        λ _ _ → false
    ; eulerLagrangePairing =
        λ _ _ → false
    ; boundaryTerm =
        λ _ _ → false
    ; discreteIBPLaw =
        λ _ _ → refl
    ; boundaryVanishingOrCondition =
        λ _ _ → Bool
    ; eulerLagrangeDStarFEqualsJTarget =
        λ _ → Bool
    ; supplyBoundary =
        "Zero discrete variation/IBP primitive supply: all scalar terms collapse to false and the IBP law is definitional"
        ∷ "This only stages the primitive record shape; it does not supply a selected Hodge/action variation pairing"
        ∷ "missingVariationPairingForSelectedHodgeStar remains the first strict Route B blocker"
        ∷ []
    }

canonicalRouteBU2NonFlatLatticeConnectionPrimitiveSupply :
  YMObs.YMSFGCUserSuppliedNonFlatLatticeConnectionPrimitiveSupply
canonicalRouteBU2NonFlatLatticeConnectionPrimitiveSupply =
  record
    { NonFlatConnectionCarrier =
        SFGC.SFGCSite2DDiscrete1Form
    ; connectionToGaugeField =
        λ _ → SFGC.vacuumGaugeField
    ; gaugeTransformConnection =
        λ _ connection → connection
    ; connectionCurvature =
        YMObs.sfgcFiniteSite2D1FormCurvatureBridge
    ; edgeTransport =
        λ _ _ fieldStrength → fieldStrength
    ; plaquetteUsesExportedBoundaryEdges =
        λ _ → Bool
    ; nonFlatWitness =
        Bool
    ; supplyBoundary =
        "u2 staging supply: the non-flat connection carrier is SFGCSite2DDiscrete1Form and curvature is δ1(connection)"
        ∷ "The gauge transform and edge transport fields are identity probes only"
        ∷ "m1's canonical advancement separately records the concrete reference curvature φ1 witness and finite-C4 holonomy laws"
        ∷ "This is not a user-supplied real non-flat Yang-Mills lattice connection"
        ∷ []
    }

record YMSFGCGate3RouteBU2ConsumerStaging : Set₁ where
  field
    gate3NonFlatCurvaturePrimitiveAdvancement :
      YMObs.YMSFGCGate3NonFlatCurvaturePrimitiveAdvancement

    gate3NonFlatCurvaturePrimitiveAdvancementIsCanonical :
      gate3NonFlatCurvaturePrimitiveAdvancement
      ≡
      YMObs.canonicalYMSFGCGate3NonFlatCurvaturePrimitiveAdvancement

    middleM1M2ImplementationProgress :
      YMObs.YMSFGCMiddleM1M2ImplementationProgress

    middleM1M2ImplementationProgressIsCanonical :
      middleM1M2ImplementationProgress
      ≡
      YMObs.canonicalYMSFGCMiddleM1M2ImplementationProgress

    lower6M1M2U2ConsolidatedHandoffReceipt :
      YMObs.YMSFGCLower6M1M2U2ConsolidatedHandoffReceipt

    lower6M1M2U2ConsolidatedHandoffReceiptIsCanonical :
      lower6M1M2U2ConsolidatedHandoffReceipt
      ≡
      YMObs.canonicalYMSFGCLower6M1M2U2ConsolidatedHandoffReceipt

    m1HolonomyTelescopingLawIsFiniteC4 :
      YMObs.YMSFGCGate3NonFlatCurvaturePrimitiveAdvancement.holonomyTelescopingLaw
        gate3NonFlatCurvaturePrimitiveAdvancement
      ≡
      YMObs.sfgcFiniteC4HolonomyTelescopingLaw

    m1HolonomyConjugationLawIsFiniteC4 :
      YMObs.YMSFGCGate3NonFlatCurvaturePrimitiveAdvancement.holonomyConjugationLaw
        gate3NonFlatCurvaturePrimitiveAdvancement
      ≡
      YMObs.sfgcFiniteC4HolonomyConjugationLaw

    u2ConnectionOneFormAsFibreAlgebraLocalReceipt :
      YMObs.YMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt

    u2ConnectionOneFormAsFibreAlgebraLocalReceiptIsCanonical :
      u2ConnectionOneFormAsFibreAlgebraLocalReceipt
      ≡
      YMObs.canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt

    u2ConnectionOneFormAsFibreAlgebraIsSelectedPhaseMap :
      YMObs.YMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt.connectionOneFormAsFibreAlgebra
        u2ConnectionOneFormAsFibreAlgebraLocalReceipt
      ≡
      YMObs.sfgcSelectedConnectionOneFormAsLocalFiniteLie3

    u2LocalFiniteLieValuedFormsAndCurvature :
      YMObs.YMSFGCLocalFiniteLieValuedFormsAndCurvature

    u2LocalFiniteLieValuedFormsAndCurvatureIsCanonical :
      u2LocalFiniteLieValuedFormsAndCurvature
      ≡
      YMObs.canonicalYMSFGCLocalFiniteLieValuedFormsAndCurvature

    u2CovariantDerivativeSquareLawIsCanonical :
      Bool

    u2NonFlatLatticeConnectionPrimitiveSupply :
      YMObs.YMSFGCUserSuppliedNonFlatLatticeConnectionPrimitiveSupply

    u2NonFlatLatticeConnectionPrimitiveSupplyIsCanonical :
      u2NonFlatLatticeConnectionPrimitiveSupply
      ≡
      canonicalRouteBU2NonFlatLatticeConnectionPrimitiveSupply

    routeBSelectedDiscreteHodgeCovariantDerivativeSupply :
      YMObs.YMSFGCDiscreteHodgeCovariantDerivativePrimitiveSupply

    routeBSelectedDiscreteHodgeCovariantDerivativeSupplyIsCanonical :
      routeBSelectedDiscreteHodgeCovariantDerivativeSupply
      ≡
      canonicalRouteBSelectedDiscreteHodgeCovariantDerivativeSupply

    routeBZeroDiscreteVariationIBPPrimitiveSupply :
      YMObs.YMSFGCDiscreteVariationIBPPrimitiveSupply

    routeBZeroDiscreteVariationIBPPrimitiveSupplyIsCanonical :
      routeBZeroDiscreteVariationIBPPrimitiveSupply
      ≡
      canonicalRouteBZeroDiscreteVariationIBPPrimitiveSupply

    firstStrictNonFlatHolonomyBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictNonFlatHolonomyBlockerIsCurvature :
      firstStrictNonFlatHolonomyBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    firstStrictRouteBBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    firstStrictRouteBBlockerIsVariationPairing :
      firstStrictRouteBBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    consumerPromoted :
      Bool

    consumerPromotedIsFalse :
      consumerPromoted ≡ false

    stagingBoundary :
      List String

canonicalYMSFGCGate3RouteBU2ConsumerStaging :
  YMSFGCGate3RouteBU2ConsumerStaging
canonicalYMSFGCGate3RouteBU2ConsumerStaging =
  record
    { gate3NonFlatCurvaturePrimitiveAdvancement =
        YMObs.canonicalYMSFGCGate3NonFlatCurvaturePrimitiveAdvancement
    ; gate3NonFlatCurvaturePrimitiveAdvancementIsCanonical =
        refl
    ; middleM1M2ImplementationProgress =
        YMObs.canonicalYMSFGCMiddleM1M2ImplementationProgress
    ; middleM1M2ImplementationProgressIsCanonical =
        refl
    ; lower6M1M2U2ConsolidatedHandoffReceipt =
        YMObs.canonicalYMSFGCLower6M1M2U2ConsolidatedHandoffReceipt
    ; lower6M1M2U2ConsolidatedHandoffReceiptIsCanonical =
        refl
    ; m1HolonomyTelescopingLawIsFiniteC4 =
        refl
    ; m1HolonomyConjugationLawIsFiniteC4 =
        refl
    ; u2ConnectionOneFormAsFibreAlgebraLocalReceipt =
        YMObs.canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt
    ; u2ConnectionOneFormAsFibreAlgebraLocalReceiptIsCanonical =
        refl
    ; u2ConnectionOneFormAsFibreAlgebraIsSelectedPhaseMap =
        refl
    ; u2LocalFiniteLieValuedFormsAndCurvature =
        YMObs.canonicalYMSFGCLocalFiniteLieValuedFormsAndCurvature
    ; u2LocalFiniteLieValuedFormsAndCurvatureIsCanonical =
        refl
    ; u2CovariantDerivativeSquareLawIsCanonical =
        true
    ; u2NonFlatLatticeConnectionPrimitiveSupply =
        canonicalRouteBU2NonFlatLatticeConnectionPrimitiveSupply
    ; u2NonFlatLatticeConnectionPrimitiveSupplyIsCanonical =
        refl
    ; routeBSelectedDiscreteHodgeCovariantDerivativeSupply =
        canonicalRouteBSelectedDiscreteHodgeCovariantDerivativeSupply
    ; routeBSelectedDiscreteHodgeCovariantDerivativeSupplyIsCanonical =
        refl
    ; routeBZeroDiscreteVariationIBPPrimitiveSupply =
        canonicalRouteBZeroDiscreteVariationIBPPrimitiveSupply
    ; routeBZeroDiscreteVariationIBPPrimitiveSupplyIsCanonical =
        refl
    ; firstStrictNonFlatHolonomyBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; firstStrictNonFlatHolonomyBlockerIsCurvature =
        refl
    ; firstStrictRouteBBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; firstStrictRouteBBlockerIsVariationPairing =
        refl
    ; consumerPromoted =
        false
    ; consumerPromotedIsFalse =
        refl
    ; stagingBoundary =
        "Consumes m1 canonicalYMSFGCGate3NonFlatCurvaturePrimitiveAdvancement and the canonical gate3NonFlatCurvaturePrimitiveAdvancement field"
        ∷ "Rebases Route B lower Hodge/current onto SFGCSite2DFieldStrengthBridge using the selected identity Hodge probe and selected current source"
        ∷ "Stages YMSFGCDiscreteVariationIBPPrimitiveSupply only as a zero Boolean primitive supply; no variation pairing is supplied"
        ∷ "Stages u2 connectionOneFormAsFibreAlgebra, local Lie-valued D_A^2 = [F_A,_], finite-C4 holonomy telescoping/conjugation, and a receipt-local non-flat lattice supply shape"
        ∷ "Strict blockers remain non-flat curvature/holonomy promotion and missingVariationPairingForSelectedHodgeStar"
        ∷ []
    }

record YMSFGCRouteBLowerHodgeCurrentSurface : Set₁ where
  field
    lowerDiscreteHodgeCovariantDerivativeSupply :
      YMObs.YMSFGCDiscreteHodgeCovariantDerivativePrimitiveSupply

    lowerDiscreteHodgeCovariantDerivativeSupplyIsCanonical :
      lowerDiscreteHodgeCovariantDerivativeSupply
      ≡
      canonicalRouteBLowerDiscreteHodgeCovariantDerivativeSupply

    lowerCovariantDerivativeOnDualCurvature :
      SFGC.GaugeField →
      Bool →
      Bool

    lowerCovariantDerivativeOnDualCurvatureIsCanonical :
      lowerCovariantDerivativeOnDualCurvature
      ≡
      routeBLowerCovariantDerivativeOnDualCurvature

    lowerCurrentSource :
      SFGC.GaugeField →
      Bool

    lowerCurrentSourceIsCanonical :
      lowerCurrentSource
      ≡
      routeBLowerCurrentSource

    lowerDStarFEqualsJLaw :
      (A : SFGC.GaugeField) →
      routeBLowerCovariantDerivativeOnDualCurvature
        A
        (routeBLowerHodgeStar
          (SFGC.sfgcSite2DFieldStrengthFromCurvature
            (SFGC.sfgcSite2Dδ₁
              (SFGC.sfgcSite2DConnectionTo1Form A))))
      ≡
      routeBLowerCurrentSource A

    lowerDStarFEqualsJLawIsCanonical :
      lowerDStarFEqualsJLaw
      ≡
      routeBLowerDStarFEqualsJLaw

    discreteVariationIBPSurface :
      YMObs.YMSFGCDiscreteVariationIBPLowerCandidate

    discreteVariationIBPSurfaceIsCanonical :
      discreteVariationIBPSurface
      ≡
      YMObs.canonicalYMSFGCDiscreteVariationIBPLowerCandidate

    selectedDiscreteHodgeCovariantDerivativeSupply :
      YMObs.YMSFGCDiscreteHodgeCovariantDerivativePrimitiveSupply

    selectedDiscreteHodgeCovariantDerivativeSupplyIsCanonical :
      selectedDiscreteHodgeCovariantDerivativeSupply
      ≡
      canonicalRouteBSelectedDiscreteHodgeCovariantDerivativeSupply

    zeroDiscreteVariationIBPPrimitiveSupply :
      YMObs.YMSFGCDiscreteVariationIBPPrimitiveSupply

    zeroDiscreteVariationIBPPrimitiveSupplyIsCanonical :
      zeroDiscreteVariationIBPPrimitiveSupply
      ≡
      canonicalRouteBZeroDiscreteVariationIBPPrimitiveSupply

    firstStrictRouteBMissingPrimitive :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    firstStrictRouteBMissingPrimitiveIsVariationPairing :
      firstStrictRouteBMissingPrimitive
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    sourcedDStarFEqualsJBlocker :
      YMObs.YMSFGCSourcedDStarFEqualsJBlocker

    sourcedDStarFEqualsJBlockerIsCanonical :
      sourcedDStarFEqualsJBlocker
      ≡
      YMObs.canonicalYMSFGCSourcedDStarFEqualsJBlocker

    routeBLowerPromoted :
      Bool

    routeBLowerPromotedIsFalse :
      routeBLowerPromoted ≡ false

    surfaceBoundary :
      List String

canonicalYMSFGCRouteBLowerHodgeCurrentSurface :
  YMSFGCRouteBLowerHodgeCurrentSurface
canonicalYMSFGCRouteBLowerHodgeCurrentSurface =
  record
    { lowerDiscreteHodgeCovariantDerivativeSupply =
        canonicalRouteBLowerDiscreteHodgeCovariantDerivativeSupply
    ; lowerDiscreteHodgeCovariantDerivativeSupplyIsCanonical =
        refl
    ; lowerCovariantDerivativeOnDualCurvature =
        routeBLowerCovariantDerivativeOnDualCurvature
    ; lowerCovariantDerivativeOnDualCurvatureIsCanonical =
        refl
    ; lowerCurrentSource =
        routeBLowerCurrentSource
    ; lowerCurrentSourceIsCanonical =
        refl
    ; lowerDStarFEqualsJLaw =
        routeBLowerDStarFEqualsJLaw
    ; lowerDStarFEqualsJLawIsCanonical =
        refl
    ; discreteVariationIBPSurface =
        YMObs.canonicalYMSFGCDiscreteVariationIBPLowerCandidate
    ; discreteVariationIBPSurfaceIsCanonical =
        refl
    ; selectedDiscreteHodgeCovariantDerivativeSupply =
        canonicalRouteBSelectedDiscreteHodgeCovariantDerivativeSupply
    ; selectedDiscreteHodgeCovariantDerivativeSupplyIsCanonical =
        refl
    ; zeroDiscreteVariationIBPPrimitiveSupply =
        canonicalRouteBZeroDiscreteVariationIBPPrimitiveSupply
    ; zeroDiscreteVariationIBPPrimitiveSupplyIsCanonical =
        refl
    ; firstStrictRouteBMissingPrimitive =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; firstStrictRouteBMissingPrimitiveIsVariationPairing =
        refl
    ; sourcedDStarFEqualsJBlocker =
        YMObs.canonicalYMSFGCSourcedDStarFEqualsJBlocker
    ; sourcedDStarFEqualsJBlockerIsCanonical =
        refl
    ; routeBLowerPromoted =
        false
    ; routeBLowerPromotedIsFalse =
        refl
    ; surfaceBoundary =
        "Route B lower Hodge/current target now has concrete Bool-valued covariantDerivativeOnDualCurvature, currentSource, and dStarFEqualsJLaw symbols"
        ∷ "Route B selected-field-strength target now also has hodgeStar, covariantDerivativeOnDualCurvature, currentSource, and dStarFEqualsJLaw rebased onto the m1/m2 selected identity Hodge probe"
        ∷ "YMSFGCDiscreteVariationIBPPrimitiveSupply is staged only as a zero Boolean primitive supply"
        ∷ "The attached discrete variation/IBP surface is only the canonical zero-variation lower candidate"
        ∷ "The first strict Route B blocker remains missingVariationPairingForSelectedHodgeStar"
        ∷ "This surface does not discharge m1 curvature, non-flat holonomy, real Hodge star, source coupling, or Yang-Mills promotion"
        ∷ []
    }

data YMSFGCM1FiniteCarrierGapStagingStatus : Set where
  m1FiniteCarrierGapStagedNoContinuumPromotion :
    YMSFGCM1FiniteCarrierGapStagingStatus

data YMSFGCM1FiniteCarrierHardExternalHalt : Set where
  uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient :
    YMSFGCM1FiniteCarrierHardExternalHalt

record YMSFGCM1FiniteCarrierGapStagingReceipt : Set₁ where
  field
    status :
      YMSFGCM1FiniteCarrierGapStagingStatus

    m1FiniteHolonomyMathReceipt :
      YMObs.YMSFGCGate3Wave2FiniteHolonomyMathReceipt

    m1FiniteHolonomyMathReceiptIsCanonical :
      m1FiniteHolonomyMathReceipt
      ≡
      YMObs.canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt

    m1StrictPromotionDecision :
      YMObs.YMSFGCGate3Wave3StrictPromotionDecisionReceipt

    m1StrictPromotionDecisionIsCanonical :
      m1StrictPromotionDecision
      ≡
      YMObs.canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt

    finiteLieAlgebraSupply :
      YMObs.YMSFGCNonAbelianCovariantDerivativePrimitiveSupply

    finiteLieAlgebraSupplyIsLocalFiniteLie3 :
      finiteLieAlgebraSupply
      ≡
      YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply

    finiteTraceAdInvarianceSupply :
      YMObs.YMSFGCLieAlgebraTraceAdInvariancePrimitiveSupply

    finiteTraceAdInvarianceSupplyIsFiniteC4 :
      finiteTraceAdInvarianceSupply
      ≡
      YMObs.canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply

    casimirStyleFiniteCarrier :
      Set

    casimirStyleFiniteCarrierIsLocalFiniteLie3 :
      casimirStyleFiniteCarrier
      ≡
      YMObs.YMSFGCLocalFiniteLie3Carrier

    casimirStyleFiniteCarrierGapStaged :
      Bool

    casimirStyleFiniteCarrierGapStagedIsTrue :
      casimirStyleFiniteCarrierGapStaged ≡ true

    firstStrictNonFlatCurvatureBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictNonFlatCurvatureBlockerIsCanonical :
      firstStrictNonFlatCurvatureBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    firstStrictSelectedGaugeSectorBlocker :
      YMObs.YMSFGCRealKillingAdInvarianceIrreducibility

    firstStrictSelectedGaugeSectorBlockerIsCanonical :
      firstStrictSelectedGaugeSectorBlocker
      ≡
      YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    firstStrictVariationPairingBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    firstStrictVariationPairingBlockerIsCanonical :
      firstStrictVariationPairingBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    realCarrierHalt :
      YMSFGCM1FiniteCarrierHardExternalHalt

    realCarrierHaltIsUniformBalabanOrAgawa :
      realCarrierHalt
      ≡
      uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    selfAdjointHamiltonianConstructed :
      Bool

    selfAdjointHamiltonianConstructedIsFalse :
      selfAdjointHamiltonianConstructed ≡ false

    continuumMassGapPromoted :
      Bool

    continuumMassGapPromotedIsFalse :
      continuumMassGapPromoted ≡ false

    stagingBoundary :
      List String

canonicalYMSFGCM1FiniteCarrierGapStagingReceipt :
  YMSFGCM1FiniteCarrierGapStagingReceipt
canonicalYMSFGCM1FiniteCarrierGapStagingReceipt =
  record
    { status =
        m1FiniteCarrierGapStagedNoContinuumPromotion
    ; m1FiniteHolonomyMathReceipt =
        YMObs.canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt
    ; m1FiniteHolonomyMathReceiptIsCanonical =
        refl
    ; m1StrictPromotionDecision =
        YMObs.canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt
    ; m1StrictPromotionDecisionIsCanonical =
        refl
    ; finiteLieAlgebraSupply =
        YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
    ; finiteLieAlgebraSupplyIsLocalFiniteLie3 =
        refl
    ; finiteTraceAdInvarianceSupply =
        YMObs.canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply
    ; finiteTraceAdInvarianceSupplyIsFiniteC4 =
        refl
    ; casimirStyleFiniteCarrier =
        YMObs.YMSFGCLocalFiniteLie3Carrier
    ; casimirStyleFiniteCarrierIsLocalFiniteLie3 =
        refl
    ; casimirStyleFiniteCarrierGapStaged =
        true
    ; casimirStyleFiniteCarrierGapStagedIsTrue =
        refl
    ; firstStrictNonFlatCurvatureBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; firstStrictNonFlatCurvatureBlockerIsCanonical =
        refl
    ; firstStrictSelectedGaugeSectorBlocker =
        YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; firstStrictSelectedGaugeSectorBlockerIsCanonical =
        refl
    ; firstStrictVariationPairingBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; firstStrictVariationPairingBlockerIsCanonical =
        refl
    ; realCarrierHalt =
        uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; realCarrierHaltIsUniformBalabanOrAgawa =
        refl
    ; selfAdjointHamiltonianConstructed =
        false
    ; selfAdjointHamiltonianConstructedIsFalse =
        refl
    ; continuumMassGapPromoted =
        false
    ; continuumMassGapPromotedIsFalse =
        refl
    ; stagingBoundary =
        "m1 finite carrier gap staging consumes the local finite Lie3 bracket/Jacobi supply and finite-C4 trace/Ad-invariance supply"
        ∷ "The Casimir-style carrier is only the local finite Lie3 carrier; no continuum Hamiltonian or spectral theorem is constructed"
        ∷ "The receipt is attached to the existing Wave 3 strict-promotion decision; the Site2D connection adapter exists, while holonomy, Lie, and dual-curvature bridges remain absent"
        ∷ "Remaining blockers stay missingNonFlatSFGCSite2DConnectionCurvature, missingLieAlgebraCarrierForSelectedFiniteGaugeSector, missingVariationPairingForSelectedHodgeStar, and UniformBalaban-or-AgawaIRFixedPoint"
        ∷ []
    }

data YMSFGCGate3M1U2M2WorkerReceiptStatus : Set where
  gate3M1U2M2WorkerReceiptFailClosedNoPromotion :
    YMSFGCGate3M1U2M2WorkerReceiptStatus

record YMSFGCGate3M1U2M2WorkerReceipt : Set₁ where
  field
    status :
      YMSFGCGate3M1U2M2WorkerReceiptStatus

    obstructionFinalReceipt :
      YMObs.YMSFGCGate3M1U2M2WorkerFinalReceipt

    obstructionFinalReceiptIsCanonical :
      obstructionFinalReceipt
      ≡
      YMObs.canonicalYMSFGCGate3M1U2M2WorkerFinalReceipt

    routeBU2ConsumerStaging :
      YMSFGCGate3RouteBU2ConsumerStaging

    routeBU2ConsumerStagingIsCanonical :
      routeBU2ConsumerStaging
      ≡
      canonicalYMSFGCGate3RouteBU2ConsumerStaging

    routeBLowerHodgeCurrentSurface :
      YMSFGCRouteBLowerHodgeCurrentSurface

    routeBLowerHodgeCurrentSurfaceIsCanonical :
      routeBLowerHodgeCurrentSurface
      ≡
      canonicalYMSFGCRouteBLowerHodgeCurrentSurface

    middle6DiscreteIBPVariationPairingProgress :
      YMObs.YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt

    middle6DiscreteIBPVariationPairingProgressIsCanonical :
      middle6DiscreteIBPVariationPairingProgress
      ≡
      YMObs.canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt

    m1FiniteCarrierGapStagingReceipt :
      YMSFGCM1FiniteCarrierGapStagingReceipt

    m1FiniteCarrierGapStagingReceiptIsCanonical :
      m1FiniteCarrierGapStagingReceipt
      ≡
      canonicalYMSFGCM1FiniteCarrierGapStagingReceipt

    m1ExactBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    m1ExactBlockerIsNonFlatCurvature :
      m1ExactBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    u2ExactTransportBlocker :
      YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    u2ExactTransportBlockerIsFieldStrengthAction :
      u2ExactTransportBlocker
      ≡
      YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    m2ExactBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    m2ExactBlockerIsVariationPairing :
      m2ExactBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    routeBSelectedDStarLawIsLowerDefinitional :
      (A : SFGC.GaugeField) →
      routeBSelectedCovariantDerivativeOnDualCurvature
        A
        (routeBSelectedHodgeStar
          (SFGC.sfgcSite2DFieldStrengthFromCurvature
            (SFGC.sfgcSite2Dδ₁
              (SFGC.sfgcSite2DConnectionTo1Form A))))
      ≡
      routeBSelectedCurrentSource A

    receiptPromoted :
      Bool

    receiptPromotedIsFalse :
      receiptPromoted ≡ false

    receiptBoundary :
      List String

canonicalYMSFGCGate3M1U2M2WorkerReceipt :
  YMSFGCGate3M1U2M2WorkerReceipt
canonicalYMSFGCGate3M1U2M2WorkerReceipt =
  record
    { status =
        gate3M1U2M2WorkerReceiptFailClosedNoPromotion
    ; obstructionFinalReceipt =
        YMObs.canonicalYMSFGCGate3M1U2M2WorkerFinalReceipt
    ; obstructionFinalReceiptIsCanonical =
        refl
    ; routeBU2ConsumerStaging =
        canonicalYMSFGCGate3RouteBU2ConsumerStaging
    ; routeBU2ConsumerStagingIsCanonical =
        refl
    ; routeBLowerHodgeCurrentSurface =
        canonicalYMSFGCRouteBLowerHodgeCurrentSurface
    ; routeBLowerHodgeCurrentSurfaceIsCanonical =
        refl
    ; middle6DiscreteIBPVariationPairingProgress =
        YMObs.canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt
    ; middle6DiscreteIBPVariationPairingProgressIsCanonical =
        refl
    ; m1FiniteCarrierGapStagingReceipt =
        canonicalYMSFGCM1FiniteCarrierGapStagingReceipt
    ; m1FiniteCarrierGapStagingReceiptIsCanonical =
        refl
    ; m1ExactBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; m1ExactBlockerIsNonFlatCurvature =
        refl
    ; u2ExactTransportBlocker =
        YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; u2ExactTransportBlockerIsFieldStrengthAction =
        refl
    ; m2ExactBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; m2ExactBlockerIsVariationPairing =
        refl
    ; routeBSelectedDStarLawIsLowerDefinitional =
        routeBSelectedDStarFEqualsJLaw
    ; receiptPromoted =
        false
    ; receiptPromotedIsFalse =
        refl
    ; receiptBoundary =
        "m1/u2/m2 final worker receipt consumes the obstruction-side final receipt, Route B u2 consumer staging, lower Hodge/current surface, and m1 finite-carrier staging"
        ∷ "Route B selected D * F = J is recorded only as the existing definitional lower identity-current law on SFGCSite2DFieldStrengthBridge"
        ∷ "Middle6 discrete IBP progress is recorded as the finite zero-variation IBP law; strict variation pairing remains uninhabited"
        ∷ "Strict m1 remains blocked at missingNonFlatSFGCSite2DConnectionCurvature"
        ∷ "Strict u2 remains blocked at missingFieldStrengthTransportActionOnSelectedGaugeBundle"
        ∷ "Strict m2 remains blocked at missingVariationPairingForSelectedHodgeStar"
        ∷ "No Yang-Mills, Maxwell, spectral-gap, mass-gap, Clay, or terminal promotion is asserted"
        ∷ []
    }

data YMSFGCGate3FirstMissingPrimitiveWorkerReceiptStatus : Set where
  gate3FirstMissingPrimitiveWorkerFailClosedNoPromotion :
    YMSFGCGate3FirstMissingPrimitiveWorkerReceiptStatus

record YMSFGCGate3FirstMissingPrimitiveWorkerReceipt : Set₁ where
  field
    status :
      YMSFGCGate3FirstMissingPrimitiveWorkerReceiptStatus

    obstructionProgressReceipt :
      YMObs.YMSFGCGate3FirstMissingPrimitiveProgressReceipt

    obstructionProgressReceiptIsCanonical :
      obstructionProgressReceipt
      ≡
      YMObs.canonicalYMSFGCGate3FirstMissingPrimitiveProgressReceipt

    workerReceipt :
      YMSFGCGate3M1U2M2WorkerReceipt

    workerReceiptIsCanonical :
      workerReceipt
      ≡
      canonicalYMSFGCGate3M1U2M2WorkerReceipt

    finiteSU3LikeCarrierShape :
      Set

    finiteSU3LikeCarrierShapeIsObstructionShape :
      finiteSU3LikeCarrierShape
      ≡
      YMObs.YMSFGCLocalFiniteSU3Carrier

    connectionOneFormAsFibreAlgebraPreStage :
      SFGC.GaugeField →
      YMObs.YMSFGCLocalFiniteLie3Carrier

    connectionOneFormAsFibreAlgebraPreStageIsSelected :
      connectionOneFormAsFibreAlgebraPreStage
      ≡
      YMObs.sfgcSelectedConnectionOneFormAsLocalFiniteLie3

    selectedHodgeFiniteShape :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    selectedHodgeFiniteShapeIsIdentityProbe :
      selectedHodgeFiniteShape
      ≡
      YMObs.sfgcSelectedHodgeStarLowerCandidate

    exactNonFlatCurvatureBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    exactNonFlatCurvatureBlockerIsMissingNonFlatSFGCSite2DConnectionCurvature :
      exactNonFlatCurvatureBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    exactSelectedGaugeSectorBlocker :
      YMObs.YMSFGCRealKillingAdInvarianceIrreducibility

    exactSelectedGaugeSectorBlockerIsMissingLieAlgebraCarrier :
      exactSelectedGaugeSectorBlocker
      ≡
      YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    exactVariationPairingBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    exactVariationPairingBlockerIsMissingVariationPairing :
      exactVariationPairingBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    receiptPromoted :
      Bool

    receiptPromotedIsFalse :
      receiptPromoted ≡ false

    receiptBoundary :
      List String

canonicalYMSFGCGate3FirstMissingPrimitiveWorkerReceipt :
  YMSFGCGate3FirstMissingPrimitiveWorkerReceipt
canonicalYMSFGCGate3FirstMissingPrimitiveWorkerReceipt =
  record
    { status =
        gate3FirstMissingPrimitiveWorkerFailClosedNoPromotion
    ; obstructionProgressReceipt =
        YMObs.canonicalYMSFGCGate3FirstMissingPrimitiveProgressReceipt
    ; obstructionProgressReceiptIsCanonical =
        refl
    ; workerReceipt =
        canonicalYMSFGCGate3M1U2M2WorkerReceipt
    ; workerReceiptIsCanonical =
        refl
    ; finiteSU3LikeCarrierShape =
        YMObs.YMSFGCLocalFiniteSU3Carrier
    ; finiteSU3LikeCarrierShapeIsObstructionShape =
        refl
    ; connectionOneFormAsFibreAlgebraPreStage =
        YMObs.sfgcSelectedConnectionOneFormAsLocalFiniteLie3
    ; connectionOneFormAsFibreAlgebraPreStageIsSelected =
        refl
    ; selectedHodgeFiniteShape =
        YMObs.sfgcSelectedHodgeStarLowerCandidate
    ; selectedHodgeFiniteShapeIsIdentityProbe =
        refl
    ; exactNonFlatCurvatureBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; exactNonFlatCurvatureBlockerIsMissingNonFlatSFGCSite2DConnectionCurvature =
        refl
    ; exactSelectedGaugeSectorBlocker =
        YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; exactSelectedGaugeSectorBlockerIsMissingLieAlgebraCarrier =
        refl
    ; exactVariationPairingBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; exactVariationPairingBlockerIsMissingVariationPairing =
        refl
    ; receiptPromoted =
        false
    ; receiptPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Gate 3 first-missing worker receipt consumes the obstruction progress receipt for finite SU3-like, local connection-one-form, D_A pre-stage, and Hodge arithmetic shapes"
        ∷ "The finite shapes are not promoted beyond the Site2D connection adapter into the remaining user-supplied Yang-Mills carriers"
        ∷ "Exact fail-closed blockers are missingNonFlatSFGCSite2DConnectionCurvature, missingLieAlgebraCarrierForSelectedFiniteGaugeSector, and missingVariationPairingForSelectedHodgeStar"
        ∷ "No mass-gap, Clay, spectral-gap, Yang-Mills field-equation, or terminal promotion claim is introduced"
        ∷ []
    }

record YMSFGCGate3ConcreteYMModuleWireupReceipt : Set₁ where
  field
    su2LieAlgebraModule :
      YM_SU2.SU2LieAlgebra

    su2LieAlgebraModuleIsCanonical :
      su2LieAlgebraModule
      ≡
      YM_SU2.canonicalSU2LieAlgebra

    covariantDerivativeModule :
      YM_CD.GaugeField →
      YM_CD.AdjSection →
      YM_CD.LatticeEdge →
      YM_CD.AdjElement

    covariantDerivativeModuleIsCanonical :
      covariantDerivativeModule
      ≡
      YM_CD.D_A

    fieldStrengthModule :
      YM_FS.GaugeField →
      YM_FS.LatticeEdge →
      YM_FS.LatticeEdge →
      YM_FS.AdjElement

    fieldStrengthModuleIsCanonical :
      fieldStrengthModule
      ≡
      YM_FS.F_A

    yangMillsActionModule :
      YM_YM.GaugeField →
      ℤ

    yangMillsActionModuleIsCanonical :
      yangMillsActionModule
      ≡
      YM_YM.ymAction

    exactNonFlatCurvatureBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    exactNonFlatCurvatureBlockerIsOpen :
      exactNonFlatCurvatureBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    exactStrictLieCarrierBlocker :
      YMObs.YMSFGCRealKillingAdInvarianceIrreducibility

    exactStrictLieCarrierBlockerIsOpen :
      exactStrictLieCarrierBlocker
      ≡
      YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    exactStrictTransportBlocker :
      YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    exactStrictTransportBlockerIsOpen :
      exactStrictTransportBlocker
      ≡
      YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    exactStrictVariationBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    exactStrictVariationBlockerIsOpen :
      exactStrictVariationBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    strictPromotion :
      Bool

    strictPromotionIsFalse :
      strictPromotion ≡ false

    receiptBoundary :
      List String

canonicalYMSFGCGate3ConcreteYMModuleWireupReceipt :
  YMSFGCGate3ConcreteYMModuleWireupReceipt
canonicalYMSFGCGate3ConcreteYMModuleWireupReceipt =
  record
    { su2LieAlgebraModule =
        YM_SU2.canonicalSU2LieAlgebra
    ; su2LieAlgebraModuleIsCanonical =
        refl
    ; covariantDerivativeModule =
        YM_CD.D_A
    ; covariantDerivativeModuleIsCanonical =
        refl
    ; fieldStrengthModule =
        YM_FS.F_A
    ; fieldStrengthModuleIsCanonical =
        refl
    ; yangMillsActionModule =
        YM_YM.ymAction
    ; yangMillsActionModuleIsCanonical =
        refl
    ; exactNonFlatCurvatureBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; exactNonFlatCurvatureBlockerIsOpen =
        refl
    ; exactStrictLieCarrierBlocker =
        YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; exactStrictLieCarrierBlockerIsOpen =
        refl
    ; exactStrictTransportBlocker =
        YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; exactStrictTransportBlockerIsOpen =
        refl
    ; exactStrictVariationBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; exactStrictVariationBlockerIsOpen =
        refl
    ; strictPromotion =
        false
    ; strictPromotionIsFalse =
        refl
    ; receiptBoundary =
        "Gate 3 receipt wireup is concrete for canonicalSU2LieAlgebra, D_A, F_A, and ymAction"
        ∷ "The strict non-flat, Lie-carrier, field-strength transport, and variation-pairing blockers remain exact and open"
        ∷ []
    }

yangMillsGate3FirstMissingPrimitiveWorkerReceiptIsNonPromoting :
  YMSFGCGate3FirstMissingPrimitiveWorkerReceipt.receiptPromoted
    canonicalYMSFGCGate3FirstMissingPrimitiveWorkerReceipt
  ≡
  false
yangMillsGate3FirstMissingPrimitiveWorkerReceiptIsNonPromoting =
  refl

yangMillsGate3FirstMissingPrimitiveWorkerReceiptNonFlatBlockerIsExact :
  YMSFGCGate3FirstMissingPrimitiveWorkerReceipt.exactNonFlatCurvatureBlocker
    canonicalYMSFGCGate3FirstMissingPrimitiveWorkerReceipt
  ≡
  YMObs.missingNonFlatSFGCSite2DConnectionCurvature
yangMillsGate3FirstMissingPrimitiveWorkerReceiptNonFlatBlockerIsExact =
  refl

yangMillsGate3FirstMissingPrimitiveWorkerReceiptGaugeSectorBlockerIsExact :
  YMSFGCGate3FirstMissingPrimitiveWorkerReceipt.exactSelectedGaugeSectorBlocker
    canonicalYMSFGCGate3FirstMissingPrimitiveWorkerReceipt
  ≡
  YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
yangMillsGate3FirstMissingPrimitiveWorkerReceiptGaugeSectorBlockerIsExact =
  refl

yangMillsGate3FirstMissingPrimitiveWorkerReceiptVariationBlockerIsExact :
  YMSFGCGate3FirstMissingPrimitiveWorkerReceipt.exactVariationPairingBlocker
    canonicalYMSFGCGate3FirstMissingPrimitiveWorkerReceipt
  ≡
  YMObs.missingVariationPairingForSelectedHodgeStar
yangMillsGate3FirstMissingPrimitiveWorkerReceiptVariationBlockerIsExact =
  refl

data YMSFGCGate3GenuineFirstMissingNextIterationReceiptStatus : Set where
  gate3GenuineFirstMissingNextIterationConsumedFailClosed :
    YMSFGCGate3GenuineFirstMissingNextIterationReceiptStatus

record YMSFGCGate3GenuineFirstMissingNextIterationReceipt : Set₁ where
  field
    status :
      YMSFGCGate3GenuineFirstMissingNextIterationReceiptStatus

    workerReceipt :
      YMSFGCGate3FirstMissingPrimitiveWorkerReceipt

    workerReceiptIsCanonical :
      workerReceipt
      ≡
      canonicalYMSFGCGate3FirstMissingPrimitiveWorkerReceipt

    obstructionNextIterationResiduals :
      YMObs.YMSFGCGate3GenuineFirstMissingNextIterationTypedResidualReceipt

    obstructionNextIterationResidualsAreCanonical :
      obstructionNextIterationResiduals
      ≡
      YMObs.canonicalYMSFGCGate3GenuineFirstMissingNextIterationTypedResidualReceipt

    finiteResiduals :
      YMObs.YMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals

    finiteResidualsAreCanonical :
      finiteResiduals
      ≡
      YMObs.canonicalYMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals

    exactNonFlatCurvatureBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    exactNonFlatCurvatureBlockerIsMissingNonFlatSFGCSite2DConnectionCurvature :
      exactNonFlatCurvatureBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    exactSelectedLieCarrierBlocker :
      YMObs.YMSFGCRealKillingAdInvarianceIrreducibility

    exactSelectedLieCarrierBlockerIsMissingLieAlgebraCarrier :
      exactSelectedLieCarrierBlocker
      ≡
      YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    exactFieldStrengthTransportBlocker :
      YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    exactFieldStrengthTransportBlockerIsMissingTransportAction :
      exactFieldStrengthTransportBlocker
      ≡
      YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    exactVariationPairingBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    exactVariationPairingBlockerIsMissingVariationPairing :
      exactVariationPairingBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    receiptPromoted :
      Bool

    receiptPromotedIsFalse :
      receiptPromoted ≡ false

    receiptBoundary :
      List String

canonicalYMSFGCGate3GenuineFirstMissingNextIterationReceipt :
  YMSFGCGate3GenuineFirstMissingNextIterationReceipt
canonicalYMSFGCGate3GenuineFirstMissingNextIterationReceipt =
  record
    { status =
        gate3GenuineFirstMissingNextIterationConsumedFailClosed
    ; workerReceipt =
        canonicalYMSFGCGate3FirstMissingPrimitiveWorkerReceipt
    ; workerReceiptIsCanonical =
        refl
    ; obstructionNextIterationResiduals =
        YMObs.canonicalYMSFGCGate3GenuineFirstMissingNextIterationTypedResidualReceipt
    ; obstructionNextIterationResidualsAreCanonical =
        refl
    ; finiteResiduals =
        YMObs.canonicalYMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals
    ; finiteResidualsAreCanonical =
        refl
    ; exactNonFlatCurvatureBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; exactNonFlatCurvatureBlockerIsMissingNonFlatSFGCSite2DConnectionCurvature =
        refl
    ; exactSelectedLieCarrierBlocker =
        YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; exactSelectedLieCarrierBlockerIsMissingLieAlgebraCarrier =
        refl
    ; exactFieldStrengthTransportBlocker =
        YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; exactFieldStrengthTransportBlockerIsMissingTransportAction =
        refl
    ; exactVariationPairingBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; exactVariationPairingBlockerIsMissingVariationPairing =
        refl
    ; receiptPromoted =
        false
    ; receiptPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Gate 3 genuine first-missing fail-closed receipt consumes the next-iteration obstruction residuals"
        ∷ "Finite arithmetic is explicit: local cross-product laws, φ1 Wilson-loop nonzero evidence, finite trace/Ad probe, and Hodge epsilon contraction"
        ∷ "The finite evidence is not promoted to a real non-flat connection, selected real Lie carrier, field-strength transport, or variation pairing"
        ∷ "Exact blockers remain non-flat SFGCSite2D connection curvature, selected real Lie carrier, field-strength transport action, and selected Hodge/action variation pairing"
        ∷ []
    }

yangMillsGate3GenuineFirstMissingNextIterationReceiptIsNonPromoting :
  YMSFGCGate3GenuineFirstMissingNextIterationReceipt.receiptPromoted
    canonicalYMSFGCGate3GenuineFirstMissingNextIterationReceipt
  ≡
  false
yangMillsGate3GenuineFirstMissingNextIterationReceiptIsNonPromoting =
  refl

yangMillsGate3GenuineFirstMissingNextIterationReceiptNonFlatBlockerIsExact :
  YMSFGCGate3GenuineFirstMissingNextIterationReceipt.exactNonFlatCurvatureBlocker
    canonicalYMSFGCGate3GenuineFirstMissingNextIterationReceipt
  ≡
  YMObs.missingNonFlatSFGCSite2DConnectionCurvature
yangMillsGate3GenuineFirstMissingNextIterationReceiptNonFlatBlockerIsExact =
  refl

record YangMillsFieldEquationReceipt : Set₂ where
  field
    status :
      YangMillsFieldEquationReceiptStatus

    target :
      YangMillsFieldEquationTarget

    targetIsCanonical :
      target
      ≡
      canonicalYangMillsFieldEquationTarget

    discreteConnectionCandidate :
      DCRT.DiscreteConnectionCandidateFromCRT

    discreteConnectionCandidateIsCanonical :
      discreteConnectionCandidate
      ≡
      DCRT.canonicalDiscreteConnectionCandidateFromCRT

    discreteCurvatureCarrierObligation :
      G2DCC.G2ShiftGaugeDiscreteCurvatureCarrierObligation

    discreteCurvatureCarrierObligationIsCanonical :
      discreteCurvatureCarrierObligation
      ≡
      G2DCC.canonicalSFGCGaugeDiscreteCurvatureCarrierObligation

    upstreamCurvatureAPIObstruction :
      G2DCC.G2SFGCGaugeFieldCurvatureAPIObstruction

    upstreamCurvatureAPIObstructionIsCanonical :
      upstreamCurvatureAPIObstruction
      ≡
      G2DCC.canonicalSFGCGaugeFieldCurvatureAPIObstruction

    upstreamCurvatureAPIFirstMissing :
      G2DCC.G2SFGCGaugeFieldCurvatureAPIGap

    upstreamCurvatureAPIFirstMissingIsGaugeConnection :
      upstreamCurvatureAPIFirstMissing
      ≡
      G2DCC.missingShiftGaugeFieldGaugeConnection

    implementedNondegeneratePlaquetteAPI :
      G2NP.RequiredNondegenerateSFGCPlaquetteAPI
        SFGC.GaugeField

    implementedNondegeneratePlaquetteAPIIsCanonical :
      implementedNondegeneratePlaquetteAPI
      ≡
      YMObs.canonicalYMSFGCNondegeneratePlaquetteAPI

    implementedDiscreteCurvatureCarrier :
      G2DCC.DiscreteCurvatureCarrier SFGC.GaugeField

    implementedDiscreteCurvatureCarrierIsCanonical :
      implementedDiscreteCurvatureCarrier
      ≡
      YMObs.canonicalYMSFGCDiscreteCurvatureCarrier

    su2LieAlgebraModule :
      YM_SU2.SU2LieAlgebra

    su2LieAlgebraModuleIsCanonical :
      su2LieAlgebraModule
      ≡
      YM_SU2.canonicalSU2LieAlgebra

    covariantDerivativeModule :
      YM_CD.GaugeField →
      YM_CD.AdjSection →
      YM_CD.LatticeEdge →
      YM_CD.AdjElement

    covariantDerivativeModuleIsCanonical :
      covariantDerivativeModule
      ≡
      YM_CD.D_A

    fieldStrengthModule :
      YM_FS.GaugeField →
      YM_FS.LatticeEdge →
      YM_FS.LatticeEdge →
      YM_FS.AdjElement

    fieldStrengthModuleIsCanonical :
      fieldStrengthModule
      ≡
      YM_FS.F_A

    yangMillsActionModule :
      YM_YM.GaugeField →
      ℤ

    yangMillsActionModuleIsCanonical :
      yangMillsActionModule
      ≡
      YM_YM.ymAction

    discreteBianchiReceipt :
      Bianchi.DiscreteBianchiIdentityReceipt

    discreteBianchiReceiptIsCanonical :
      discreteBianchiReceipt
      ≡
      Bianchi.canonicalDiscreteBianchiIdentityReceipt

    fieldEquationObstruction :
      YMObs.YangMillsFieldEquationObstruction

    fieldEquationObstructionIsCanonical :
      fieldEquationObstruction
      ≡
      YMObs.canonicalYangMillsFieldEquationObstruction

    covariantHodgeCurrentPackageRequest :
      YMObs.YMSFGCCovariantHodgeCurrentPackageRequest

    covariantHodgeCurrentPackageRequestIsCanonical :
      covariantHodgeCurrentPackageRequest
      ≡
      YMObs.canonicalYMSFGCCovariantHodgeCurrentPackageRequest

    selectedOperatorSkeleton :
      YMObs.YMSFGCSelectedOperatorSkeleton

    selectedOperatorSkeletonIsCanonical :
      selectedOperatorSkeleton
      ≡
      YMObs.canonicalYMSFGCSelectedOperatorSkeleton

    primitiveDefinitionCandidateSurface :
      YMObs.YMSFGCPrimitiveDefinitionCandidateSurface

    primitiveDefinitionCandidateSurfaceIsCanonical :
      primitiveDefinitionCandidateSurface
      ≡
      YMObs.canonicalYMSFGCPrimitiveDefinitionCandidateSurface

    lowerPrimitiveCandidateBundle :
      YMObs.YMSFGCLowerPrimitiveCandidateBundle

    lowerPrimitiveCandidateBundleIsCanonical :
      lowerPrimitiveCandidateBundle
      ≡
      YMObs.canonicalYMSFGCLowerPrimitiveCandidateBundle

    suppliedLinkFibreTransportCompilerReceipt :
      YMObs.YMSFGCSuppliedLinkFibreTransportCompilerReceipt

    suppliedLinkFibreTransportCompilerReceiptIsCanonical :
      suppliedLinkFibreTransportCompilerReceipt
      ≡
      YMObs.canonicalYMSFGCSuppliedLinkFibreTransportCompilerReceipt

    primitiveInterfaceRequest :
      YMObs.YMSFGCPrimitiveInterfaceRequest

    primitiveInterfaceRequestIsCanonical :
      primitiveInterfaceRequest
      ≡
      YMObs.canonicalYMSFGCPrimitiveInterfaceRequest

    nonAbelianCovariantDerivativeTheoremThinReceipt :
      YMObs.YMSFGCNonAbelianCovariantDerivativeTheoremThinReceipt

    nonAbelianCovariantDerivativeTheoremThinReceiptIsCanonical :
      nonAbelianCovariantDerivativeTheoremThinReceipt
      ≡
      YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeTheoremThinReceipt

    su3JacobiGlobalCarrierRouteReceipt :
      YMObs.YMSFGCSU3JacobiGlobalCarrierRouteReceipt

    su3JacobiGlobalCarrierRouteReceiptIsCanonical :
      su3JacobiGlobalCarrierRouteReceipt
      ≡
      YMObs.canonicalYMSFGCSU3JacobiGlobalCarrierRouteReceipt

    transportActionVariationAbsenceLedger :
      YMObs.YMSFGCFieldStrengthTransportActionVariationAbsenceLedger

    transportActionVariationAbsenceLedgerIsCanonical :
      transportActionVariationAbsenceLedger
      ≡
      YMObs.canonicalYMSFGCFieldStrengthTransportActionVariationAbsenceLedger

    realYMPrimitiveSupplyRequestPack :
      YMObs.YMSFGCRealYMPrimitiveSupplyRequestPack

    realYMPrimitiveSupplyRequestPackIsCanonical :
      realYMPrimitiveSupplyRequestPack
      ≡
      YMObs.canonicalYMSFGCRealYMPrimitiveSupplyRequestPack

    gate3RouteBU2ConsumerStaging :
      YMSFGCGate3RouteBU2ConsumerStaging

    gate3RouteBU2ConsumerStagingIsCanonical :
      gate3RouteBU2ConsumerStaging
      ≡
      canonicalYMSFGCGate3RouteBU2ConsumerStaging

    gate3Wave2FiniteHolonomyMathReceipt :
      YMObs.YMSFGCGate3Wave2FiniteHolonomyMathReceipt

    gate3Wave2FiniteHolonomyMathReceiptIsCanonical :
      gate3Wave2FiniteHolonomyMathReceipt
      ≡
      YMObs.canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt

    gate3Wave3StrictPromotionDecisionReceipt :
      YMObs.YMSFGCGate3Wave3StrictPromotionDecisionReceipt

    gate3Wave3StrictPromotionDecisionReceiptIsCanonical :
      gate3Wave3StrictPromotionDecisionReceipt
      ≡
      YMObs.canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt

    m1FiniteCarrierGapStagingReceipt :
      YMSFGCM1FiniteCarrierGapStagingReceipt

    m1FiniteCarrierGapStagingReceiptIsCanonical :
      m1FiniteCarrierGapStagingReceipt
      ≡
      canonicalYMSFGCM1FiniteCarrierGapStagingReceipt

    gate3M1U2M2WorkerReceipt :
      YMSFGCGate3M1U2M2WorkerReceipt

    gate3M1U2M2WorkerReceiptIsCanonical :
      gate3M1U2M2WorkerReceipt
      ≡
      canonicalYMSFGCGate3M1U2M2WorkerReceipt

    userSuppliedRealYMPrimitiveTypedRequest :
      YMObs.YMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    userSuppliedRealYMPrimitiveTypedRequestIsCanonical :
      userSuppliedRealYMPrimitiveTypedRequest
      ≡
      YMObs.canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    arbitraryGaugeHolonomyKillingAttempt :
      YMObs.YMSFGCArbitraryGaugeHolonomyKillingAttempt

    arbitraryGaugeHolonomyKillingAttemptIsCanonical :
      arbitraryGaugeHolonomyKillingAttempt
      ≡
      YMObs.canonicalYMSFGCArbitraryGaugeHolonomyKillingAttempt

    bianchiDFEqualsZeroBlocker :
      YMObs.YMSFGCBianchiDFEqualsZeroBlocker

    bianchiDFEqualsZeroBlockerIsCanonical :
      bianchiDFEqualsZeroBlocker
      ≡
      YMObs.canonicalYMSFGCBianchiDFEqualsZeroBlocker

    routeABianchiAndDiscreteHodgeProgress :
      YMObs.YMSFGCBianchiAndDiscreteHodgeRouteAProgress

    routeABianchiAndDiscreteHodgeProgressIsCanonical :
      routeABianchiAndDiscreteHodgeProgress
      ≡
      YMObs.canonicalYMSFGCBianchiAndDiscreteHodgeRouteAProgress

    flatConnectionGaugeCompatibilityOfBianchiWitness :
      YMObs.YMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness

    flatConnectionGaugeCompatibilityOfBianchiWitnessIsCanonical :
      flatConnectionGaugeCompatibilityOfBianchiWitness
      ≡
      YMObs.canonicalYMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness

    flatGaugeCompatibilityDischargedPrimitive :
      YMObs.YangMillsBianchiMissingPrimitive

    flatGaugeCompatibilityDischargedPrimitiveIsGaugeCompatibility :
      flatGaugeCompatibilityDischargedPrimitive
      ≡
      YMObs.missingGaugeCompatibilityOfBianchiLaw

    flatGaugeCompatibilityLocalRemainingBianchiPrimitives :
      List YMObs.YangMillsBianchiMissingPrimitive

    flatGaugeCompatibilityLocalRemainingBianchiPrimitivesExhausted :
      flatGaugeCompatibilityLocalRemainingBianchiPrimitives
      ≡
      []

    nonFlatHolonomyConjugationIrreducibilityLedger :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibilityLedger

    nonFlatHolonomyConjugationIrreducibilityLedgerIsCanonical :
      nonFlatHolonomyConjugationIrreducibilityLedger
      ≡
      YMObs.canonicalYMSFGCNonFlatHolonomyConjugationIrreducibilityLedger

    selectedEndpointGaugeFactorSourceTargetReceipt :
      YMObs.YMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt

    selectedEndpointGaugeFactorSourceTargetReceiptIsCanonical :
      selectedEndpointGaugeFactorSourceTargetReceipt
      ≡
      YMObs.canonicalYMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt

    connectionOneFormAsFibreAlgebraLocalReceipt :
      YMObs.YMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt

    connectionOneFormAsFibreAlgebraLocalReceiptIsCanonical :
      connectionOneFormAsFibreAlgebraLocalReceipt
      ≡
      YMObs.canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt

    firstStrictNonFlatHolonomyMissingPrimitive :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictNonFlatHolonomyMissingPrimitiveIsCurvature :
      firstStrictNonFlatHolonomyMissingPrimitive
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    sourcedDStarFEqualsJBlocker :
      YMObs.YMSFGCSourcedDStarFEqualsJBlocker

    sourcedDStarFEqualsJBlockerIsCanonical :
      sourcedDStarFEqualsJBlocker
      ≡
      YMObs.canonicalYMSFGCSourcedDStarFEqualsJBlocker

    routeBLowerHodgeCurrentSurface :
      YMSFGCRouteBLowerHodgeCurrentSurface

    routeBLowerHodgeCurrentSurfaceIsCanonical :
      routeBLowerHodgeCurrentSurface
      ≡
      canonicalYMSFGCRouteBLowerHodgeCurrentSurface

    middle6DiscreteIBPVariationPairingProgress :
      YMObs.YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt

    middle6DiscreteIBPVariationPairingProgressIsCanonical :
      middle6DiscreteIBPVariationPairingProgress
      ≡
      YMObs.canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt

    middle6VariationPairingFirstMissingDependency :
      YMObs.YMSFGCMiddle6VariationPairingFirstMissingDependency

    middle6VariationPairingFirstMissingDependencyIsSelectedActionPairing :
      middle6VariationPairingFirstMissingDependency
      ≡
      YMObs.missingSelectedActionVariationPairingIntoUserActionScalarCarrier

    finalPrimitiveLowerLawCandidate :
      YMObs.YMSFGCFinalPrimitiveLowerLawCandidate

    finalPrimitiveLowerLawCandidateIsCanonical :
      finalPrimitiveLowerLawCandidate
      ≡
      YMObs.canonicalYMSFGCFinalPrimitiveLowerLawCandidate

    exactCanonicalMissingPrimitiveSummary :
      YMObs.YMSFGCExactCanonicalMissingPrimitiveSummary

    exactCanonicalMissingPrimitiveSummaryIsCanonical :
      exactCanonicalMissingPrimitiveSummary
      ≡
      YMObs.canonicalYMSFGCExactCanonicalMissingPrimitiveSummary

    typedPathTransportPrimitiveRequest :
      YMObs.SFGCPathTransportPrimitiveTypedRequest

    typedPathTransportPrimitiveRequestIsCanonical :
      typedPathTransportPrimitiveRequest
      ≡
      YMObs.canonicalSFGCPathTransportPrimitiveTypedRequest

    typedCovariantDifferencePrimitiveRequest :
      YMObs.CovariantDifferencePrimitiveTypedRequest
        YMObs.canonicalSFGCPathTransportPrimitiveTypedRequest

    typedCovariantDifferencePrimitiveRequestIsCanonical :
      typedCovariantDifferencePrimitiveRequest
      ≡
      YMObs.canonicalCovariantDifferencePrimitiveTypedRequest

    typedGaugeInvariantQuadraticDensityPrimitiveRequest :
      YMObs.GaugeInvariantQuadraticDensityPrimitiveTypedRequest

    typedGaugeInvariantQuadraticDensityPrimitiveRequestIsCanonical :
      typedGaugeInvariantQuadraticDensityPrimitiveRequest
      ≡
      YMObs.canonicalGaugeInvariantQuadraticDensityPrimitiveTypedRequest

    typedDiscreteYMActionPrimitiveRequest :
      YMObs.DiscreteYMActionPrimitiveTypedRequest
        YMObs.canonicalGaugeInvariantQuadraticDensityPrimitiveTypedRequest

    typedDiscreteYMActionPrimitiveRequestIsCanonical :
      typedDiscreteYMActionPrimitiveRequest
      ≡
      YMObs.canonicalDiscreteYMActionPrimitiveTypedRequest

    typedDiscreteHodgeCovariantDerivativePrimitiveRequest :
      YMObs.DiscreteHodgeCovariantDerivativePrimitiveTypedRequest

    typedDiscreteHodgeCovariantDerivativePrimitiveRequestIsCanonical :
      typedDiscreteHodgeCovariantDerivativePrimitiveRequest
      ≡
      YMObs.canonicalDiscreteHodgeCovariantDerivativePrimitiveTypedRequest

    typedNonAbelianCovariantDerivativePrimitiveRequest :
      YMObs.YMSFGCNonAbelianCovariantDerivativeTypedRequest

    typedNonAbelianCovariantDerivativePrimitiveRequestIsCanonical :
      typedNonAbelianCovariantDerivativePrimitiveRequest
      ≡
      YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest

    selectedFieldStrengthTransportActionCandidate :
      YMObs.YMSFGCSelectedFieldStrengthAdjointTransportCandidate

    selectedFieldStrengthTransportActionCandidateIsCanonical :
      selectedFieldStrengthTransportActionCandidate
      ≡
      YMObs.canonicalYMSFGCSelectedFieldStrengthAdjointTransportCandidate

    covariantDerivativeExtendsSelectedExteriorDerivativeCandidate :
      YMObs.YMSFGCFlatConnectionExteriorExtensionWitness

    covariantDerivativeExtendsSelectedExteriorDerivativeCandidateIsCanonical :
      covariantDerivativeExtendsSelectedExteriorDerivativeCandidate
      ≡
      YMObs.canonicalYMSFGCFlatConnectionExteriorExtensionWitness

    curvatureQuadraticDensityOnPhase4PlaquettesCandidate :
      YMObs.YMSFGCCurvatureQuadraticDensityProxy

    curvatureQuadraticDensityOnPhase4PlaquettesCandidateIsCanonical :
      curvatureQuadraticDensityOnPhase4PlaquettesCandidate
      ≡
      YMObs.canonicalYMSFGCCurvatureQuadraticDensityProxy

    selectedExteriorDerivativeSquaredZeroWitness :
      YMObs.YMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    selectedExteriorDerivativeSquaredZeroWitnessIsCanonical :
      selectedExteriorDerivativeSquaredZeroWitness
      ≡
      YMObs.canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    exactMissingPrerequisites :
      List YMObs.YangMillsFieldEquationMissingPrerequisite

    exactMissingPrerequisitesAreCanonical :
      exactMissingPrerequisites
      ≡
      YMObs.canonicalYangMillsFieldEquationMissingPrerequisites

    bianchiMissingPrimitives :
      List YMObs.YangMillsBianchiMissingPrimitive

    bianchiMissingPrimitivesAreCanonical :
      bianchiMissingPrimitives
      ≡
      YMObs.canonicalYangMillsBianchiMissingPrimitives

    variationalEquationMissingPrimitives :
      List YMObs.YangMillsVariationalEquationMissingPrimitive

    variationalEquationMissingPrimitivesAreCanonical :
      variationalEquationMissingPrimitives
      ≡
      YMObs.canonicalYangMillsVariationalEquationMissingPrimitives

    selectedCovariantDerivativeMissingPrimitives :
      List YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    selectedCovariantDerivativeMissingPrimitivesAreCanonical :
      selectedCovariantDerivativeMissingPrimitives
      ≡
      YMObs.canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives

    selectedFiniteGaugeSectorBridge :
      YMObs.YMSFGCSelectedFiniteGaugeSectorBridge

    selectedFiniteGaugeSectorBridgeIsCanonical :
      selectedFiniteGaugeSectorBridge
      ≡
      YMObs.canonicalYMSFGCSelectedFiniteGaugeSectorBridge

    nonAbelianCovariantDerivativeMissingPrimitives :
      List YMObs.YMSFGCNonAbelianCovariantDerivativeMissingPrimitive

    nonAbelianCovariantDerivativeMissingPrimitivesAreCanonical :
      nonAbelianCovariantDerivativeMissingPrimitives
      ≡
      YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeMissingPrimitives

    actionFunctionalMissingPrimitives :
      List YMObs.YMSFGCActionFunctionalMissingPrimitive

    actionFunctionalMissingPrimitivesAreCanonical :
      actionFunctionalMissingPrimitives
      ≡
      YMObs.canonicalYMSFGCActionFunctionalMissingPrimitives

    obligations :
      List YangMillsFieldEquationTargetObligation

    obligationsAreCanonical :
      obligations
      ≡
      canonicalYangMillsFieldEquationTargetObligations

    firstMissing :
      YangMillsFieldEquationFirstMissing

    firstMissingIsCovariantDerivativeHodgeCurrentPackage :
      firstMissing
      ≡
      missingCovariantDerivativeHodgeCurrentPackage

    receiptScope :
      List String

    missingSurface :
      List String

    unsupportedClaims :
      List YangMillsFieldEquationUnsupportedClaim

    unsupportedClaimsAreCanonical :
      unsupportedClaims
      ≡
      canonicalYangMillsFieldEquationUnsupportedClaims

    yangMillsClosurePromoted :
      Bool

    yangMillsClosurePromotedIsFalse :
      yangMillsClosurePromoted ≡ false

    maxwellClosurePromoted :
      Bool

    maxwellClosurePromotedIsFalse :
      maxwellClosurePromoted ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    nonPromotionBoundary :
      List String

canonicalYangMillsFieldEquationReceipt :
  YangMillsFieldEquationReceipt
canonicalYangMillsFieldEquationReceipt =
  record
    { status =
        obligationTargetOnly
    ; target =
        canonicalYangMillsFieldEquationTarget
    ; targetIsCanonical =
        refl
    ; discreteConnectionCandidate =
        DCRT.canonicalDiscreteConnectionCandidateFromCRT
    ; discreteConnectionCandidateIsCanonical =
        refl
    ; discreteCurvatureCarrierObligation =
        G2DCC.canonicalSFGCGaugeDiscreteCurvatureCarrierObligation
    ; discreteCurvatureCarrierObligationIsCanonical =
        refl
    ; upstreamCurvatureAPIObstruction =
        G2DCC.canonicalSFGCGaugeFieldCurvatureAPIObstruction
    ; upstreamCurvatureAPIObstructionIsCanonical =
        refl
    ; upstreamCurvatureAPIFirstMissing =
        G2DCC.G2SFGCGaugeFieldCurvatureAPIObstruction.firstMissing
          G2DCC.canonicalSFGCGaugeFieldCurvatureAPIObstruction
    ; upstreamCurvatureAPIFirstMissingIsGaugeConnection =
        refl
    ; implementedNondegeneratePlaquetteAPI =
        YMObs.canonicalYMSFGCNondegeneratePlaquetteAPI
    ; implementedNondegeneratePlaquetteAPIIsCanonical =
        refl
    ; implementedDiscreteCurvatureCarrier =
        YMObs.canonicalYMSFGCDiscreteCurvatureCarrier
    ; implementedDiscreteCurvatureCarrierIsCanonical =
        refl
    ; su2LieAlgebraModule =
        YM_SU2.canonicalSU2LieAlgebra
    ; su2LieAlgebraModuleIsCanonical =
        refl
    ; covariantDerivativeModule =
        YM_CD.D_A
    ; covariantDerivativeModuleIsCanonical =
        refl
    ; fieldStrengthModule =
        YM_FS.F_A
    ; fieldStrengthModuleIsCanonical =
        refl
    ; yangMillsActionModule =
        YM_YM.ymAction
    ; yangMillsActionModuleIsCanonical =
        refl
    ; discreteBianchiReceipt =
        Bianchi.canonicalDiscreteBianchiIdentityReceipt
    ; discreteBianchiReceiptIsCanonical =
        refl
    ; fieldEquationObstruction =
        YMObs.canonicalYangMillsFieldEquationObstruction
    ; fieldEquationObstructionIsCanonical =
        refl
    ; covariantHodgeCurrentPackageRequest =
        YMObs.canonicalYMSFGCCovariantHodgeCurrentPackageRequest
    ; covariantHodgeCurrentPackageRequestIsCanonical =
        refl
    ; selectedOperatorSkeleton =
        YMObs.canonicalYMSFGCSelectedOperatorSkeleton
    ; selectedOperatorSkeletonIsCanonical =
        refl
    ; primitiveDefinitionCandidateSurface =
        YMObs.canonicalYMSFGCPrimitiveDefinitionCandidateSurface
    ; primitiveDefinitionCandidateSurfaceIsCanonical =
        refl
    ; lowerPrimitiveCandidateBundle =
        YMObs.canonicalYMSFGCLowerPrimitiveCandidateBundle
    ; lowerPrimitiveCandidateBundleIsCanonical =
        refl
    ; suppliedLinkFibreTransportCompilerReceipt =
        YMObs.canonicalYMSFGCSuppliedLinkFibreTransportCompilerReceipt
    ; suppliedLinkFibreTransportCompilerReceiptIsCanonical =
        refl
    ; primitiveInterfaceRequest =
        YMObs.canonicalYMSFGCPrimitiveInterfaceRequest
    ; primitiveInterfaceRequestIsCanonical =
        refl
    ; nonAbelianCovariantDerivativeTheoremThinReceipt =
        YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeTheoremThinReceipt
    ; nonAbelianCovariantDerivativeTheoremThinReceiptIsCanonical =
        refl
    ; su3JacobiGlobalCarrierRouteReceipt =
        YMObs.canonicalYMSFGCSU3JacobiGlobalCarrierRouteReceipt
    ; su3JacobiGlobalCarrierRouteReceiptIsCanonical =
        refl
    ; transportActionVariationAbsenceLedger =
        YMObs.canonicalYMSFGCFieldStrengthTransportActionVariationAbsenceLedger
    ; transportActionVariationAbsenceLedgerIsCanonical =
        refl
    ; realYMPrimitiveSupplyRequestPack =
        YMObs.canonicalYMSFGCRealYMPrimitiveSupplyRequestPack
    ; realYMPrimitiveSupplyRequestPackIsCanonical =
        refl
    ; gate3RouteBU2ConsumerStaging =
        canonicalYMSFGCGate3RouteBU2ConsumerStaging
    ; gate3RouteBU2ConsumerStagingIsCanonical =
        refl
    ; gate3Wave2FiniteHolonomyMathReceipt =
        YMObs.canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt
    ; gate3Wave2FiniteHolonomyMathReceiptIsCanonical =
        refl
    ; gate3Wave3StrictPromotionDecisionReceipt =
        YMObs.canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt
    ; gate3Wave3StrictPromotionDecisionReceiptIsCanonical =
        refl
    ; m1FiniteCarrierGapStagingReceipt =
        canonicalYMSFGCM1FiniteCarrierGapStagingReceipt
    ; m1FiniteCarrierGapStagingReceiptIsCanonical =
        refl
    ; gate3M1U2M2WorkerReceipt =
        canonicalYMSFGCGate3M1U2M2WorkerReceipt
    ; gate3M1U2M2WorkerReceiptIsCanonical =
        refl
    ; userSuppliedRealYMPrimitiveTypedRequest =
        YMObs.canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; userSuppliedRealYMPrimitiveTypedRequestIsCanonical =
        refl
    ; arbitraryGaugeHolonomyKillingAttempt =
        YMObs.canonicalYMSFGCArbitraryGaugeHolonomyKillingAttempt
    ; arbitraryGaugeHolonomyKillingAttemptIsCanonical =
        refl
    ; bianchiDFEqualsZeroBlocker =
        YMObs.canonicalYMSFGCBianchiDFEqualsZeroBlocker
    ; bianchiDFEqualsZeroBlockerIsCanonical =
        refl
    ; routeABianchiAndDiscreteHodgeProgress =
        YMObs.canonicalYMSFGCBianchiAndDiscreteHodgeRouteAProgress
    ; routeABianchiAndDiscreteHodgeProgressIsCanonical =
        refl
    ; flatConnectionGaugeCompatibilityOfBianchiWitness =
        YMObs.canonicalYMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness
    ; flatConnectionGaugeCompatibilityOfBianchiWitnessIsCanonical =
        refl
    ; flatGaugeCompatibilityDischargedPrimitive =
        YMObs.YMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness.dischargedBianchiPrimitive
          YMObs.canonicalYMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness
    ; flatGaugeCompatibilityDischargedPrimitiveIsGaugeCompatibility =
        refl
    ; flatGaugeCompatibilityLocalRemainingBianchiPrimitives =
        YMObs.YMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness.localRemainingBianchiPrimitives
          YMObs.canonicalYMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness
    ; flatGaugeCompatibilityLocalRemainingBianchiPrimitivesExhausted =
        refl
    ; nonFlatHolonomyConjugationIrreducibilityLedger =
        YMObs.canonicalYMSFGCNonFlatHolonomyConjugationIrreducibilityLedger
    ; nonFlatHolonomyConjugationIrreducibilityLedgerIsCanonical =
        refl
    ; selectedEndpointGaugeFactorSourceTargetReceipt =
        YMObs.canonicalYMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt
    ; selectedEndpointGaugeFactorSourceTargetReceiptIsCanonical =
        refl
    ; connectionOneFormAsFibreAlgebraLocalReceipt =
        YMObs.canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt
    ; connectionOneFormAsFibreAlgebraLocalReceiptIsCanonical =
        refl
    ; firstStrictNonFlatHolonomyMissingPrimitive =
        YMObs.YMSFGCExactCanonicalMissingPrimitiveSummary.firstStrictNonFlatHolonomyMissingPrimitive
          YMObs.canonicalYMSFGCExactCanonicalMissingPrimitiveSummary
    ; firstStrictNonFlatHolonomyMissingPrimitiveIsCurvature =
        refl
    ; sourcedDStarFEqualsJBlocker =
        YMObs.canonicalYMSFGCSourcedDStarFEqualsJBlocker
    ; sourcedDStarFEqualsJBlockerIsCanonical =
        refl
    ; routeBLowerHodgeCurrentSurface =
        canonicalYMSFGCRouteBLowerHodgeCurrentSurface
    ; routeBLowerHodgeCurrentSurfaceIsCanonical =
        refl
    ; middle6DiscreteIBPVariationPairingProgress =
        YMObs.canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt
    ; middle6DiscreteIBPVariationPairingProgressIsCanonical =
        refl
    ; middle6VariationPairingFirstMissingDependency =
        YMObs.YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt.firstMissingDependency
          YMObs.canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt
    ; middle6VariationPairingFirstMissingDependencyIsSelectedActionPairing =
        refl
    ; finalPrimitiveLowerLawCandidate =
        YMObs.canonicalYMSFGCFinalPrimitiveLowerLawCandidate
    ; finalPrimitiveLowerLawCandidateIsCanonical =
        refl
    ; exactCanonicalMissingPrimitiveSummary =
        YMObs.canonicalYMSFGCExactCanonicalMissingPrimitiveSummary
    ; exactCanonicalMissingPrimitiveSummaryIsCanonical =
        refl
    ; typedPathTransportPrimitiveRequest =
        YMObs.canonicalSFGCPathTransportPrimitiveTypedRequest
    ; typedPathTransportPrimitiveRequestIsCanonical =
        refl
    ; typedCovariantDifferencePrimitiveRequest =
        YMObs.canonicalCovariantDifferencePrimitiveTypedRequest
    ; typedCovariantDifferencePrimitiveRequestIsCanonical =
        refl
    ; typedGaugeInvariantQuadraticDensityPrimitiveRequest =
        YMObs.canonicalGaugeInvariantQuadraticDensityPrimitiveTypedRequest
    ; typedGaugeInvariantQuadraticDensityPrimitiveRequestIsCanonical =
        refl
    ; typedDiscreteYMActionPrimitiveRequest =
        YMObs.canonicalDiscreteYMActionPrimitiveTypedRequest
    ; typedDiscreteYMActionPrimitiveRequestIsCanonical =
        refl
    ; typedDiscreteHodgeCovariantDerivativePrimitiveRequest =
        YMObs.canonicalDiscreteHodgeCovariantDerivativePrimitiveTypedRequest
    ; typedDiscreteHodgeCovariantDerivativePrimitiveRequestIsCanonical =
        refl
    ; typedNonAbelianCovariantDerivativePrimitiveRequest =
        YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest
    ; typedNonAbelianCovariantDerivativePrimitiveRequestIsCanonical =
        refl
    ; selectedFieldStrengthTransportActionCandidate =
        YMObs.canonicalYMSFGCSelectedFieldStrengthAdjointTransportCandidate
    ; selectedFieldStrengthTransportActionCandidateIsCanonical =
        refl
    ; covariantDerivativeExtendsSelectedExteriorDerivativeCandidate =
        YMObs.canonicalYMSFGCFlatConnectionExteriorExtensionWitness
    ; covariantDerivativeExtendsSelectedExteriorDerivativeCandidateIsCanonical =
        refl
    ; curvatureQuadraticDensityOnPhase4PlaquettesCandidate =
        YMObs.canonicalYMSFGCCurvatureQuadraticDensityProxy
    ; curvatureQuadraticDensityOnPhase4PlaquettesCandidateIsCanonical =
        refl
    ; selectedExteriorDerivativeSquaredZeroWitness =
        YMObs.canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness
    ; selectedExteriorDerivativeSquaredZeroWitnessIsCanonical =
        refl
    ; exactMissingPrerequisites =
        YMObs.canonicalYangMillsFieldEquationMissingPrerequisites
    ; exactMissingPrerequisitesAreCanonical =
        refl
    ; bianchiMissingPrimitives =
        YMObs.canonicalYangMillsBianchiMissingPrimitives
    ; bianchiMissingPrimitivesAreCanonical =
        refl
    ; variationalEquationMissingPrimitives =
        YMObs.canonicalYangMillsVariationalEquationMissingPrimitives
    ; variationalEquationMissingPrimitivesAreCanonical =
        refl
    ; selectedCovariantDerivativeMissingPrimitives =
        YMObs.canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives
    ; selectedCovariantDerivativeMissingPrimitivesAreCanonical =
        refl
    ; selectedFiniteGaugeSectorBridge =
        YMObs.canonicalYMSFGCSelectedFiniteGaugeSectorBridge
    ; selectedFiniteGaugeSectorBridgeIsCanonical =
        refl
    ; nonAbelianCovariantDerivativeMissingPrimitives =
        YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeMissingPrimitives
    ; nonAbelianCovariantDerivativeMissingPrimitivesAreCanonical =
        refl
    ; actionFunctionalMissingPrimitives =
        YMObs.canonicalYMSFGCActionFunctionalMissingPrimitives
    ; actionFunctionalMissingPrimitivesAreCanonical =
        refl
    ; obligations =
        canonicalYangMillsFieldEquationTargetObligations
    ; obligationsAreCanonical =
        refl
    ; firstMissing =
        missingCovariantDerivativeHodgeCurrentPackage
    ; firstMissingIsCovariantDerivativeHodgeCurrentPackage =
        refl
    ; receiptScope =
        "Records a connection carrier target from DiscreteConnectionCandidateFromCRT"
        ∷ "Records a curvature carrier obligation from G2DiscreteCurvatureCarrier"
        ∷ "Records the SFGCSite2D nondegenerate plaquette API as the implemented curvature carrier"
        ∷ "Records selected operator skeleton A -> δ1(connectionTo1Form A) -> field-strength bridge"
        ∷ "Records three non-promoting primitive candidates: selected field-strength transport action, flat covariant-extension witness, and Phase4 plaquette-density proxy"
        ∷ "Records a lower non-promoting bundle that instantiates all four primitive record shapes and closes the identity-edge target law"
        ∷ "Records the supplied link/fibre field-strength transport interface and compiler into SFGCPathTransportPrimitive"
        ∷ "Records a theorem-thin non-abelian covariant derivative target and a local finite 3-axis bracket witness for bracket/negation/antisymmetry/Jacobi"
        ∷ "Records the SU(3)-target eight-generator scaffold with embedded SU(2) first-three-generator bracket witnesses"
        ∷ "Records the coefficient-carrying list-valued SU(3) structure table, including the multi-output [4,5] and [6,7] Cartan decompositions"
        ∷ "Records the fail-closed route receipt from the finite coefficient-aware 512 Jacobi carrier toward SU3JacobiGlobalCarrier"
        ∷ "Records a typed absence ledger for the remaining field-strength fibre-action covariance and action-variation blockers"
        ∷ "Records real primitive supply requests for user-supplied non-flat lattice connection, holonomy telescoping, Lie/trace Ad-invariance, discrete Hodge/covariant derivative, and discrete IBP"
        ∷ "Consumes the Gate 3 m1 curvature advancement and stages Route B plus u2 fibre-consumer fields in a non-promoting receipt-local consumer surface"
        ∷ "Records selected endpoint gauge factors at SFGCSite2DEdge sources/targets, including bottom/left source identification with the plaquette SW corner"
        ∷ "Records a local connectionOneFormAsFibreAlgebra receipt into finite Lie3 and the local finite SU(3) scaffold without promoting a user-supplied non-flat connection"
        ∷ "Records the wave-3 final-local promotion decision: finite-local curvature/holonomy/Lie/Hodge evidence does not definitionally match the strict user-supplied real YM carriers"
        ∷ "Records m1 finite Lie/Casimir-style carrier gap staging against the existing non-flat curvature, selected finite gauge-sector, variation-pairing, and UniformBalaban-or-Agawa blockers"
        ∷ "Records arbitrary-gauge selected holonomy conjugation by finite-C4 flat square cancellation"
        ∷ "Records lower final-law candidates for constant-gauge vacuum holonomy covariance, trivial-adjoint phase-zero density invariance, and zero-variation IBP"
        ∷ "Records separate blocker surfaces for homogeneous D F = 0 and sourced D * F = J"
        ∷ "Records a Route B lower Hodge/current surface with Bool-valued covariantDerivativeOnDualCurvature, currentSource, and definitional D * F = J law"
        ∷ "Records the bounded flat gauge-compatibility witness for the selected Bianchi plaquette law and its exhausted local primitive queue"
        ∷ "Records exact typed primitive requests for path transport, covariant difference, non-abelian covariant derivative, gauge-invariant quadratic density, discrete YM action, and discrete Hodge/covariant derivative"
        ∷ "Records the final typed primitive math blockers: non-flat holonomy conjugation under gauge transform, Killing-form Ad-invariance, and discrete variation/IBP"
        ∷ "Records the exact canonical missing primitive summary: lower transport/covariant-difference/density/action candidates, flat holonomy cancellation, trivial Ad residual cancellation, and exact zero-IBP law"
        ∷ "The path request reuses SFGCSite2DEdge source/target and asks for identity path, field-strength fiber transport, and gauge-compatibility law"
        ∷ "The action request reuses SFGCSite2DPlaquette and asks for nonconstant Killing density, plaquette integration, variation pairing, and Euler-Lagrange target"
        ∷ "Records selected exterior d^2 = 0 from SFGC.sfgcSite2DP2P3BoundaryOfBoundaryZero"
        ∷ "Consumes YangMillsFieldEquationObstruction to name the exact missing prerequisites"
        ∷ "Records covariant-derivative, Hodge-dual, D * F = J, and Bianchi targets as obligations"
        ∷ "Records the 64-slot repeated-first-two-axis SU(3) Jacobi zero batch and the named [1,4,5] coefficient-erased residual blocker"
        ∷ []
    ; missingSurface =
        "First missing: covariant derivative, Hodge-star, and current-source package for the selected SFGCSite2D curvature carrier"
        ∷ "Legacy upstream curvature API obstruction still records missingShiftGaugeFieldGaugeConnection for the older right-edge-only G2DCC diagnostic"
        ∷ "A DiscreteCurvatureCarrier SFGC.GaugeField is now derived from canonicalYMSFGCNondegeneratePlaquetteAPI"
        ∷ "Selected operator skeleton is now present, but it does not include a promoted field-strength transport/action or covariant difference"
        ∷ "Non-abelian D_A receipt now has a local finite 3-axis bracket witness and an SU(3)-target scaffold with embedded first-three-generator, off-diagonal root-direction, generator-8 Cartan action brackets, a coefficient-carrying multi-output structure table, and a finite 512-entry positive-axis Jacobi carrier"
        ∷ "Representative SU(3) Jacobi slots [1,2,3], [4,5,8], and [6,7,8] now carry zero-residual witnesses, and the 64 repeated-first-two-axis slots [x,x,z] are checked zero"
        ∷ "Coefficient-aware all-slot SU(3) Jacobi residuals are staged over the finite slot function, but SU3JacobiGlobalCarrier remains blocked by missingSFGCFibreRepresentationIntoSU3Carrier"
        ∷ "A concrete typed SFGC fibre representation candidate into the local finite SU(3) carrier is now wired at the theorem-thin layer"
        ∷ "Lower candidates now inhabit SFGCPathTransportPrimitive, CovariantDifferencePrimitive, GaugeInvariantQuadraticDensityPrimitive, and DiscreteYMActionPrimitive only as non-promoting surfaces"
        ∷ "Typed path detail: identityPathTargetLaw for SFGCSite2DEdge is closed by SFGC.sfgcSite2DIdentityEdgeTargetLaw; the supplied link/fibre compiler lowers the edge-target probe into SFGCPathTransportPrimitive"
        ∷ "Typed absence detail: the remaining supplied-interface blockers are fibre-action covariance for real transport and variation pairing for the selected action surface"
        ∷ "Real primitive request detail: user-supplied non-flat lattice connection, holonomy telescoping, Lie-algebra trace/Killing Ad-invariance, discrete Hodge/covariant derivative, and discrete IBP remain requested supply records, not local proofs"
        ∷ "Gate 3 Route B/u2 consumer detail: the selected lower Hodge/current supply closes only a definitional selected-field-strength equation, while the u2 non-flat lattice supply keeps gauge transform and transport as identity probes"
        ∷ "Endpoint source/target detail: concrete Phase4 endpoint factors are exposed, but the real non-flat holonomy carrier remains user-supplied"
        ∷ "Connection-one-form detail: the local finite receipt maps the selected start-point gauge phase into finite Lie3/SU3, and the requested non-flat connection carrier now has the finite SFGCSite2D adapter"
        ∷ "Wave-3 final-local detail: the Site2D connection and dual-curvature adapters are finite; strict promotion still requires an exact GaugeField section plus holonomy, Lie, transport, Hodge, and variation laws"
        ∷ "m1 finite-carrier gap detail: the local finite Lie3 and finite-C4 trace/Ad receipts stage only a Casimir-style finite-carrier witness; they do not construct a continuum spectral gap"
        ∷ "Typed lower-law detail: only constant-gauge vacuum holonomy covariance, trivial-adjoint phase-zero density invariance, and zero-variation IBP are discharged"
        ∷ "Round-2 typed law detail: arbitrary selected SFGC holonomy conjugation is discharged by Wilson-loop phase zero before and after arbitrary gauge transform"
        ∷ "Final typed blocker detail: non-flat holonomy conjugation under gauge transform, real Killing-form Ad-invariance, and discrete variation/IBP are not supplied"
        ∷ "Exact summary detail: the strongest inhabited laws are flat selected holonomy cancellation, identity-adjoint residual cancellation, local finite bracket/Jacobi, typed SFGC-to-SU(3) candidate representation, and zero-variation IBP; first strict blockers are real field-strength fibre action, gauge-compatible representation law, non-flat connection curvature, and variation pairing"
        ∷ "D F = 0 blocker detail: selected exterior d^2 = 0 is available, but no covariant Bianchi transport law is supplied"
        ∷ "Flat Bianchi gauge-compat detail: the selected vacuum plaquette law is gauge-compatible by flat finite-C4 holonomy cancellation and the trivial selected adjoint candidate"
        ∷ "Non-flat Bianchi gauge-compat blocker detail: missingNonFlatSFGCSite2DConnectionCurvature remains the first strict holonomy-conjugation primitive"
        ∷ "D * F = J blocker detail: Hodge star, current source, selected action variation, and Euler-Lagrange law are not supplied"
        ∷ "Route B lower Hodge/current detail: the Bool-valued D * F = J shape is inhabited only as false == false and is paired with the existing sourced blocker"
        ∷ "Still missing: real gauge-compatible field-strength fibre transport, real covariant difference, gauge-compatible SFGC fibre representation law into the local finite Lie carrier, physical D_A laws, Killing trace density, plaquette integration, Hodge star, dual covariant derivative, current coupling, and variation pairing"
        ∷ "First selected covariant derivative primitive missing: field-strength transport/action on the selected gauge bundle"
        ∷ "First action-functional primitive missing: curvature quadratic density on Phase4 plaquette values"
        ∷ "Selected exterior d^2 = 0 is wired for δ1(δ0 f) on the p2/p3 plaquette evaluation"
        ∷ "No closed covariant derivative over the selected gauge bundle is supplied"
        ∷ "No Hodge-star construction is supplied"
        ∷ "No current/source term J is coupled to D * F"
        ∷ "No variational Yang-Mills equation D * F = J is supplied"
        ∷ "No transport from selected exterior d^2 = 0 to covariant Yang-Mills D F = 0 is supplied"
        ∷ []
    ; unsupportedClaims =
        canonicalYangMillsFieldEquationUnsupportedClaims
    ; unsupportedClaimsAreCanonical =
        refl
    ; yangMillsClosurePromoted =
        false
    ; yangMillsClosurePromotedIsFalse =
        refl
    ; maxwellClosurePromoted =
        false
    ; maxwellClosurePromotedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; nonPromotionBoundary =
        "This receipt is an obligation surface only"
        ∷ "SFGC.shiftFiniteGaugeCoupling is recorded as a finite matter covariant operator, not a Yang-Mills derivative on curvature"
        ∷ "The selected operator skeleton records curvature and field-strength construction, but not Yang-Mills transport, Hodge star, action functional, or source coupling"
        ∷ "The primitive interface request records exact missing transport, covariant difference, density, and action surfaces; the lower bundle inhabits them only as non-promoting candidates"
        ∷ "The new YM modules are concrete: canonicalSU2LieAlgebra, D_A, F_A, and ymAction are now imported as inhabited witnesses"
        ∷ "The non-abelian covariant derivative receipt has a local finite bracket/Jacobi witness but remains uninhabited by physical SFGC/SFGS fibre primitives"
        ∷ "The SU(3)-target scaffold records the embedded SU(2) first-three-generator bracket lane, coefficient-aware all-slot finite Jacobi arithmetic, and the route blocker missingSFGCFibreRepresentationIntoSU3Carrier; it does not promote full SU(3)"
        ∷ "The real primitive supply request pack records the finite Site2D non-flat connection adapter plus holonomy, Lie/trace, Hodge/covariant-derivative, and IBP supplies still absent from SFGC/SFGS"
        ∷ "The Gate 3 Route B/u2 consumer staging surface consumes m1 curvature advancement but keeps consumerPromoted false"
        ∷ "The m1 finite-carrier gap staging receipt keeps selfAdjointHamiltonianConstructed false and continuumMassGapPromoted false"
        ∷ "The final lower-law candidate now closes arbitrary selected SFGC holonomy conjugation, but only by flat finite-C4 cancellation"
        ∷ "The final absence ledger names the missing non-flat holonomy-conjugation, Killing Ad-invariance, and discrete variation/IBP primitives"
        ∷ "The homogeneous D F = 0 blocker is separated from the sourced D * F = J blocker"
        ∷ "The Route B lower Hodge/current surface inhabits only a trivial Bool-current equation and keeps missingVariationPairingForSelectedHodgeStar as the strict blocker"
        ∷ "The flat gauge-compatibility witness exhausts only the bounded selected vacuum Bianchi primitive queue"
        ∷ "The first strict non-flat holonomy blocker is still missingNonFlatSFGCSite2DConnectionCurvature"
        ∷ "The variational D * F = J blockers and the Bianchi d^2-to-D F transport blockers are split in YMSFGCCovariantHodgeCurrentPackageRequest"
        ∷ "It does not prove D * F = J"
        ∷ "It does not prove a covariant Yang-Mills Bianchi identity"
        ∷ "It does not claim Maxwell closure, Yang-Mills closure, mass gap, Clay problem resolution, spectral gap, or terminal promotion"
        ∷ []
    }

yangMillsFieldEquationReceiptStatusIsObligationOnly :
  YangMillsFieldEquationReceipt.status
    canonicalYangMillsFieldEquationReceipt
  ≡
  obligationTargetOnly
yangMillsFieldEquationReceiptStatusIsObligationOnly = refl

yangMillsFieldEquationReceiptFirstMissing :
  YangMillsFieldEquationReceipt.firstMissing
    canonicalYangMillsFieldEquationReceipt
  ≡
  missingCovariantDerivativeHodgeCurrentPackage
yangMillsFieldEquationReceiptFirstMissing = refl

yangMillsFieldEquationReceiptCurvatureCarrierImplemented :
  YangMillsFieldEquationReceipt.implementedDiscreteCurvatureCarrier
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCDiscreteCurvatureCarrier
yangMillsFieldEquationReceiptCurvatureCarrierImplemented = refl

yangMillsFieldEquationReceiptCovariantHodgeCurrentPackageRequest :
  YangMillsFieldEquationReceipt.covariantHodgeCurrentPackageRequest
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCCovariantHodgeCurrentPackageRequest
yangMillsFieldEquationReceiptCovariantHodgeCurrentPackageRequest = refl

yangMillsFieldEquationReceiptSelectedOperatorSkeleton :
  YangMillsFieldEquationReceipt.selectedOperatorSkeleton
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCSelectedOperatorSkeleton
yangMillsFieldEquationReceiptSelectedOperatorSkeleton = refl

yangMillsFieldEquationReceiptPrimitiveDefinitionCandidateSurface :
  YangMillsFieldEquationReceipt.primitiveDefinitionCandidateSurface
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCPrimitiveDefinitionCandidateSurface
yangMillsFieldEquationReceiptPrimitiveDefinitionCandidateSurface =
  refl

yangMillsFieldEquationReceiptLowerPrimitiveCandidateBundle :
  YangMillsFieldEquationReceipt.lowerPrimitiveCandidateBundle
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCLowerPrimitiveCandidateBundle
yangMillsFieldEquationReceiptLowerPrimitiveCandidateBundle =
  refl

yangMillsFieldEquationReceiptSuppliedLinkFibreTransportCompilerReceipt :
  YangMillsFieldEquationReceipt.suppliedLinkFibreTransportCompilerReceipt
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCSuppliedLinkFibreTransportCompilerReceipt
yangMillsFieldEquationReceiptSuppliedLinkFibreTransportCompilerReceipt =
  refl

yangMillsFieldEquationReceiptPrimitiveInterfaceRequest :
  YangMillsFieldEquationReceipt.primitiveInterfaceRequest
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCPrimitiveInterfaceRequest
yangMillsFieldEquationReceiptPrimitiveInterfaceRequest =
  refl

yangMillsFieldEquationReceiptTransportActionVariationAbsenceLedger :
  YangMillsFieldEquationReceipt.transportActionVariationAbsenceLedger
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCFieldStrengthTransportActionVariationAbsenceLedger
yangMillsFieldEquationReceiptTransportActionVariationAbsenceLedger =
  refl

yangMillsFieldEquationReceiptRealYMPrimitiveSupplyRequestPack :
  YangMillsFieldEquationReceipt.realYMPrimitiveSupplyRequestPack
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCRealYMPrimitiveSupplyRequestPack
yangMillsFieldEquationReceiptRealYMPrimitiveSupplyRequestPack =
  refl

yangMillsFieldEquationReceiptUserSuppliedRealYMPrimitiveTypedRequest :
  YangMillsFieldEquationReceipt.userSuppliedRealYMPrimitiveTypedRequest
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
yangMillsFieldEquationReceiptUserSuppliedRealYMPrimitiveTypedRequest =
  refl

yangMillsFieldEquationReceiptArbitraryGaugeHolonomyKillingAttempt :
  YangMillsFieldEquationReceipt.arbitraryGaugeHolonomyKillingAttempt
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCArbitraryGaugeHolonomyKillingAttempt
yangMillsFieldEquationReceiptArbitraryGaugeHolonomyKillingAttempt =
  refl

yangMillsFieldEquationReceiptBianchiDFEqualsZeroBlocker :
  YangMillsFieldEquationReceipt.bianchiDFEqualsZeroBlocker
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCBianchiDFEqualsZeroBlocker
yangMillsFieldEquationReceiptBianchiDFEqualsZeroBlocker =
  refl

yangMillsFieldEquationReceiptRouteABianchiAndDiscreteHodgeProgress :
  YangMillsFieldEquationReceipt.routeABianchiAndDiscreteHodgeProgress
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCBianchiAndDiscreteHodgeRouteAProgress
yangMillsFieldEquationReceiptRouteABianchiAndDiscreteHodgeProgress =
  refl

yangMillsFieldEquationReceiptFlatGaugeCompatibilityWitness :
  YangMillsFieldEquationReceipt.flatConnectionGaugeCompatibilityOfBianchiWitness
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness
yangMillsFieldEquationReceiptFlatGaugeCompatibilityWitness =
  refl

yangMillsFieldEquationReceiptFlatGaugeCompatibilityDischargedPrimitive :
  YangMillsFieldEquationReceipt.flatGaugeCompatibilityDischargedPrimitive
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.missingGaugeCompatibilityOfBianchiLaw
yangMillsFieldEquationReceiptFlatGaugeCompatibilityDischargedPrimitive =
  refl

yangMillsFieldEquationReceiptFlatGaugeCompatibilityLocalQueueExhausted :
  YangMillsFieldEquationReceipt.flatGaugeCompatibilityLocalRemainingBianchiPrimitives
    canonicalYangMillsFieldEquationReceipt
  ≡
  []
yangMillsFieldEquationReceiptFlatGaugeCompatibilityLocalQueueExhausted =
  refl

yangMillsFieldEquationReceiptNonFlatHolonomyLedger :
  YangMillsFieldEquationReceipt.nonFlatHolonomyConjugationIrreducibilityLedger
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCNonFlatHolonomyConjugationIrreducibilityLedger
yangMillsFieldEquationReceiptNonFlatHolonomyLedger =
  refl

yangMillsFieldEquationReceiptEndpointGaugeFactorSourceTargetReceipt :
  YangMillsFieldEquationReceipt.selectedEndpointGaugeFactorSourceTargetReceipt
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt
yangMillsFieldEquationReceiptEndpointGaugeFactorSourceTargetReceipt =
  refl

yangMillsFieldEquationReceiptConnectionOneFormAsFibreAlgebraLocalReceipt :
  YangMillsFieldEquationReceipt.connectionOneFormAsFibreAlgebraLocalReceipt
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt
yangMillsFieldEquationReceiptConnectionOneFormAsFibreAlgebraLocalReceipt =
  refl

yangMillsFieldEquationReceiptFirstStrictNonFlatHolonomyMissingPrimitive :
  YangMillsFieldEquationReceipt.firstStrictNonFlatHolonomyMissingPrimitive
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.missingNonFlatSFGCSite2DConnectionCurvature
yangMillsFieldEquationReceiptFirstStrictNonFlatHolonomyMissingPrimitive =
  refl

yangMillsFieldEquationReceiptSourcedDStarFEqualsJBlocker :
  YangMillsFieldEquationReceipt.sourcedDStarFEqualsJBlocker
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCSourcedDStarFEqualsJBlocker
yangMillsFieldEquationReceiptSourcedDStarFEqualsJBlocker =
  refl

yangMillsFieldEquationReceiptRouteBLowerHodgeCurrentSurface :
  YangMillsFieldEquationReceipt.routeBLowerHodgeCurrentSurface
    canonicalYangMillsFieldEquationReceipt
  ≡
  canonicalYMSFGCRouteBLowerHodgeCurrentSurface
yangMillsFieldEquationReceiptRouteBLowerHodgeCurrentSurface =
  refl

yangMillsFieldEquationReceiptRouteBLowerHodgeSupply :
  YMSFGCRouteBLowerHodgeCurrentSurface.lowerDiscreteHodgeCovariantDerivativeSupply
    (YangMillsFieldEquationReceipt.routeBLowerHodgeCurrentSurface
      canonicalYangMillsFieldEquationReceipt)
  ≡
  canonicalRouteBLowerDiscreteHodgeCovariantDerivativeSupply
yangMillsFieldEquationReceiptRouteBLowerHodgeSupply =
  refl

yangMillsFieldEquationReceiptRouteBLowerCovariantDerivativeOnDualCurvature :
  YMSFGCRouteBLowerHodgeCurrentSurface.lowerCovariantDerivativeOnDualCurvature
    (YangMillsFieldEquationReceipt.routeBLowerHodgeCurrentSurface
      canonicalYangMillsFieldEquationReceipt)
  ≡
  routeBLowerCovariantDerivativeOnDualCurvature
yangMillsFieldEquationReceiptRouteBLowerCovariantDerivativeOnDualCurvature =
  refl

yangMillsFieldEquationReceiptRouteBLowerCurrentSource :
  YMSFGCRouteBLowerHodgeCurrentSurface.lowerCurrentSource
    (YangMillsFieldEquationReceipt.routeBLowerHodgeCurrentSurface
      canonicalYangMillsFieldEquationReceipt)
  ≡
  routeBLowerCurrentSource
yangMillsFieldEquationReceiptRouteBLowerCurrentSource =
  refl

yangMillsFieldEquationReceiptRouteBLowerDStarFEqualsJLaw :
  YMSFGCRouteBLowerHodgeCurrentSurface.lowerDStarFEqualsJLaw
    (YangMillsFieldEquationReceipt.routeBLowerHodgeCurrentSurface
      canonicalYangMillsFieldEquationReceipt)
  ≡
  routeBLowerDStarFEqualsJLaw
yangMillsFieldEquationReceiptRouteBLowerDStarFEqualsJLaw =
  refl

yangMillsFieldEquationReceiptRouteBLowerDiscreteVariationIBPSurface :
  YMSFGCRouteBLowerHodgeCurrentSurface.discreteVariationIBPSurface
    (YangMillsFieldEquationReceipt.routeBLowerHodgeCurrentSurface
      canonicalYangMillsFieldEquationReceipt)
  ≡
  YMObs.canonicalYMSFGCDiscreteVariationIBPLowerCandidate
yangMillsFieldEquationReceiptRouteBLowerDiscreteVariationIBPSurface =
  refl

yangMillsFieldEquationReceiptRouteBSelectedHodgeSupply :
  YMSFGCRouteBLowerHodgeCurrentSurface.selectedDiscreteHodgeCovariantDerivativeSupply
    (YangMillsFieldEquationReceipt.routeBLowerHodgeCurrentSurface
      canonicalYangMillsFieldEquationReceipt)
  ≡
  canonicalRouteBSelectedDiscreteHodgeCovariantDerivativeSupply
yangMillsFieldEquationReceiptRouteBSelectedHodgeSupply =
  refl

yangMillsFieldEquationReceiptRouteBSelectedHodgeStar :
  YMObs.YMSFGCDiscreteHodgeCovariantDerivativePrimitiveSupply.hodgeStar
    (YMSFGCRouteBLowerHodgeCurrentSurface.selectedDiscreteHodgeCovariantDerivativeSupply
      (YangMillsFieldEquationReceipt.routeBLowerHodgeCurrentSurface
        canonicalYangMillsFieldEquationReceipt))
  ≡
  routeBSelectedHodgeStar
yangMillsFieldEquationReceiptRouteBSelectedHodgeStar =
  refl

yangMillsFieldEquationReceiptRouteBSelectedCovariantDerivativeOnDualCurvature :
  YMObs.YMSFGCDiscreteHodgeCovariantDerivativePrimitiveSupply.covariantDerivativeOnDualCurvature
    (YMSFGCRouteBLowerHodgeCurrentSurface.selectedDiscreteHodgeCovariantDerivativeSupply
      (YangMillsFieldEquationReceipt.routeBLowerHodgeCurrentSurface
        canonicalYangMillsFieldEquationReceipt))
  ≡
  routeBSelectedCovariantDerivativeOnDualCurvature
yangMillsFieldEquationReceiptRouteBSelectedCovariantDerivativeOnDualCurvature =
  refl

yangMillsFieldEquationReceiptRouteBSelectedCurrentSource :
  YMObs.YMSFGCDiscreteHodgeCovariantDerivativePrimitiveSupply.currentSource
    (YMSFGCRouteBLowerHodgeCurrentSurface.selectedDiscreteHodgeCovariantDerivativeSupply
      (YangMillsFieldEquationReceipt.routeBLowerHodgeCurrentSurface
        canonicalYangMillsFieldEquationReceipt))
  ≡
  routeBSelectedCurrentSource
yangMillsFieldEquationReceiptRouteBSelectedCurrentSource =
  refl

yangMillsFieldEquationReceiptRouteBSelectedDStarFEqualsJLaw :
  YMObs.YMSFGCDiscreteHodgeCovariantDerivativePrimitiveSupply.dStarFEqualsJLaw
    (YMSFGCRouteBLowerHodgeCurrentSurface.selectedDiscreteHodgeCovariantDerivativeSupply
      (YangMillsFieldEquationReceipt.routeBLowerHodgeCurrentSurface
        canonicalYangMillsFieldEquationReceipt))
  ≡
  routeBSelectedDStarFEqualsJLaw
yangMillsFieldEquationReceiptRouteBSelectedDStarFEqualsJLaw =
  refl

yangMillsFieldEquationReceiptRouteBZeroDiscreteVariationIBPPrimitiveSupply :
  YMSFGCRouteBLowerHodgeCurrentSurface.zeroDiscreteVariationIBPPrimitiveSupply
    (YangMillsFieldEquationReceipt.routeBLowerHodgeCurrentSurface
      canonicalYangMillsFieldEquationReceipt)
  ≡
  canonicalRouteBZeroDiscreteVariationIBPPrimitiveSupply
yangMillsFieldEquationReceiptRouteBZeroDiscreteVariationIBPPrimitiveSupply =
  refl

yangMillsFieldEquationReceiptRouteBMissingVariationPairingForSelectedHodgeStar :
  YMSFGCRouteBLowerHodgeCurrentSurface.firstStrictRouteBMissingPrimitive
    (YangMillsFieldEquationReceipt.routeBLowerHodgeCurrentSurface
      canonicalYangMillsFieldEquationReceipt)
  ≡
  YMObs.missingVariationPairingForSelectedHodgeStar
yangMillsFieldEquationReceiptRouteBMissingVariationPairingForSelectedHodgeStar =
  refl

yangMillsFieldEquationReceiptYMActionIBPSourceProgress :
  YMObs.YangMillsFieldEquationObstruction.ymActionIBPSourceProgress
    (YangMillsFieldEquationReceipt.fieldEquationObstruction
      canonicalYangMillsFieldEquationReceipt)
  ≡
  YMObs.canonicalYMSFGCYMActionIBPSourceProgress
yangMillsFieldEquationReceiptYMActionIBPSourceProgress =
  refl

yangMillsFieldEquationReceiptGate3RouteBU2ConsumerStaging :
  YangMillsFieldEquationReceipt.gate3RouteBU2ConsumerStaging
    canonicalYangMillsFieldEquationReceipt
  ≡
  canonicalYMSFGCGate3RouteBU2ConsumerStaging
yangMillsFieldEquationReceiptGate3RouteBU2ConsumerStaging =
  refl

yangMillsFieldEquationReceiptGate3NonFlatCurvaturePrimitiveAdvancement :
  YMSFGCGate3RouteBU2ConsumerStaging.gate3NonFlatCurvaturePrimitiveAdvancement
    (YangMillsFieldEquationReceipt.gate3RouteBU2ConsumerStaging
      canonicalYangMillsFieldEquationReceipt)
  ≡
  YMObs.canonicalYMSFGCGate3NonFlatCurvaturePrimitiveAdvancement
yangMillsFieldEquationReceiptGate3NonFlatCurvaturePrimitiveAdvancement =
  refl

yangMillsFieldEquationReceiptGate3Wave2FiniteHolonomyMathReceipt :
  YangMillsFieldEquationReceipt.gate3Wave2FiniteHolonomyMathReceipt
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt
yangMillsFieldEquationReceiptGate3Wave2FiniteHolonomyMathReceipt =
  refl

yangMillsFieldEquationReceiptGate3Wave2FiniteCurvatureClosed :
  YMObs.YMSFGCGate3Wave2FiniteHolonomyMathReceipt.finiteLocalCurvatureHolonomyTraceClosed
    (YangMillsFieldEquationReceipt.gate3Wave2FiniteHolonomyMathReceipt
      canonicalYangMillsFieldEquationReceipt)
  ≡
  true
yangMillsFieldEquationReceiptGate3Wave2FiniteCurvatureClosed =
  refl

yangMillsFieldEquationReceiptGate3Wave2StrictRealBlocker :
  YMObs.YMSFGCGate3Wave2FiniteHolonomyMathReceipt.strictRealNonFlatYMPromotionBlocker
    (YangMillsFieldEquationReceipt.gate3Wave2FiniteHolonomyMathReceipt
      canonicalYangMillsFieldEquationReceipt)
  ≡
  YMObs.missingNonFlatSFGCSite2DConnectionCurvature
yangMillsFieldEquationReceiptGate3Wave2StrictRealBlocker =
  refl

yangMillsFieldEquationReceiptGate3Wave3StrictPromotionDecisionReceipt :
  YangMillsFieldEquationReceipt.gate3Wave3StrictPromotionDecisionReceipt
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt
yangMillsFieldEquationReceiptGate3Wave3StrictPromotionDecisionReceipt =
  refl

yangMillsFieldEquationReceiptGate3Wave3StrictPromotionDecisionNonPromoting :
  YMObs.YMSFGCGate3Wave3StrictPromotionDecisionReceipt.finiteLocalEvidencePromotedToStrictRealYM
    (YangMillsFieldEquationReceipt.gate3Wave3StrictPromotionDecisionReceipt
      canonicalYangMillsFieldEquationReceipt)
  ≡
  false
yangMillsFieldEquationReceiptGate3Wave3StrictPromotionDecisionNonPromoting =
  refl

yangMillsFieldEquationReceiptGate3Wave3FirstStrictNonFlatBlocker :
  YMObs.YMSFGCGate3Wave3StrictPromotionDecisionReceipt.firstStrictNonFlatHolonomyBlocker
    (YangMillsFieldEquationReceipt.gate3Wave3StrictPromotionDecisionReceipt
      canonicalYangMillsFieldEquationReceipt)
  ≡
  YMObs.missingNonFlatSFGCSite2DConnectionCurvature
yangMillsFieldEquationReceiptGate3Wave3FirstStrictNonFlatBlocker =
  refl

yangMillsFieldEquationReceiptGate3Wave3FirstStrictGaugeSectorBlocker :
  YMObs.YMSFGCGate3Wave3StrictPromotionDecisionReceipt.firstStrictGaugeSectorBlocker
    (YangMillsFieldEquationReceipt.gate3Wave3StrictPromotionDecisionReceipt
      canonicalYangMillsFieldEquationReceipt)
  ≡
  YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
yangMillsFieldEquationReceiptGate3Wave3FirstStrictGaugeSectorBlocker =
  refl

yangMillsFieldEquationReceiptGate3Wave3FirstStrictRouteBBlocker :
  YMObs.YMSFGCGate3Wave3StrictPromotionDecisionReceipt.firstStrictRouteBBlocker
    (YangMillsFieldEquationReceipt.gate3Wave3StrictPromotionDecisionReceipt
      canonicalYangMillsFieldEquationReceipt)
  ≡
  YMObs.missingVariationPairingForSelectedHodgeStar
yangMillsFieldEquationReceiptGate3Wave3FirstStrictRouteBBlocker =
  refl

yangMillsFieldEquationReceiptGate3HolonomyTelescopingLaw :
  YMSFGCGate3RouteBU2ConsumerStaging.m1HolonomyTelescopingLawIsFiniteC4
    (YangMillsFieldEquationReceipt.gate3RouteBU2ConsumerStaging
      canonicalYangMillsFieldEquationReceipt)
  ≡
  refl
yangMillsFieldEquationReceiptGate3HolonomyTelescopingLaw =
  refl

yangMillsFieldEquationReceiptGate3HolonomyConjugationLaw :
  YMSFGCGate3RouteBU2ConsumerStaging.m1HolonomyConjugationLawIsFiniteC4
    (YangMillsFieldEquationReceipt.gate3RouteBU2ConsumerStaging
      canonicalYangMillsFieldEquationReceipt)
  ≡
  refl
yangMillsFieldEquationReceiptGate3HolonomyConjugationLaw =
  refl

yangMillsFieldEquationReceiptU2ConnectionOneFormAsFibreAlgebra :
  YMSFGCGate3RouteBU2ConsumerStaging.u2ConnectionOneFormAsFibreAlgebraLocalReceipt
    (YangMillsFieldEquationReceipt.gate3RouteBU2ConsumerStaging
      canonicalYangMillsFieldEquationReceipt)
  ≡
  YMObs.canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt
yangMillsFieldEquationReceiptU2ConnectionOneFormAsFibreAlgebra =
  refl

yangMillsFieldEquationReceiptU2NonFlatLatticeConnectionPrimitiveSupply :
  YMSFGCGate3RouteBU2ConsumerStaging.u2NonFlatLatticeConnectionPrimitiveSupply
    (YangMillsFieldEquationReceipt.gate3RouteBU2ConsumerStaging
      canonicalYangMillsFieldEquationReceipt)
  ≡
  canonicalRouteBU2NonFlatLatticeConnectionPrimitiveSupply
yangMillsFieldEquationReceiptU2NonFlatLatticeConnectionPrimitiveSupply =
  refl

yangMillsFieldEquationReceiptU2CovariantDerivativeSquareLaw :
  YMSFGCGate3RouteBU2ConsumerStaging.u2CovariantDerivativeSquareLawIsCanonical
    (YangMillsFieldEquationReceipt.gate3RouteBU2ConsumerStaging
      canonicalYangMillsFieldEquationReceipt)
  ≡
  true
yangMillsFieldEquationReceiptU2CovariantDerivativeSquareLaw =
  refl

yangMillsFieldEquationReceiptGate3RouteBU2ConsumerStagingNonPromoting :
  YMSFGCGate3RouteBU2ConsumerStaging.consumerPromoted
    (YangMillsFieldEquationReceipt.gate3RouteBU2ConsumerStaging
      canonicalYangMillsFieldEquationReceipt)
  ≡
  false
yangMillsFieldEquationReceiptGate3RouteBU2ConsumerStagingNonPromoting =
  refl

yangMillsFieldEquationReceiptFinalPrimitiveLowerLawCandidate :
  YangMillsFieldEquationReceipt.finalPrimitiveLowerLawCandidate
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCFinalPrimitiveLowerLawCandidate
yangMillsFieldEquationReceiptFinalPrimitiveLowerLawCandidate =
  refl

yangMillsFieldEquationReceiptFinalPrimitiveMathBlockers :
  YMObs.YMSFGCFinalPrimitiveLowerLawCandidate.finalPrimitiveMathBlockers
    (YangMillsFieldEquationReceipt.finalPrimitiveLowerLawCandidate
      canonicalYangMillsFieldEquationReceipt)
  ≡
  YMObs.canonicalYMSFGCFinalPrimitiveMathBlockers
yangMillsFieldEquationReceiptFinalPrimitiveMathBlockers =
  refl

yangMillsFieldEquationReceiptExactCanonicalMissingPrimitiveSummary :
  YangMillsFieldEquationReceipt.exactCanonicalMissingPrimitiveSummary
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCExactCanonicalMissingPrimitiveSummary
yangMillsFieldEquationReceiptExactCanonicalMissingPrimitiveSummary =
  refl

yangMillsFieldEquationReceiptSelectedFieldStrengthTransportActionCandidate :
  YangMillsFieldEquationReceipt.selectedFieldStrengthTransportActionCandidate
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCSelectedFieldStrengthAdjointTransportCandidate
yangMillsFieldEquationReceiptSelectedFieldStrengthTransportActionCandidate =
  refl

yangMillsFieldEquationReceiptCovariantExtensionCandidate :
  YangMillsFieldEquationReceipt.covariantDerivativeExtendsSelectedExteriorDerivativeCandidate
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCFlatConnectionExteriorExtensionWitness
yangMillsFieldEquationReceiptCovariantExtensionCandidate =
  refl

yangMillsFieldEquationReceiptCurvatureDensityCandidate :
  YangMillsFieldEquationReceipt.curvatureQuadraticDensityOnPhase4PlaquettesCandidate
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCCurvatureQuadraticDensityProxy
yangMillsFieldEquationReceiptCurvatureDensityCandidate =
  refl

yangMillsFieldEquationReceiptDiscreteHodgeCovariantDerivativeTypedRequest :
  YangMillsFieldEquationReceipt.typedDiscreteHodgeCovariantDerivativePrimitiveRequest
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalDiscreteHodgeCovariantDerivativePrimitiveTypedRequest
yangMillsFieldEquationReceiptDiscreteHodgeCovariantDerivativeTypedRequest =
  refl

yangMillsFieldEquationReceiptSelectedFieldStrengthTransportCandidate :
  YMObs.YMSFGCSelectedOperatorSkeleton.selectedFieldStrengthTransportCandidate
    (YangMillsFieldEquationReceipt.selectedOperatorSkeleton
      canonicalYangMillsFieldEquationReceipt)
  ≡
  YMObs.canonicalYMSFGCSelectedFieldStrengthAdjointTransportCandidate
yangMillsFieldEquationReceiptSelectedFieldStrengthTransportCandidate =
  refl

yangMillsFieldEquationReceiptFlatConnectionExteriorExtensionWitness :
  YMObs.YMSFGCSelectedOperatorSkeleton.flatConnectionExteriorExtensionWitness
    (YangMillsFieldEquationReceipt.selectedOperatorSkeleton
      canonicalYangMillsFieldEquationReceipt)
  ≡
  YMObs.canonicalYMSFGCFlatConnectionExteriorExtensionWitness
yangMillsFieldEquationReceiptFlatConnectionExteriorExtensionWitness =
  refl

yangMillsFieldEquationReceiptCurvatureQuadraticDensityProxy :
  YMObs.YMSFGCSelectedOperatorSkeleton.curvatureQuadraticDensityProxy
    (YangMillsFieldEquationReceipt.selectedOperatorSkeleton
      canonicalYangMillsFieldEquationReceipt)
  ≡
  YMObs.canonicalYMSFGCCurvatureQuadraticDensityProxy
yangMillsFieldEquationReceiptCurvatureQuadraticDensityProxy =
  refl

yangMillsFieldEquationReceiptExactMissingPrerequisites :
  YangMillsFieldEquationReceipt.exactMissingPrerequisites
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYangMillsFieldEquationMissingPrerequisites
yangMillsFieldEquationReceiptExactMissingPrerequisites = refl

yangMillsFieldEquationReceiptBianchiMissingPrimitives :
  YangMillsFieldEquationReceipt.bianchiMissingPrimitives
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYangMillsBianchiMissingPrimitives
yangMillsFieldEquationReceiptBianchiMissingPrimitives = refl

yangMillsFieldEquationReceiptSelectedCovariantDerivativeMissingPrimitives :
  YangMillsFieldEquationReceipt.selectedCovariantDerivativeMissingPrimitives
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives
yangMillsFieldEquationReceiptSelectedCovariantDerivativeMissingPrimitives =
  refl

yangMillsFieldEquationReceiptSelectedExteriorDerivativeSquaredZeroWitness :
  YangMillsFieldEquationReceipt.selectedExteriorDerivativeSquaredZeroWitness
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness
yangMillsFieldEquationReceiptSelectedExteriorDerivativeSquaredZeroWitness =
  refl

yangMillsFieldEquationReceiptVariationalEquationMissingPrimitives :
  YangMillsFieldEquationReceipt.variationalEquationMissingPrimitives
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYangMillsVariationalEquationMissingPrimitives
yangMillsFieldEquationReceiptVariationalEquationMissingPrimitives =
  refl

yangMillsFieldEquationReceiptActionFunctionalMissingPrimitives :
  YangMillsFieldEquationReceipt.actionFunctionalMissingPrimitives
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.canonicalYMSFGCActionFunctionalMissingPrimitives
yangMillsFieldEquationReceiptActionFunctionalMissingPrimitives =
  refl

yangMillsFieldEquationReceiptUpstreamAPIFirstMissing :
  YangMillsFieldEquationReceipt.upstreamCurvatureAPIFirstMissing
    canonicalYangMillsFieldEquationReceipt
  ≡
  G2DCC.missingShiftGaugeFieldGaugeConnection
yangMillsFieldEquationReceiptUpstreamAPIFirstMissing = refl

yangMillsFieldEquationReceiptYangMillsPromotionFalse :
  YangMillsFieldEquationReceipt.yangMillsClosurePromoted
    canonicalYangMillsFieldEquationReceipt
  ≡
  false
yangMillsFieldEquationReceiptYangMillsPromotionFalse = refl

yangMillsFieldEquationPromoted :
  Bool
yangMillsFieldEquationPromoted =
  false

yangMillsFieldEquationPromotedIsFalse :
  yangMillsFieldEquationPromoted ≡ false
yangMillsFieldEquationPromotedIsFalse =
  refl

yangMillsFieldEquationReceiptMaxwellPromotionFalse :
  YangMillsFieldEquationReceipt.maxwellClosurePromoted
    canonicalYangMillsFieldEquationReceipt
  ≡
  false
yangMillsFieldEquationReceiptMaxwellPromotionFalse = refl

yangMillsFieldEquationReceiptSpectralPromotionFalse :
  YangMillsFieldEquationReceipt.spectralGapPromoted
    canonicalYangMillsFieldEquationReceipt
  ≡
  false
yangMillsFieldEquationReceiptSpectralPromotionFalse = refl

yangMillsFieldEquationReceiptClayPromotionFalse :
  YangMillsFieldEquationReceipt.continuumClayMassGapPromoted
    canonicalYangMillsFieldEquationReceipt
  ≡
  false
yangMillsFieldEquationReceiptClayPromotionFalse = refl

yangMillsFieldEquationReceiptTerminalPromotionFalse :
  YangMillsFieldEquationReceipt.terminalClaimPromoted
    canonicalYangMillsFieldEquationReceipt
  ≡
  false
yangMillsFieldEquationReceiptTerminalPromotionFalse = refl

record NonAbelianCovariantDerivativeCarrier : Set₁ where
  field
    FibreCarrier :
      Set

    connOneForm :
      SFGC.GaugeField →
      FibreCarrier

    discreteDiff :
      FibreCarrier →
      FibreCarrier

    curvature :
      SFGC.GaugeField →
      FibreCarrier

    bracket :
      FibreCarrier →
      FibreCarrier →
      FibreCarrier

    add :
      FibreCarrier →
      FibreCarrier →
      FibreCarrier

    DA :
      SFGC.GaugeField →
      FibreCarrier →
      FibreCarrier

    DA-def :
      (A : SFGC.GaugeField) →
      (section : FibreCarrier) →
      DA A section
      ≡
      add
        (discreteDiff section)
        (bracket (connOneForm A) section)

    DA²-obligation :
      (A : SFGC.GaugeField) →
      (section : FibreCarrier) →
      DA A (DA A section)
      ≡
      bracket (curvature A) section

    strictRealSU3Promoted :
      Bool

    strictRealSU3PromotedIsFalse :
      strictRealSU3Promoted ≡ false

    carrierBoundary :
      List String

canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier :
  NonAbelianCovariantDerivativeCarrier
canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier =
  record
    { FibreCarrier =
        YMObs.YMSFGCLocalFiniteLie3Carrier
    ; connOneForm =
        YMObs.YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.connectionOneFormAsFibreAlgebra
          YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
    ; discreteDiff =
        YMObs.YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.exteriorDerivative
          YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
    ; curvature =
        YMObs.YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.curvatureAsFibreAlgebra
          YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
    ; bracket =
        YMObs.localFiniteLie3Bracket
    ; add =
        YMObs.localFiniteLie3JacobiAdd
    ; DA =
        YMObs.YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.covariantDerivative
          YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
    ; DA-def =
        YMObs.YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.covariantDerivativeFormula
          YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
    ; DA²-obligation =
        YMObs.YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.curvatureActionTheorem
          YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
    ; strictRealSU3Promoted =
        false
    ; strictRealSU3PromotedIsFalse =
        refl
    ; carrierBoundary =
        "NonAbelianCovariantDerivativeCarrier is inhabited only by the local finite Lie3 primitive supply"
        ∷ "connOneForm is the finite local connectionOneFormAsFibreAlgebra probe, not a user-supplied real SU3 connection one-form"
        ∷ "discreteDiff, DA, DA-def, and DA^2-obligation are recorded from the local finite primitive supply"
        ∷ "Strict real SU3 promotion remains false until real non-flat curvature, selected real Lie algebra, field-strength transport, and Hodge variation pairing are inhabited"
        ∷ []
    }

localFiniteNonAbelianCarrierConnOneFormIsPrimitive :
  NonAbelianCovariantDerivativeCarrier.connOneForm
    canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier
  ≡
  YMObs.YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.connectionOneFormAsFibreAlgebra
    YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
localFiniteNonAbelianCarrierConnOneFormIsPrimitive =
  refl

localFiniteNonAbelianCarrierDiscreteDiffIsPrimitive :
  NonAbelianCovariantDerivativeCarrier.discreteDiff
    canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier
  ≡
  YMObs.YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.exteriorDerivative
    YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
localFiniteNonAbelianCarrierDiscreteDiffIsPrimitive =
  refl

localFiniteNonAbelianCarrierDAIsPrimitive :
  NonAbelianCovariantDerivativeCarrier.DA
    canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier
  ≡
  YMObs.YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.covariantDerivative
    YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
localFiniteNonAbelianCarrierDAIsPrimitive =
  refl

localFiniteNonAbelianCarrierDADefIsPrimitive :
  NonAbelianCovariantDerivativeCarrier.DA-def
    canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier
  ≡
  YMObs.YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.covariantDerivativeFormula
    YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
localFiniteNonAbelianCarrierDADefIsPrimitive =
  refl

localFiniteNonAbelianCarrierDA²ObligationIsPrimitive :
  NonAbelianCovariantDerivativeCarrier.DA²-obligation
    canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier
  ≡
  YMObs.YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.curvatureActionTheorem
    YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
localFiniteNonAbelianCarrierDA²ObligationIsPrimitive =
  refl

------------------------------------------------------------------------
-- u2 / Gate 3 real SU3 fibre and covariant derivative attempt.
--
-- This section is intentionally narrow.  It records exactly what can be
-- consumed in the current workspace and where the requested real SU3 handoff
-- stops.  The only inhabited connection-one-form and D_A^2 surfaces available
-- here are the local finite Lie3 probes in YMObs.  The strict user-supplied
-- non-flat connection carrier now has an SFGC-backed adapter; the real Lie,
-- holonomy, transport, and variation laws are still request surfaces in
-- YangMillsFieldEquationObstruction.

data YMSFGCU2RealSU3CovariantDerivativeAttemptStatus : Set where
  blockedByMissingM1RealFibreData :
    YMSFGCU2RealSU3CovariantDerivativeAttemptStatus

record YMSFGCU2RealSU3CovariantDerivativeAttemptReceipt : Set₁ where
  field
    status :
      YMSFGCU2RealSU3CovariantDerivativeAttemptStatus

    consumedLocalConnectionOneFormReceipt :
      YMObs.YMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt

    consumedLocalConnectionOneFormReceiptIsCanonical :
      consumedLocalConnectionOneFormReceipt
      ≡
      YMObs.canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt

    localConnectionOneFormIsFiniteLie3PhaseMap :
      YMObs.YMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt.connectionOneFormAsFibreAlgebra
        consumedLocalConnectionOneFormReceipt
      ≡
      YMObs.sfgcSelectedConnectionOneFormAsLocalFiniteLie3

    consumedLocalNonAbelianDerivativeSupply :
      YMObs.YMSFGCNonAbelianCovariantDerivativePrimitiveSupply

    consumedLocalNonAbelianDerivativeSupplyIsFiniteLie3 :
      consumedLocalNonAbelianDerivativeSupply
      ≡
      YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply

    localDASquaredBracketLaw :
      (A : SFGC.GaugeField) →
      (section : YMObs.YMSFGCLocalFiniteLie3Carrier) →
      YMObs.localFiniteLie3DA0Form
        A
        (YMObs.localFiniteLie3DA0Form A (YMObs.lieValued0 section))
      ≡
      YMObs.localFiniteLie3CurvatureBracketActionOn0Form
        (YMObs.localFiniteLie3FA2Form A)
        (YMObs.lieValued0 section)

    localDASquaredBracketLawIsCanonical :
      localDASquaredBracketLaw
      ≡
      YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms

    nonAbelianCovariantDerivativeCarrier :
      NonAbelianCovariantDerivativeCarrier

    nonAbelianCovariantDerivativeCarrierIsLocalFinite :
      nonAbelianCovariantDerivativeCarrier
      ≡
      canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier

    strictConnectionOneFormTargetType :
      Set

    strictConnectionOneFormTargetTypeIsUserSupplied :
      strictConnectionOneFormTargetType
      ≡
      (YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
       YMObs.YMSFGCUserSuppliedLieAlgebraCarrier)

    strictCovariantDerivativeTargetType :
      Set

    strictCovariantDerivativeTargetTypeIsUserSupplied :
      strictCovariantDerivativeTargetType
      ≡
      (YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
       YMObs.YMSFGCUserSuppliedLieAlgebraCarrier →
       YMObs.YMSFGCUserSuppliedLieAlgebraCarrier)

    firstM1CurvatureBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstM1CurvatureBlockerIsExact :
      firstM1CurvatureBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    firstM1LieCarrierBlocker :
      YMObs.YMSFGCRealKillingAdInvarianceIrreducibility

    firstM1LieCarrierBlockerIsExact :
      firstM1LieCarrierBlocker
      ≡
      YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    firstGaugeCovarianceBlocker :
      YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    firstGaugeCovarianceBlockerIsTransportAction :
      firstGaugeCovarianceBlocker
      ≡
      YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    firstM2HandoffBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    firstM2HandoffBlockerIsVariationPairing :
      firstM2HandoffBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    emptyPatternRouteRejected :
      Bool

    emptyPatternRouteRejectedIsTrue :
      emptyPatternRouteRejected ≡ true

    nonAbelianCovariantDerivativePromoted :
      Bool

    nonAbelianCovariantDerivativePromotedIsFalse :
      nonAbelianCovariantDerivativePromoted ≡ false

    m2HandoffPromoted :
      Bool

    m2HandoffPromotedIsFalse :
      m2HandoffPromoted ≡ false

    attemptBoundary :
      List String

canonicalYMSFGCU2RealSU3CovariantDerivativeAttemptReceipt :
  YMSFGCU2RealSU3CovariantDerivativeAttemptReceipt
canonicalYMSFGCU2RealSU3CovariantDerivativeAttemptReceipt =
  record
    { status =
        blockedByMissingM1RealFibreData
    ; consumedLocalConnectionOneFormReceipt =
        YMObs.canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt
    ; consumedLocalConnectionOneFormReceiptIsCanonical =
        refl
    ; localConnectionOneFormIsFiniteLie3PhaseMap =
        refl
    ; consumedLocalNonAbelianDerivativeSupply =
        YMObs.canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
    ; consumedLocalNonAbelianDerivativeSupplyIsFiniteLie3 =
        refl
    ; localDASquaredBracketLaw =
        YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms
    ; localDASquaredBracketLawIsCanonical =
        refl
    ; nonAbelianCovariantDerivativeCarrier =
        canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier
    ; nonAbelianCovariantDerivativeCarrierIsLocalFinite =
        refl
    ; strictConnectionOneFormTargetType =
        YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMObs.YMSFGCUserSuppliedLieAlgebraCarrier
    ; strictConnectionOneFormTargetTypeIsUserSupplied =
        refl
    ; strictCovariantDerivativeTargetType =
        YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMObs.YMSFGCUserSuppliedLieAlgebraCarrier →
        YMObs.YMSFGCUserSuppliedLieAlgebraCarrier
    ; strictCovariantDerivativeTargetTypeIsUserSupplied =
        refl
    ; firstM1CurvatureBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; firstM1CurvatureBlockerIsExact =
        refl
    ; firstM1LieCarrierBlocker =
        YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; firstM1LieCarrierBlockerIsExact =
        refl
    ; firstGaugeCovarianceBlocker =
        YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; firstGaugeCovarianceBlockerIsTransportAction =
        refl
    ; firstM2HandoffBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; firstM2HandoffBlockerIsVariationPairing =
        refl
    ; emptyPatternRouteRejected =
        true
    ; emptyPatternRouteRejectedIsTrue =
        refl
    ; nonAbelianCovariantDerivativePromoted =
        false
    ; nonAbelianCovariantDerivativePromotedIsFalse =
        refl
    ; m2HandoffPromoted =
        false
    ; m2HandoffPromotedIsFalse =
        refl
    ; attemptBoundary =
        "u2 consumed the existing local connectionOneFormAsFibreAlgebra receipt and the local finite Lie3 D_A^2=[F_A,_] law"
        ∷ "The receipt-local NonAbelianCovariantDerivativeCarrier records connOneForm, discreteDiff, DA, DA-def, and DA^2-obligation from that local finite supply"
        ∷ "Those terms are not a real SU3 proof: the strict connectionOneForm target is from the user-supplied non-flat connection carrier to the user-supplied Lie algebra carrier"
        ∷ "The strict non-flat connection, dual-curvature/current, variation, and action-scalar carriers now have finite wrappers; physical holonomy, Lie algebra transport, and nontrivial selected action variation remain request surfaces"
        ∷ "Gauge covariance still needs a field-strength transport action on the selected gauge bundle"
        ∷ "m2 handoff remains blocked until missingVariationPairingForSelectedHodgeStar is inhabited"
        ∷ []
    }

yangMillsU2AttemptFirstM1CurvatureBlockerIsExact :
  YMSFGCU2RealSU3CovariantDerivativeAttemptReceipt.firstM1CurvatureBlocker
    canonicalYMSFGCU2RealSU3CovariantDerivativeAttemptReceipt
  ≡
  YMObs.missingNonFlatSFGCSite2DConnectionCurvature
yangMillsU2AttemptFirstM1CurvatureBlockerIsExact =
  refl

yangMillsU2AttemptFirstM1LieCarrierBlockerIsExact :
  YMSFGCU2RealSU3CovariantDerivativeAttemptReceipt.firstM1LieCarrierBlocker
    canonicalYMSFGCU2RealSU3CovariantDerivativeAttemptReceipt
  ≡
  YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
yangMillsU2AttemptFirstM1LieCarrierBlockerIsExact =
  refl

yangMillsU2AttemptGaugeCovarianceBlockerIsTransport :
  YMSFGCU2RealSU3CovariantDerivativeAttemptReceipt.firstGaugeCovarianceBlocker
    canonicalYMSFGCU2RealSU3CovariantDerivativeAttemptReceipt
  ≡
  YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
yangMillsU2AttemptGaugeCovarianceBlockerIsTransport =
  refl

yangMillsU2AttemptM2HandoffBlockerIsVariationPairing :
  YMSFGCU2RealSU3CovariantDerivativeAttemptReceipt.firstM2HandoffBlocker
    canonicalYMSFGCU2RealSU3CovariantDerivativeAttemptReceipt
  ≡
  YMObs.missingVariationPairingForSelectedHodgeStar
yangMillsU2AttemptM2HandoffBlockerIsVariationPairing =
  refl

yangMillsU2AttemptNonAbelianPromotionFalse :
  YMSFGCU2RealSU3CovariantDerivativeAttemptReceipt.nonAbelianCovariantDerivativePromoted
    canonicalYMSFGCU2RealSU3CovariantDerivativeAttemptReceipt
  ≡
  false
yangMillsU2AttemptNonAbelianPromotionFalse =
  refl

data YMSFGCU2Upper6SU3FibreConnectionLiftAuditStatus : Set where
  upper6SU3FibreConnectionLiftAuditFailClosed :
    YMSFGCU2Upper6SU3FibreConnectionLiftAuditStatus

record YMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface : Set₁ where
  field
    status :
      YMSFGCU2Upper6SU3FibreConnectionLiftAuditStatus

    consumedU2AttemptReceipt :
      YMSFGCU2RealSU3CovariantDerivativeAttemptReceipt

    consumedU2AttemptReceiptIsCanonical :
      consumedU2AttemptReceipt
      ≡
      canonicalYMSFGCU2RealSU3CovariantDerivativeAttemptReceipt

    consumedLocalFiniteCarrier :
      NonAbelianCovariantDerivativeCarrier

    consumedLocalFiniteCarrierIsCanonical :
      consumedLocalFiniteCarrier
      ≡
      canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier

    SU3FibreConnectionLift :
      SFGC.GaugeField →
      NonAbelianCovariantDerivativeCarrier.FibreCarrier
        consumedLocalFiniteCarrier

    SU3FibreConnectionLiftIsLocalFiniteConnOneForm :
      SU3FibreConnectionLift
      ≡
      NonAbelianCovariantDerivativeCarrier.connOneForm
        consumedLocalFiniteCarrier

    strictSU3FibreConnectionLiftTargetType :
      Set

    strictSU3FibreConnectionLiftTargetTypeIsUserSupplied :
      strictSU3FibreConnectionLiftTargetType
      ≡
      (YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
       YMObs.YMSFGCUserSuppliedLieAlgebraCarrier)

    fieldStrengthTransportAuditCandidate :
      YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    fieldStrengthTransportAuditCandidateIsMissingSelectedBundleAction :
      fieldStrengthTransportAuditCandidate
      ≡
      YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    fieldStrengthTransportStrictTargetType :
      Set

    fieldStrengthTransportStrictTargetTypeIsSelectedBundleAction :
      fieldStrengthTransportStrictTargetType
      ≡
      (SFGC.SFGCSite2DEdge →
       SFGC.SFGCSite2DFieldStrengthBridge →
       SFGC.SFGCSite2DFieldStrengthBridge)

    DA²Audit :
      (A : SFGC.GaugeField) →
      (section :
        NonAbelianCovariantDerivativeCarrier.FibreCarrier
          consumedLocalFiniteCarrier) →
      NonAbelianCovariantDerivativeCarrier.DA
        consumedLocalFiniteCarrier
        A
        (NonAbelianCovariantDerivativeCarrier.DA
          consumedLocalFiniteCarrier
          A
          section)
      ≡
      NonAbelianCovariantDerivativeCarrier.bracket
        consumedLocalFiniteCarrier
        (NonAbelianCovariantDerivativeCarrier.curvature
          consumedLocalFiniteCarrier
          A)
        section

    DA²AuditIsLocalFiniteCarrierObligation :
      DA²Audit
      ≡
      NonAbelianCovariantDerivativeCarrier.DA²-obligation
        consumedLocalFiniteCarrier

    m1CurvatureDependency :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    m1CurvatureDependencyIsMissingNonFlatSFGCSite2DConnectionCurvature :
      m1CurvatureDependency
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    selectedLieAlgebraDependency :
      YMObs.YMSFGCRealKillingAdInvarianceIrreducibility

    selectedLieAlgebraDependencyIsMissingLieAlgebraCarrier :
      selectedLieAlgebraDependency
      ≡
      YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    strictRealSU3FibreLiftPromoted :
      Bool

    strictRealSU3FibreLiftPromotedIsFalse :
      strictRealSU3FibreLiftPromoted ≡ false

    strictFieldStrengthTransportPromoted :
      Bool

    strictFieldStrengthTransportPromotedIsFalse :
      strictFieldStrengthTransportPromoted ≡ false

    strictDA²Promoted :
      Bool

    strictDA²PromotedIsFalse :
      strictDA²Promoted ≡ false

    auditBoundary :
      List String

canonicalYMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface :
  YMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface
canonicalYMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface =
  record
    { status =
        upper6SU3FibreConnectionLiftAuditFailClosed
    ; consumedU2AttemptReceipt =
        canonicalYMSFGCU2RealSU3CovariantDerivativeAttemptReceipt
    ; consumedU2AttemptReceiptIsCanonical =
        refl
    ; consumedLocalFiniteCarrier =
        canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier
    ; consumedLocalFiniteCarrierIsCanonical =
        refl
    ; SU3FibreConnectionLift =
        NonAbelianCovariantDerivativeCarrier.connOneForm
          canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier
    ; SU3FibreConnectionLiftIsLocalFiniteConnOneForm =
        refl
    ; strictSU3FibreConnectionLiftTargetType =
        YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMObs.YMSFGCUserSuppliedLieAlgebraCarrier
    ; strictSU3FibreConnectionLiftTargetTypeIsUserSupplied =
        refl
    ; fieldStrengthTransportAuditCandidate =
        YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; fieldStrengthTransportAuditCandidateIsMissingSelectedBundleAction =
        refl
    ; fieldStrengthTransportStrictTargetType =
        SFGC.SFGCSite2DEdge →
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; fieldStrengthTransportStrictTargetTypeIsSelectedBundleAction =
        refl
    ; DA²Audit =
        NonAbelianCovariantDerivativeCarrier.DA²-obligation
          canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier
    ; DA²AuditIsLocalFiniteCarrierObligation =
        refl
    ; m1CurvatureDependency =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; m1CurvatureDependencyIsMissingNonFlatSFGCSite2DConnectionCurvature =
        refl
    ; selectedLieAlgebraDependency =
        YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; selectedLieAlgebraDependencyIsMissingLieAlgebraCarrier =
        refl
    ; strictRealSU3FibreLiftPromoted =
        false
    ; strictRealSU3FibreLiftPromotedIsFalse =
        refl
    ; strictFieldStrengthTransportPromoted =
        false
    ; strictFieldStrengthTransportPromotedIsFalse =
        refl
    ; strictDA²Promoted =
        false
    ; strictDA²PromotedIsFalse =
        refl
    ; auditBoundary =
        "upper6 u2 audit consumes canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier for SU3FibreConnectionLift and DA^2 only as a local finite carrier"
        ∷ "fieldStrengthTransport is recorded as the selected gauge-bundle action blocker missingFieldStrengthTransportActionOnSelectedGaugeBundle"
        ∷ "Strict real SU3 fibre semantics remain fail-closed at missingNonFlatSFGCSite2DConnectionCurvature and missingLieAlgebraCarrierForSelectedFiniteGaugeSector"
        ∷ "No real SU3 fibre lift, real field-strength transport action, or strict covariant derivative square theorem is promoted"
        ∷ []
    }

yangMillsU2Upper6SU3FibreConnectionLiftAuditNonPromoting :
  YMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface.strictRealSU3FibreLiftPromoted
    canonicalYMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface
  ≡
  false
yangMillsU2Upper6SU3FibreConnectionLiftAuditNonPromoting =
  refl

yangMillsU2Upper6FieldStrengthTransportAuditBlockerIsExact :
  YMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface.fieldStrengthTransportAuditCandidate
    canonicalYMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface
  ≡
  YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
yangMillsU2Upper6FieldStrengthTransportAuditBlockerIsExact =
  refl

yangMillsU2Upper6M1CurvatureDependencyIsExact :
  YMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface.m1CurvatureDependency
    canonicalYMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface
  ≡
  YMObs.missingNonFlatSFGCSite2DConnectionCurvature
yangMillsU2Upper6M1CurvatureDependencyIsExact =
  refl

yangMillsU2Upper6LieAlgebraDependencyIsExact :
  YMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface.selectedLieAlgebraDependency
    canonicalYMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface
  ≡
  YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
yangMillsU2Upper6LieAlgebraDependencyIsExact =
  refl

data YMSFGCU2Upper6BoundedDASquaredReceiptStatus : Set where
  upper6BoundedDASquaredReceiptFiniteOnly :
    YMSFGCU2Upper6BoundedDASquaredReceiptStatus

record YMSFGCU2Upper6BoundedDASquaredReceipt : Set₁ where
  field
    status :
      YMSFGCU2Upper6BoundedDASquaredReceiptStatus

    consumedUpper6Audit :
      YMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface

    consumedUpper6AuditIsCanonical :
      consumedUpper6Audit
      ≡
      canonicalYMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface

    boundedLocalFiniteCarrier :
      NonAbelianCovariantDerivativeCarrier

    boundedLocalFiniteCarrierIsCanonical :
      boundedLocalFiniteCarrier
      ≡
      canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier

    carrierDASquaredReceipt :
      (A : SFGC.GaugeField) →
      (section :
        NonAbelianCovariantDerivativeCarrier.FibreCarrier
          boundedLocalFiniteCarrier) →
      NonAbelianCovariantDerivativeCarrier.DA
        boundedLocalFiniteCarrier
        A
        (NonAbelianCovariantDerivativeCarrier.DA
          boundedLocalFiniteCarrier
          A
          section)
      ≡
      NonAbelianCovariantDerivativeCarrier.bracket
        boundedLocalFiniteCarrier
        (NonAbelianCovariantDerivativeCarrier.curvature
          boundedLocalFiniteCarrier
          A)
        section

    carrierDASquaredReceiptIsCarrierObligation :
      carrierDASquaredReceipt
      ≡
      NonAbelianCovariantDerivativeCarrier.DA²-obligation
        boundedLocalFiniteCarrier

    localFiniteDASquaredBracketLaw :
      (A : SFGC.GaugeField) →
      (section : YMObs.YMSFGCLocalFiniteLie3Carrier) →
      YMObs.localFiniteLie3DA0Form
        A
        (YMObs.localFiniteLie3DA0Form A (YMObs.lieValued0 section))
      ≡
      YMObs.localFiniteLie3CurvatureBracketActionOn0Form
        (YMObs.localFiniteLie3FA2Form A)
        (YMObs.lieValued0 section)

    localFiniteDASquaredBracketLawIsCanonical :
      localFiniteDASquaredBracketLaw
      ≡
      YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms

    upper6OnlyBounded :
      Bool

    upper6OnlyBoundedIsTrue :
      upper6OnlyBounded ≡ true

    m1RealNonFlatCurvatureWaitsOn :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    m1RealNonFlatCurvatureWaitsOnIsExact :
      m1RealNonFlatCurvatureWaitsOn
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    selectedLieAlgebraWaitsOn :
      YMObs.YMSFGCRealKillingAdInvarianceIrreducibility

    selectedLieAlgebraWaitsOnIsExact :
      selectedLieAlgebraWaitsOn
      ≡
      YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    strictRealSU3Promoted :
      Bool

    strictRealSU3PromotedIsFalse :
      strictRealSU3Promoted ≡ false

    receiptBoundary :
      List String

canonicalYMSFGCU2Upper6BoundedDASquaredReceipt :
  YMSFGCU2Upper6BoundedDASquaredReceipt
canonicalYMSFGCU2Upper6BoundedDASquaredReceipt =
  record
    { status =
        upper6BoundedDASquaredReceiptFiniteOnly
    ; consumedUpper6Audit =
        canonicalYMSFGCU2Upper6SU3FibreConnectionLiftAuditSurface
    ; consumedUpper6AuditIsCanonical =
        refl
    ; boundedLocalFiniteCarrier =
        canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier
    ; boundedLocalFiniteCarrierIsCanonical =
        refl
    ; carrierDASquaredReceipt =
        NonAbelianCovariantDerivativeCarrier.DA²-obligation
          canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier
    ; carrierDASquaredReceiptIsCarrierObligation =
        refl
    ; localFiniteDASquaredBracketLaw =
        YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms
    ; localFiniteDASquaredBracketLawIsCanonical =
        refl
    ; upper6OnlyBounded =
        true
    ; upper6OnlyBoundedIsTrue =
        refl
    ; m1RealNonFlatCurvatureWaitsOn =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; m1RealNonFlatCurvatureWaitsOnIsExact =
        refl
    ; selectedLieAlgebraWaitsOn =
        YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; selectedLieAlgebraWaitsOnIsExact =
        refl
    ; strictRealSU3Promoted =
        false
    ; strictRealSU3PromotedIsFalse =
        refl
    ; receiptBoundary =
        "upper6-only bounded D_A^2 receipt consumes the existing NonAbelianCovariantDerivativeCarrier and its DA^2-obligation"
        ∷ "The finite law is exactly localFiniteLie3DASquaredEqualsBracketFAOn0Forms over the local finite Lie3 carrier"
        ∷ "This is only a bounded finite receipt for D_A^2 s = [F_A,s], not a real SU3 promotion"
        ∷ "Strict real SU3 still waits on m1 real non-flat curvature and the selected Lie algebra carrier"
        ∷ []
    }

yangMillsU2Upper6BoundedDASquaredReceiptNonPromoting :
  YMSFGCU2Upper6BoundedDASquaredReceipt.strictRealSU3Promoted
    canonicalYMSFGCU2Upper6BoundedDASquaredReceipt
  ≡
  false
yangMillsU2Upper6BoundedDASquaredReceiptNonPromoting =
  refl

yangMillsU2Upper6BoundedDASquaredReceiptLocalLawIsCanonical :
  YMSFGCU2Upper6BoundedDASquaredReceipt.localFiniteDASquaredBracketLaw
    canonicalYMSFGCU2Upper6BoundedDASquaredReceipt
  ≡
  YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms
yangMillsU2Upper6BoundedDASquaredReceiptLocalLawIsCanonical =
  refl

yangMillsU2Upper6BoundedDASquaredReceiptM1CurvatureWaitsOnExact :
  YMSFGCU2Upper6BoundedDASquaredReceipt.m1RealNonFlatCurvatureWaitsOn
    canonicalYMSFGCU2Upper6BoundedDASquaredReceipt
  ≡
  YMObs.missingNonFlatSFGCSite2DConnectionCurvature
yangMillsU2Upper6BoundedDASquaredReceiptM1CurvatureWaitsOnExact =
  refl

yangMillsU2Upper6BoundedDASquaredReceiptSelectedLieAlgebraWaitsOnExact :
  YMSFGCU2Upper6BoundedDASquaredReceipt.selectedLieAlgebraWaitsOn
    canonicalYMSFGCU2Upper6BoundedDASquaredReceipt
  ≡
  YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
yangMillsU2Upper6BoundedDASquaredReceiptSelectedLieAlgebraWaitsOnExact =
  refl

record YMSFGCGate3M1M2U2FailClosedReceipt : Set₁ where
  field
    lower6M1M2U2ConsolidatedHandoff :
      YMObs.YMSFGCLower6M1M2U2ConsolidatedHandoffReceipt

    lower6M1M2U2ConsolidatedHandoffIsCanonical :
      lower6M1M2U2ConsolidatedHandoff
      ≡
      YMObs.canonicalYMSFGCLower6M1M2U2ConsolidatedHandoffReceipt

    finiteSU3LikeCarrierRoute :
      YMObs.YMSFGCSU3JacobiGlobalCarrierRouteReceipt

    finiteSU3LikeCarrierRouteIsCanonical :
      finiteSU3LikeCarrierRoute
      ≡
      YMObs.canonicalYMSFGCSU3JacobiGlobalCarrierRouteReceipt

    nontrivialAdjointTracePairingSupply :
      YMObs.YMSFGCLieAlgebraTraceAdInvariancePrimitiveSupply

    nontrivialAdjointTracePairingSupplyIsFiniteC4 :
      nontrivialAdjointTracePairingSupply
      ≡
      YMObs.canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply

    gate3Wave3StrictPromotionDecision :
      YMObs.YMSFGCGate3Wave3StrictPromotionDecisionReceipt

    gate3Wave3StrictPromotionDecisionIsCanonical :
      gate3Wave3StrictPromotionDecision
      ≡
      YMObs.canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt

    routeBU2ConsumerStaging :
      YMSFGCGate3RouteBU2ConsumerStaging

    routeBU2ConsumerStagingIsCanonical :
      routeBU2ConsumerStaging
      ≡
      canonicalYMSFGCGate3RouteBU2ConsumerStaging

    routeBHodgeCurrentSurface :
      YMSFGCRouteBLowerHodgeCurrentSurface

    routeBHodgeCurrentSurfaceIsCanonical :
      routeBHodgeCurrentSurface
      ≡
      canonicalYMSFGCRouteBLowerHodgeCurrentSurface

    m1NonFlatCurvatureWitnessIsReference :
      YMObs.YMSFGCLower6M1M2U2ConsolidatedHandoffReceipt.m1ReferenceNonFlatCurvatureAtReference
        lower6M1M2U2ConsolidatedHandoff
      ≡
      YMObs.sfgcReferenceNonFlatCurvatureAtReference

    m1FieldStrengthWitnessIsReference :
      YMObs.YMSFGCLower6M1M2U2ConsolidatedHandoffReceipt.m1ReferenceFieldStrengthAtReference
        lower6M1M2U2ConsolidatedHandoff
      ≡
      YMObs.sfgcReferenceNonFlatFieldStrengthAtReference

    m2HodgeCandidateIsIdentityProbe :
      YMObs.YMSFGCLower6M1M2U2ConsolidatedHandoffReceipt.m2HodgeStarLowerCandidate
        lower6M1M2U2ConsolidatedHandoff
      ≡
      YMObs.sfgcSelectedHodgeStarLowerCandidate

    m2IBPCandidateIsZeroLowerCandidate :
      YMObs.YMSFGCLower6M1M2U2ConsolidatedHandoffReceipt.m2ZeroVariationIBPLowerCandidate
        lower6M1M2U2ConsolidatedHandoff
      ≡
      YMObs.canonicalYMSFGCDiscreteVariationIBPLowerCandidate

    firstStrictSU3GlobalCarrierBlocker :
      YMObs.YMSFGCLocalFiniteSU3MissingPrimitive

    firstStrictSU3GlobalCarrierBlockerIsFibreRepresentation :
      firstStrictSU3GlobalCarrierBlocker
      ≡
      YMObs.missingSFGCFibreRepresentationIntoSU3Carrier

    firstStrictNonFlatHolonomyBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictNonFlatHolonomyBlockerIsCurvature :
      firstStrictNonFlatHolonomyBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    firstStrictTransportBlocker :
      YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    firstStrictTransportBlockerIsFieldStrengthAction :
      firstStrictTransportBlocker
      ≡
      YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    firstStrictRouteBBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    firstStrictRouteBBlockerIsVariationPairing :
      firstStrictRouteBBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    gate3TranchePromoted :
      Bool

    gate3TranchePromotedIsFalse :
      gate3TranchePromoted ≡ false

    failClosedBoundary :
      List String

canonicalYMSFGCGate3M1M2U2FailClosedReceipt :
  YMSFGCGate3M1M2U2FailClosedReceipt
canonicalYMSFGCGate3M1M2U2FailClosedReceipt =
  record
    { lower6M1M2U2ConsolidatedHandoff =
        YMObs.canonicalYMSFGCLower6M1M2U2ConsolidatedHandoffReceipt
    ; lower6M1M2U2ConsolidatedHandoffIsCanonical =
        refl
    ; finiteSU3LikeCarrierRoute =
        YMObs.canonicalYMSFGCSU3JacobiGlobalCarrierRouteReceipt
    ; finiteSU3LikeCarrierRouteIsCanonical =
        refl
    ; nontrivialAdjointTracePairingSupply =
        YMObs.canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply
    ; nontrivialAdjointTracePairingSupplyIsFiniteC4 =
        refl
    ; gate3Wave3StrictPromotionDecision =
        YMObs.canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt
    ; gate3Wave3StrictPromotionDecisionIsCanonical =
        refl
    ; routeBU2ConsumerStaging =
        canonicalYMSFGCGate3RouteBU2ConsumerStaging
    ; routeBU2ConsumerStagingIsCanonical =
        refl
    ; routeBHodgeCurrentSurface =
        canonicalYMSFGCRouteBLowerHodgeCurrentSurface
    ; routeBHodgeCurrentSurfaceIsCanonical =
        refl
    ; m1NonFlatCurvatureWitnessIsReference =
        refl
    ; m1FieldStrengthWitnessIsReference =
        refl
    ; m2HodgeCandidateIsIdentityProbe =
        refl
    ; m2IBPCandidateIsZeroLowerCandidate =
        refl
    ; firstStrictSU3GlobalCarrierBlocker =
        YMObs.missingSFGCFibreRepresentationIntoSU3Carrier
    ; firstStrictSU3GlobalCarrierBlockerIsFibreRepresentation =
        refl
    ; firstStrictNonFlatHolonomyBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; firstStrictNonFlatHolonomyBlockerIsCurvature =
        refl
    ; firstStrictTransportBlocker =
        YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; firstStrictTransportBlockerIsFieldStrengthAction =
        refl
    ; firstStrictRouteBBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; firstStrictRouteBBlockerIsVariationPairing =
        refl
    ; gate3TranchePromoted =
        false
    ; gate3TranchePromotedIsFalse =
        refl
    ; failClosedBoundary =
        "Gate 3 m1/m2/u2 receipt consumes finite SU(3)-like route staging, finite C4 trace/adjoint invariance, reference non-flat curvature, covariant-derivative handoff, and lower Hodge/current/IBP surfaces"
        ∷ "Inhabited content remains finite and lower: m1 has a reference φ1 plaquette curvature witness, u2 has local finite Lie/SU3-like scaffolding, and m2 has identity Hodge plus zero-variation IBP candidates"
        ∷ "Fail-closed blockers are exact: missingSFGCFibreRepresentationIntoSU3Carrier, missingNonFlatSFGCSite2DConnectionCurvature, missingFieldStrengthTransportActionOnSelectedGaugeBundle, and missingVariationPairingForSelectedHodgeStar"
        ∷ "No real Yang-Mills D * F = J, covariant D F = 0, metric Hodge star, matter current coupling, or integration-by-parts variational theorem is promoted here"
        ∷ []
    }

yangMillsGate3M1M2U2FailClosedReceiptIsNonPromoting :
  YMSFGCGate3M1M2U2FailClosedReceipt.gate3TranchePromoted
    canonicalYMSFGCGate3M1M2U2FailClosedReceipt
  ≡
  false
yangMillsGate3M1M2U2FailClosedReceiptIsNonPromoting =
  refl

------------------------------------------------------------------------
-- lower6 next-wave u1/u2/m1/m2 receipt surfaces.
--
-- These receipts are deliberately separate from the main field-equation
-- receipt so the existing canonical consumer remains stable.  They name the
-- requested gauge-orbit quotient and Hamiltonian shapes, the SU3 fibre-lift
-- handoff shape, and the m1/m2 finite arithmetic attempts added on the
-- obstruction side.  They do not inhabit the strict real Yang-Mills blockers.

data U1GaugeOrbitQuotientHamiltonianAttemptStatus : Set where
  u1GaugeOrbitQuotientHamiltonianAttemptFailClosed :
    U1GaugeOrbitQuotientHamiltonianAttemptStatus

record U1GaugeOrbitQuotientHamiltonianShapeReceipt : Set₂ where
  field
    status :
      U1GaugeOrbitQuotientHamiltonianAttemptStatus

    ymConnectionCarrier :
      Set

    ymConnectionCarrierIsUserSuppliedNonFlat :
      ymConnectionCarrier
      ≡
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier

    gaugeTransformationCarrier :
      Set

    gaugeTransformationCarrierIsSiteToLieCarrier :
      gaugeTransformationCarrier
      ≡
      (SFGC.SFGCSite2D →
       YMObs.YMSFGCUserSuppliedLieAlgebraCarrier)

    gaugeOrbitRelationType :
      Set₁

    gaugeOrbitRelationTypeIsBinaryRelationOnConnections :
      gaugeOrbitRelationType
      ≡
      (YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
       YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
       Set)

    quotientCarrierTargetType :
      Set₁

    quotientCarrierTargetTypeIsGaugeOrbitQuotient :
      quotientCarrierTargetType
      ≡
      Set

    quotientNormTarget :
      Nat

    quotientNormTargetIsZeroPlaceholder :
      quotientNormTarget ≡ zero

    laplacianActionTargetType :
      Set₁

    laplacianActionTargetTypeIsQuotientEndomap :
      laplacianActionTargetType
      ≡
      (Set → Set)

    plaquettePotentialTargetType :
      Set₁

    plaquettePotentialTargetTypeIsQuotientToNat :
      plaquettePotentialTargetType
      ≡
      (Set → Nat)

    hamiltonianActionTargetType :
      Set₁

    hamiltonianActionTargetTypeIsQuotientEndomap :
      hamiltonianActionTargetType
      ≡
      (Set → Set)

    symmetryAttemptStaged :
      Bool

    symmetryAttemptStagedIsTrue :
      symmetryAttemptStaged ≡ true

    friedrichsExtensionRequired :
      Bool

    friedrichsExtensionRequiredIsTrue :
      friedrichsExtensionRequired ≡ true

    realGaugeOrbitQuotientConstructed :
      Bool

    realGaugeOrbitQuotientConstructedIsFalse :
      realGaugeOrbitQuotientConstructed ≡ false

    selfAdjointHamiltonianConstructed :
      Bool

    selfAdjointHamiltonianConstructedIsFalse :
      selfAdjointHamiltonianConstructed ≡ false

    exactSelfAdjointBlocker :
      YMSFGCM1FiniteCarrierHardExternalHalt

    exactSelfAdjointBlockerIsUniformBalabanOrAgawa :
      exactSelfAdjointBlocker
      ≡
      uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    quotientBoundary :
      List String

canonicalU1GaugeOrbitQuotientHamiltonianShapeReceipt :
  U1GaugeOrbitQuotientHamiltonianShapeReceipt
canonicalU1GaugeOrbitQuotientHamiltonianShapeReceipt =
  record
    { status =
        u1GaugeOrbitQuotientHamiltonianAttemptFailClosed
    ; ymConnectionCarrier =
        YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; ymConnectionCarrierIsUserSuppliedNonFlat =
        refl
    ; gaugeTransformationCarrier =
        SFGC.SFGCSite2D →
        YMObs.YMSFGCUserSuppliedLieAlgebraCarrier
    ; gaugeTransformationCarrierIsSiteToLieCarrier =
        refl
    ; gaugeOrbitRelationType =
        YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
        Set
    ; gaugeOrbitRelationTypeIsBinaryRelationOnConnections =
        refl
    ; quotientCarrierTargetType =
        Set
    ; quotientCarrierTargetTypeIsGaugeOrbitQuotient =
        refl
    ; quotientNormTarget =
        zero
    ; quotientNormTargetIsZeroPlaceholder =
        refl
    ; laplacianActionTargetType =
        Set → Set
    ; laplacianActionTargetTypeIsQuotientEndomap =
        refl
    ; plaquettePotentialTargetType =
        Set → Nat
    ; plaquettePotentialTargetTypeIsQuotientToNat =
        refl
    ; hamiltonianActionTargetType =
        Set → Set
    ; hamiltonianActionTargetTypeIsQuotientEndomap =
        refl
    ; symmetryAttemptStaged =
        true
    ; symmetryAttemptStagedIsTrue =
        refl
    ; friedrichsExtensionRequired =
        true
    ; friedrichsExtensionRequiredIsTrue =
        refl
    ; realGaugeOrbitQuotientConstructed =
        false
    ; realGaugeOrbitQuotientConstructedIsFalse =
        refl
    ; selfAdjointHamiltonianConstructed =
        false
    ; selfAdjointHamiltonianConstructedIsFalse =
        refl
    ; exactSelfAdjointBlocker =
        uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; exactSelfAdjointBlockerIsUniformBalabanOrAgawa =
        refl
    ; quotientBoundary =
        "u1 next-wave shape names YMConnectionCarrier modulo gauge orbit as a binary relation on the user-supplied non-flat connection carrier"
        ∷ "The quotient norm, connection Laplacian, plaquette potential, and H_YM = -Delta_A + V_YM action are only target shapes here"
        ∷ "Symmetry is staged as the plaquette-hermiticity route, but no dense domain or Friedrichs extension proof is supplied"
        ∷ "The real gauge-orbit quotient and SelfAdjointYangMillsHamiltonianOnCarrierQuotient remain unconstructed"
        ∷ []
    }

data U2SU3FibreLiftTransportAttemptStatus : Set where
  u2SU3FibreLiftTransportAttemptBlockedByM1 :
    U2SU3FibreLiftTransportAttemptStatus

record U2SU3FibreLiftTransportStageReceipt : Set₁ where
  field
    status :
      U2SU3FibreLiftTransportAttemptStatus

    m1FiniteArithmeticAttempt :
      YMObs.YMSFGCNextWaveFiniteSU3NonFlatCurvatureArithmeticAttemptReceipt

    m1FiniteArithmeticAttemptIsCanonical :
      m1FiniteArithmeticAttempt
      ≡
      YMObs.canonicalYMSFGCNextWaveFiniteSU3NonFlatCurvatureArithmeticAttemptReceipt

    localFiniteNonAbelianCarrier :
      NonAbelianCovariantDerivativeCarrier

    localFiniteNonAbelianCarrierIsCanonical :
      localFiniteNonAbelianCarrier
      ≡
      canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier

    fibreConnectionLiftTargetType :
      Set

    fibreConnectionLiftTargetTypeIsUserSuppliedConnectionToLie :
      fibreConnectionLiftTargetType
      ≡
      (YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
       YMObs.YMSFGCUserSuppliedLieAlgebraCarrier)

    holonomyTransportLawTargetType :
      Set

    holonomyTransportLawTargetTypeIsUserSuppliedHolonomyLaw :
      holonomyTransportLawTargetType
      ≡
      YMObs.YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedHolonomyConjugationLawType
        YMObs.canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    daSquaredBracketLocalLaw :
      (A : SFGC.GaugeField) →
      (section : YMObs.YMSFGCLocalFiniteLie3Carrier) →
      YMObs.localFiniteLie3DA0Form
        A
        (YMObs.localFiniteLie3DA0Form A (YMObs.lieValued0 section))
      ≡
      YMObs.localFiniteLie3CurvatureBracketActionOn0Form
        (YMObs.localFiniteLie3FA2Form A)
        (YMObs.lieValued0 section)

    daSquaredBracketLocalLawIsCanonical :
      daSquaredBracketLocalLaw
      ≡
      YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms

    fieldStrengthTransportBlocker :
      YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    fieldStrengthTransportBlockerIsExact :
      fieldStrengthTransportBlocker
      ≡
      YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    strictFibreLiftPromoted :
      Bool

    strictFibreLiftPromotedIsFalse :
      strictFibreLiftPromoted ≡ false

    stageBoundary :
      List String

canonicalU2SU3FibreLiftTransportStageReceipt :
  U2SU3FibreLiftTransportStageReceipt
canonicalU2SU3FibreLiftTransportStageReceipt =
  record
    { status =
        u2SU3FibreLiftTransportAttemptBlockedByM1
    ; m1FiniteArithmeticAttempt =
        YMObs.canonicalYMSFGCNextWaveFiniteSU3NonFlatCurvatureArithmeticAttemptReceipt
    ; m1FiniteArithmeticAttemptIsCanonical =
        refl
    ; localFiniteNonAbelianCarrier =
        canonicalLocalFiniteNonAbelianCovariantDerivativeCarrier
    ; localFiniteNonAbelianCarrierIsCanonical =
        refl
    ; fibreConnectionLiftTargetType =
        YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMObs.YMSFGCUserSuppliedLieAlgebraCarrier
    ; fibreConnectionLiftTargetTypeIsUserSuppliedConnectionToLie =
        refl
    ; holonomyTransportLawTargetType =
        YMObs.YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedHolonomyConjugationLawType
          YMObs.canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; holonomyTransportLawTargetTypeIsUserSuppliedHolonomyLaw =
        refl
    ; daSquaredBracketLocalLaw =
        YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms
    ; daSquaredBracketLocalLawIsCanonical =
        refl
    ; fieldStrengthTransportBlocker =
        YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; fieldStrengthTransportBlockerIsExact =
        refl
    ; strictFibreLiftPromoted =
        false
    ; strictFibreLiftPromotedIsFalse =
        refl
    ; stageBoundary =
        "u2 next-wave fibre lift consumes only the finite m1 arithmetic attempt and local finite D_A^2=[F_A,_] law"
        ∷ "The requested fibre lift remains a map from the user-supplied non-flat connection carrier into the user-supplied Lie carrier"
        ∷ "Holonomy transport/gauge covariance remains the user-supplied holonomy conjugation law target"
        ∷ "missingFieldStrengthTransportActionOnSelectedGaugeBundle remains the exact transport blocker"
        ∷ []
    }

record YMSFGCNextWaveYMWorkerReceipt : Set₂ where
  field
    u1GaugeOrbitQuotientHamiltonian :
      U1GaugeOrbitQuotientHamiltonianShapeReceipt

    u1GaugeOrbitQuotientHamiltonianIsCanonical :
      u1GaugeOrbitQuotientHamiltonian
      ≡
      canonicalU1GaugeOrbitQuotientHamiltonianShapeReceipt

    u2SU3FibreLiftTransport :
      U2SU3FibreLiftTransportStageReceipt

    u2SU3FibreLiftTransportIsCanonical :
      u2SU3FibreLiftTransport
      ≡
      canonicalU2SU3FibreLiftTransportStageReceipt

    m1FiniteSU3CurvatureArithmetic :
      YMObs.YMSFGCNextWaveFiniteSU3NonFlatCurvatureArithmeticAttemptReceipt

    m1FiniteSU3CurvatureArithmeticIsCanonical :
      m1FiniteSU3CurvatureArithmetic
      ≡
      YMObs.canonicalYMSFGCNextWaveFiniteSU3NonFlatCurvatureArithmeticAttemptReceipt

    m2HodgeEpsilonAssistance :
      YMObs.YMSFGCNextWaveHodgeEpsilonContractionAssistanceReceipt

    m2HodgeEpsilonAssistanceIsCanonical :
      m2HodgeEpsilonAssistance
      ≡
      YMObs.canonicalYMSFGCNextWaveHodgeEpsilonContractionAssistanceReceipt

    firstNonFlatCurvatureBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstNonFlatCurvatureBlockerIsExact :
      firstNonFlatCurvatureBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    firstVariationPairingBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    firstVariationPairingBlockerIsExact :
      firstVariationPairingBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    continuumClayPromoted :
      Bool

    continuumClayPromotedIsFalse :
      continuumClayPromoted ≡ false

    workerPromoted :
      Bool

    workerPromotedIsFalse :
      workerPromoted ≡ false

    workerBoundary :
      List String

canonicalYMSFGCNextWaveYMWorkerReceipt :
  YMSFGCNextWaveYMWorkerReceipt
canonicalYMSFGCNextWaveYMWorkerReceipt =
  record
    { u1GaugeOrbitQuotientHamiltonian =
        canonicalU1GaugeOrbitQuotientHamiltonianShapeReceipt
    ; u1GaugeOrbitQuotientHamiltonianIsCanonical =
        refl
    ; u2SU3FibreLiftTransport =
        canonicalU2SU3FibreLiftTransportStageReceipt
    ; u2SU3FibreLiftTransportIsCanonical =
        refl
    ; m1FiniteSU3CurvatureArithmetic =
        YMObs.canonicalYMSFGCNextWaveFiniteSU3NonFlatCurvatureArithmeticAttemptReceipt
    ; m1FiniteSU3CurvatureArithmeticIsCanonical =
        refl
    ; m2HodgeEpsilonAssistance =
        YMObs.canonicalYMSFGCNextWaveHodgeEpsilonContractionAssistanceReceipt
    ; m2HodgeEpsilonAssistanceIsCanonical =
        refl
    ; firstNonFlatCurvatureBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; firstNonFlatCurvatureBlockerIsExact =
        refl
    ; firstVariationPairingBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; firstVariationPairingBlockerIsExact =
        refl
    ; continuumClayPromoted =
        false
    ; continuumClayPromotedIsFalse =
        refl
    ; workerPromoted =
        false
    ; workerPromotedIsFalse =
        refl
    ; workerBoundary =
        "lower6 YM next-wave worker records u1 gauge-orbit quotient/Hamiltonian shape, u2 SU3 fibre-lift stage, m1 finite SU3 curvature arithmetic, and m2 epsilon assistance"
        ∷ "All four lanes are fail-closed: no real quotient, no self-adjoint H_YM, no promoted non-flat holonomy theorem, no selected Hodge variation pairing"
        ∷ "Continuum Clay, Yang-Mills closure, spectral-gap, and terminal promotion remain false"
        ∷ []
    }

yangMillsNextWaveYMWorkerReceiptIsNonPromoting :
  YMSFGCNextWaveYMWorkerReceipt.workerPromoted
    canonicalYMSFGCNextWaveYMWorkerReceipt
  ≡
  false
yangMillsNextWaveYMWorkerReceiptIsNonPromoting =
  refl

data YMSFGCGate3GenuineFirstMissingFailClosedStatus : Set where
  gate3GenuineFirstMissingFiniteOnlyStrictBlocked :
    YMSFGCGate3GenuineFirstMissingFailClosedStatus

record YMSFGCGate3GenuineFirstMissingFailClosedReceipt : Set₁ where
  field
    status :
      YMSFGCGate3GenuineFirstMissingFailClosedStatus

    finiteArithmeticResiduals :
      YMObs.YMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals

    finiteArithmeticResidualsAreCanonical :
      finiteArithmeticResiduals
      ≡
      YMObs.canonicalYMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals

    m1WilsonLoopQuarterTurnWitness :
      SFGC.sfgcSite2DEvaluate2
        YMObs.sfgcReferenceNonFlatCurvature2Form
        YMObs.sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    m1WilsonLoopQuarterTurnWitnessIsCanonical :
      m1WilsonLoopQuarterTurnWitness
      ≡
      YMObs.sfgcReferenceNonFlatCurvatureAtReference

    m1WilsonLoopNotVacuumResidual :
      SFGC.sfgcSite2DEvaluate2
        YMObs.sfgcReferenceNonFlatCurvature2Form
        YMObs.sfgcReferencePlaquette
      ≡
      SPTI4.φ0 →
      YMObs.YMSFGCEmpty

    m1WilsonLoopNotVacuumResidualIsCanonical :
      m1WilsonLoopNotVacuumResidual
      ≡
      YMObs.sfgcReferenceNonFlatCurvatureAtReferenceNotVacuum

    finiteCrossProductAntisymmetryResidual :
      (x y : YMObs.YMSFGCLocalFiniteLie3Carrier) →
      YMObs.localFiniteLie3Bracket x y
      ≡
      YMObs.localFiniteLie3Neg (YMObs.localFiniteLie3Bracket y x)

    finiteCrossProductAntisymmetryResidualIsCanonical :
      finiteCrossProductAntisymmetryResidual
      ≡
      YMObs.localFiniteLie3BracketAntisymmetry

    finiteCrossProductJacobiResidual :
      (x y z : YMObs.YMSFGCLocalFiniteLie3Carrier) →
      YMObs.localFiniteLie3JacobiAdd
        (YMObs.localFiniteLie3JacobiAdd
          (YMObs.localFiniteLie3Bracket x (YMObs.localFiniteLie3Bracket y z))
          (YMObs.localFiniteLie3Bracket y (YMObs.localFiniteLie3Bracket z x)))
        (YMObs.localFiniteLie3Bracket z (YMObs.localFiniteLie3Bracket x y))
      ≡
      YMObs.lieZero

    finiteCrossProductJacobiResidualIsCanonical :
      finiteCrossProductJacobiResidual
      ≡
      YMObs.localFiniteLie3JacobiWitness

    finiteEpsilonContractionResidual :
      YMObs.localFiniteLie3EpsilonContractionShape

    finiteEpsilonContractionResidualIsCanonical :
      finiteEpsilonContractionResidual
      ≡
      YMObs.localFiniteLie3PositiveAxisJacobi

    u2LocalDACurvatureActionResidual :
      (A : SFGC.GaugeField) →
      (section : YMObs.YMSFGCLocalFiniteLie3Carrier) →
      YMObs.localFiniteLie3DA0Form
        A
        (YMObs.localFiniteLie3DA0Form A (YMObs.lieValued0 section))
      ≡
      YMObs.localFiniteLie3CurvatureBracketActionOn0Form
        (YMObs.localFiniteLie3FA2Form A)
        (YMObs.lieValued0 section)

    u2LocalDACurvatureActionResidualIsCanonical :
      u2LocalDACurvatureActionResidual
      ≡
      YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms

    m2HodgeResidualIsIdentityProbe :
      YMObs.sfgcSelectedHodgeStarLowerCandidate
      ≡
      routeBSelectedHodgeStar

    exactFirstCurvatureBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    exactFirstCurvatureBlockerIsNonFlatCurvature :
      exactFirstCurvatureBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    exactFirstTransportBlocker :
      YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    exactFirstTransportBlockerIsFieldStrengthAction :
      exactFirstTransportBlocker
      ≡
      YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    exactFirstHodgeActionBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    exactFirstHodgeActionBlockerIsVariationPairing :
      exactFirstHodgeActionBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    strictPromotion :
      Bool

    strictPromotionIsFalse :
      strictPromotion ≡ false

    failClosedBoundary :
      List String

canonicalYMSFGCGate3GenuineFirstMissingFailClosedReceipt :
  YMSFGCGate3GenuineFirstMissingFailClosedReceipt
canonicalYMSFGCGate3GenuineFirstMissingFailClosedReceipt =
  record
    { status =
        gate3GenuineFirstMissingFiniteOnlyStrictBlocked
    ; finiteArithmeticResiduals =
        YMObs.canonicalYMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals
    ; finiteArithmeticResidualsAreCanonical =
        refl
    ; m1WilsonLoopQuarterTurnWitness =
        YMObs.sfgcReferenceNonFlatCurvatureAtReference
    ; m1WilsonLoopQuarterTurnWitnessIsCanonical =
        refl
    ; m1WilsonLoopNotVacuumResidual =
        YMObs.sfgcReferenceNonFlatCurvatureAtReferenceNotVacuum
    ; m1WilsonLoopNotVacuumResidualIsCanonical =
        refl
    ; finiteCrossProductAntisymmetryResidual =
        YMObs.localFiniteLie3BracketAntisymmetry
    ; finiteCrossProductAntisymmetryResidualIsCanonical =
        refl
    ; finiteCrossProductJacobiResidual =
        YMObs.localFiniteLie3JacobiWitness
    ; finiteCrossProductJacobiResidualIsCanonical =
        refl
    ; finiteEpsilonContractionResidual =
        YMObs.localFiniteLie3PositiveAxisJacobi
    ; finiteEpsilonContractionResidualIsCanonical =
        refl
    ; u2LocalDACurvatureActionResidual =
        YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms
    ; u2LocalDACurvatureActionResidualIsCanonical =
        refl
    ; m2HodgeResidualIsIdentityProbe =
        refl
    ; exactFirstCurvatureBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; exactFirstCurvatureBlockerIsNonFlatCurvature =
        refl
    ; exactFirstTransportBlocker =
        YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; exactFirstTransportBlockerIsFieldStrengthAction =
        refl
    ; exactFirstHodgeActionBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; exactFirstHodgeActionBlockerIsVariationPairing =
        refl
    ; strictPromotion =
        false
    ; strictPromotionIsFalse =
        refl
    ; failClosedBoundary =
        "Gate3 genuine first-missing receipt consumes the obstruction-side finite arithmetic residual bundle"
        ∷ "m1 has only the reference finite Site2D non-flat witness: Wilson-loop curvature is φ1 at sfgcReferencePlaquette and not φ0"
        ∷ "u2 has only local finite Lie3/SU3-like arithmetic: cross-product antisymmetry, Jacobi, epsilon-contraction, and D_A^2=[F_A,_] as lower residuals"
        ∷ "m2 has only the identity selected-Hodge probe, not a metric Hodge star or variation pairing"
        ∷ "Strict promotion is false because SFGC/SFGS still lack the real non-flat connection carrier/action section, real field-strength transport action, selected real Hodge/current/action APIs, and variation pairing"
        ∷ []
    }

yangMillsGate3GenuineFirstMissingFailClosedReceiptStrictPromotionFalse :
  YMSFGCGate3GenuineFirstMissingFailClosedReceipt.strictPromotion
    canonicalYMSFGCGate3GenuineFirstMissingFailClosedReceipt
  ≡
  false
yangMillsGate3GenuineFirstMissingFailClosedReceiptStrictPromotionFalse =
  refl

yangMillsGate3GenuineFirstMissingFailClosedReceiptNonFlatBlockerIsExact :
  YMSFGCGate3GenuineFirstMissingFailClosedReceipt.exactFirstCurvatureBlocker
    canonicalYMSFGCGate3GenuineFirstMissingFailClosedReceipt
  ≡
  YMObs.missingNonFlatSFGCSite2DConnectionCurvature
yangMillsGate3GenuineFirstMissingFailClosedReceiptNonFlatBlockerIsExact =
  refl

------------------------------------------------------------------------
-- lower6 YM/u1/u2/m1/m2/l6 current-wave receipt handoff.

data YMSFGCCurrentWaveYMWorkerHandoffStatus : Set where
  currentWaveYMWorkerFiniteArithmeticIntegratedFailClosed :
    YMSFGCCurrentWaveYMWorkerHandoffStatus

record YMSFGCCurrentWaveYMWorkerHandoffReceipt : Set₁ where
  field
    status :
      YMSFGCCurrentWaveYMWorkerHandoffStatus

    obstructionWorkerReceipt :
      YMObs.YMSFGCCurrentWaveYMFiniteWorkerReceipt

    obstructionWorkerReceiptIsCanonical :
      obstructionWorkerReceipt
      ≡
      YMObs.canonicalYMSFGCCurrentWaveYMFiniteWorkerReceipt

    u1DoubledChristoffelCoordination :
      YMObs.YMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt

    u1DoubledChristoffelCoordinationIsCanonical :
      u1DoubledChristoffelCoordination
      ≡
      YMObs.canonicalYMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt

    u1SelectedGRMetricHookAvailable :
      Bool

    u1SelectedGRMetricHookAvailableIsFalse :
      u1SelectedGRMetricHookAvailable ≡ false

    u2FiniteDASquaredComputation :
      YMObs.YMSFGCCurrentWaveFiniteDACurvatureComputationReceipt

    u2FiniteDASquaredComputationIsCanonical :
      u2FiniteDASquaredComputation
      ≡
      YMObs.canonicalYMSFGCCurrentWaveFiniteDACurvatureComputationReceipt

    m1FiniteAdditiveWilsonLoop :
      YMObs.YMSFGCCurrentWaveFiniteAdditiveWilsonLoopReceipt

    m1FiniteAdditiveWilsonLoopIsCanonical :
      m1FiniteAdditiveWilsonLoop
      ≡
      YMObs.canonicalYMSFGCCurrentWaveFiniteAdditiveWilsonLoopReceipt

    m2l6HodgeEpsilonAssistance :
      YMObs.YMSFGCCurrentWaveHodgeEpsilonAssistanceReceipt

    m2l6HodgeEpsilonAssistanceIsCanonical :
      m2l6HodgeEpsilonAssistance
      ≡
      YMObs.canonicalYMSFGCCurrentWaveHodgeEpsilonAssistanceReceipt

    retainedNonFlatCurvatureBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    retainedNonFlatCurvatureBlockerIsExact :
      retainedNonFlatCurvatureBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    retainedLieCarrierBlocker :
      YMObs.YMSFGCRealKillingAdInvarianceIrreducibility

    retainedLieCarrierBlockerIsExact :
      retainedLieCarrierBlocker
      ≡
      YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    retainedTransportBlocker :
      YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    retainedTransportBlockerIsExact :
      retainedTransportBlocker
      ≡
      YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    retainedVariationPairingBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    retainedVariationPairingBlockerIsExact :
      retainedVariationPairingBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    strictRealYMPromoted :
      Bool

    strictRealYMPromotedIsFalse :
      strictRealYMPromoted ≡ false

    handoffBoundary :
      List String

canonicalYMSFGCCurrentWaveYMWorkerHandoffReceipt :
  YMSFGCCurrentWaveYMWorkerHandoffReceipt
canonicalYMSFGCCurrentWaveYMWorkerHandoffReceipt =
  record
    { status =
        currentWaveYMWorkerFiniteArithmeticIntegratedFailClosed
    ; obstructionWorkerReceipt =
        YMObs.canonicalYMSFGCCurrentWaveYMFiniteWorkerReceipt
    ; obstructionWorkerReceiptIsCanonical =
        refl
    ; u1DoubledChristoffelCoordination =
        YMObs.canonicalYMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt
    ; u1DoubledChristoffelCoordinationIsCanonical =
        refl
    ; u1SelectedGRMetricHookAvailable =
        YMObs.YMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt.selectedGRMetricHookAvailableInYMFile
          YMObs.canonicalYMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt
    ; u1SelectedGRMetricHookAvailableIsFalse =
        YMObs.YMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt.selectedGRMetricHookAvailableInYMFileIsFalse
          YMObs.canonicalYMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt
    ; u2FiniteDASquaredComputation =
        YMObs.canonicalYMSFGCCurrentWaveFiniteDACurvatureComputationReceipt
    ; u2FiniteDASquaredComputationIsCanonical =
        refl
    ; m1FiniteAdditiveWilsonLoop =
        YMObs.canonicalYMSFGCCurrentWaveFiniteAdditiveWilsonLoopReceipt
    ; m1FiniteAdditiveWilsonLoopIsCanonical =
        refl
    ; m2l6HodgeEpsilonAssistance =
        YMObs.canonicalYMSFGCCurrentWaveHodgeEpsilonAssistanceReceipt
    ; m2l6HodgeEpsilonAssistanceIsCanonical =
        refl
    ; retainedNonFlatCurvatureBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; retainedNonFlatCurvatureBlockerIsExact =
        refl
    ; retainedLieCarrierBlocker =
        YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; retainedLieCarrierBlockerIsExact =
        refl
    ; retainedTransportBlocker =
        YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; retainedTransportBlockerIsExact =
        refl
    ; retainedVariationPairingBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; retainedVariationPairingBlockerIsExact =
        refl
    ; strictRealYMPromoted =
        false
    ; strictRealYMPromotedIsFalse =
        refl
    ; handoffBoundary =
        "current YM worker handoff consumes the obstruction-side finite bundle for u1/u2/m1/m2/l6"
        ∷ "u1 Christoffel coordination records the doubled integral shape only; YM has no selected GR metric hook"
        ∷ "u2 D_A^2=[F_A,_], m1 additive Wilson-loop φ1, and m2/l6 epsilon assistance are local finite receipts"
        ∷ "Strict real carriers, transport, Hodge variation, self-adjoint Hamiltonian, and Clay/continuum promotion remain fail-closed"
        ∷ []
    }

yangMillsCurrentWaveYMWorkerHandoffStrictPromotionFalse :
  YMSFGCCurrentWaveYMWorkerHandoffReceipt.strictRealYMPromoted
    canonicalYMSFGCCurrentWaveYMWorkerHandoffReceipt
  ≡
  false
yangMillsCurrentWaveYMWorkerHandoffStrictPromotionFalse =
  refl

yangMillsCurrentWaveYMWorkerHandoffCurvatureBlockerIsExact :
  YMSFGCCurrentWaveYMWorkerHandoffReceipt.retainedNonFlatCurvatureBlocker
    canonicalYMSFGCCurrentWaveYMWorkerHandoffReceipt
  ≡
  YMObs.missingNonFlatSFGCSite2DConnectionCurvature
yangMillsCurrentWaveYMWorkerHandoffCurvatureBlockerIsExact =
  refl

------------------------------------------------------------------------
-- upper6 u2 m1-consumer handoff.
--
-- This is the narrow u2 contract for the next strict Gate 3 step.  The
-- obstruction-side non-flat connection now has a finite Site2D adapter, while
-- the remaining real carriers are still user-supplied surfaces.  The executable
-- module below is parametrised by the three pieces m1/u2 must eventually
-- provide: the connection one-form into the selected fibre algebra, the
-- holonomy/field-strength transport law, and the strict
-- D_A^2=[F_A,_] curvature-action theorem.  The canonical receipt records the
-- exact types and blockers without promoting real SU3, Hodge, or Route B.

module U2Gate3ConsumeM1
  (connectionOneFormAsFibreAlgebra :
    YMObs.YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedConnectionOneFormInFibreType
      YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest)
  (fieldStrengthTransport :
    YMObs.YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedHolonomyConjugationLawType
      YMObs.canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest)
  (dA²EqualsBracketF :
    YMObs.YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedDASquaredCurvatureActionType
      YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest)
  where

  connectionOneFormAsFibreAlgebraDependency :
    YMObs.YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedConnectionOneFormInFibreType
      YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest
  connectionOneFormAsFibreAlgebraDependency =
    connectionOneFormAsFibreAlgebra

  fieldStrengthTransportDependency :
    YMObs.YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedHolonomyConjugationLawType
      YMObs.canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
  fieldStrengthTransportDependency =
    fieldStrengthTransport

  dA²EqualsBracketFDependency :
    YMObs.YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedDASquaredCurvatureActionType
      YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest
  dA²EqualsBracketFDependency =
    dA²EqualsBracketF

data U2Gate3ConsumeM1ReceiptStatus : Set where
  u2Gate3ConsumeM1ParametricFailClosed :
    U2Gate3ConsumeM1ReceiptStatus

record U2Gate3ConsumeM1Receipt : Set₁ where
  field
    status :
      U2Gate3ConsumeM1ReceiptStatus

    userSuppliedRealYMRequest :
      YMObs.YMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    userSuppliedRealYMRequestIsCanonical :
      userSuppliedRealYMRequest
      ≡
      YMObs.canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    nonAbelianCovariantDerivativeRequest :
      YMObs.YMSFGCNonAbelianCovariantDerivativeTypedRequest

    nonAbelianCovariantDerivativeRequestIsCanonical :
      nonAbelianCovariantDerivativeRequest
      ≡
      YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest

    nonFlatCurvatureInputType :
      Set

    nonFlatCurvatureInputTypeIsUserSuppliedConnection :
      nonFlatCurvatureInputType
      ≡
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier

    selectedLieAlgebraInputType :
      Set

    selectedLieAlgebraInputTypeIsUserSuppliedLieCarrier :
      selectedLieAlgebraInputType
      ≡
      YMObs.YMSFGCUserSuppliedLieAlgebraCarrier

    connectionOneFormAsFibreAlgebraTarget :
      Set

    connectionOneFormAsFibreAlgebraTargetIsRequested :
      connectionOneFormAsFibreAlgebraTarget
      ≡
      YMObs.YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedConnectionOneFormInFibreType
        nonAbelianCovariantDerivativeRequest

    fieldStrengthTransportTarget :
      Set

    fieldStrengthTransportTargetIsHolonomyConjugationLaw :
      fieldStrengthTransportTarget
      ≡
      YMObs.YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedHolonomyConjugationLawType
        userSuppliedRealYMRequest

    dA²EqualsBracketFTarget :
      Set

    dA²EqualsBracketFTargetIsRequestedCurvatureAction :
      dA²EqualsBracketFTarget
      ≡
      YMObs.YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedDASquaredCurvatureActionType
        nonAbelianCovariantDerivativeRequest

    localFiniteDASquaredBracketLaw :
      (A : SFGC.GaugeField) →
      (section : YMObs.YMSFGCLocalFiniteLie3Carrier) →
      YMObs.localFiniteLie3DA0Form
        A
        (YMObs.localFiniteLie3DA0Form A (YMObs.lieValued0 section))
      ≡
      YMObs.localFiniteLie3CurvatureBracketActionOn0Form
        (YMObs.localFiniteLie3FA2Form A)
        (YMObs.lieValued0 section)

    localFiniteDASquaredBracketLawIsCanonical :
      localFiniteDASquaredBracketLaw
      ≡
      YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms

    m1NonFlatCurvatureBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    m1NonFlatCurvatureBlockerIsExact :
      m1NonFlatCurvatureBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    selectedLieAlgebraBlocker :
      YMObs.YMSFGCRealKillingAdInvarianceIrreducibility

    selectedLieAlgebraBlockerIsExact :
      selectedLieAlgebraBlocker
      ≡
      YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    fieldStrengthTransportBlocker :
      YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    fieldStrengthTransportBlockerIsExact :
      fieldStrengthTransportBlocker
      ≡
      YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    strictRealSU3Promoted :
      Bool

    strictRealSU3PromotedIsFalse :
      strictRealSU3Promoted ≡ false

    strictHodgePromoted :
      Bool

    strictHodgePromotedIsFalse :
      strictHodgePromoted ≡ false

    consumeBoundary :
      List String

canonicalU2Gate3ConsumeM1Receipt :
  U2Gate3ConsumeM1Receipt
canonicalU2Gate3ConsumeM1Receipt =
  record
    { status =
        u2Gate3ConsumeM1ParametricFailClosed
    ; userSuppliedRealYMRequest =
        YMObs.canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; userSuppliedRealYMRequestIsCanonical =
        refl
    ; nonAbelianCovariantDerivativeRequest =
        YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest
    ; nonAbelianCovariantDerivativeRequestIsCanonical =
        refl
    ; nonFlatCurvatureInputType =
        YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; nonFlatCurvatureInputTypeIsUserSuppliedConnection =
        refl
    ; selectedLieAlgebraInputType =
        YMObs.YMSFGCUserSuppliedLieAlgebraCarrier
    ; selectedLieAlgebraInputTypeIsUserSuppliedLieCarrier =
        refl
    ; connectionOneFormAsFibreAlgebraTarget =
        YMObs.YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedConnectionOneFormInFibreType
          YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest
    ; connectionOneFormAsFibreAlgebraTargetIsRequested =
        refl
    ; fieldStrengthTransportTarget =
        YMObs.YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedHolonomyConjugationLawType
          YMObs.canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; fieldStrengthTransportTargetIsHolonomyConjugationLaw =
        refl
    ; dA²EqualsBracketFTarget =
        YMObs.YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedDASquaredCurvatureActionType
          YMObs.canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest
    ; dA²EqualsBracketFTargetIsRequestedCurvatureAction =
        refl
    ; localFiniteDASquaredBracketLaw =
        YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms
    ; localFiniteDASquaredBracketLawIsCanonical =
        refl
    ; m1NonFlatCurvatureBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; m1NonFlatCurvatureBlockerIsExact =
        refl
    ; selectedLieAlgebraBlocker =
        YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; selectedLieAlgebraBlockerIsExact =
        refl
    ; fieldStrengthTransportBlocker =
        YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; fieldStrengthTransportBlockerIsExact =
        refl
    ; strictRealSU3Promoted =
        false
    ; strictRealSU3PromotedIsFalse =
        refl
    ; strictHodgePromoted =
        false
    ; strictHodgePromotedIsFalse =
        refl
    ; consumeBoundary =
        "U2Gate3ConsumeM1 is now an explicit parametric handoff: once m1 supplies a user non-flat connection and selected Lie carrier bridge, u2 consumes connectionOneFormAsFibreAlgebra, holonomy conjugation/field-strength transport, and D_A^2=[F_A,_] as requested target types"
        ∷ "The only inhabited theorem here remains the local finite Lie3 D_A^2=[F_A,_] law; the strict real law is a dependency target, not a promotion"
        ∷ "Exact remaining u2 blockers are missingNonFlatSFGCSite2DConnectionCurvature, missingLieAlgebraCarrierForSelectedFiniteGaugeSector, and missingFieldStrengthTransportActionOnSelectedGaugeBundle"
        ∷ "No strict real SU3 fibre representation, selected Hodge star, Hodge variation pairing, or Route B equation is promoted"
        ∷ []
    }

yangMillsU2Gate3ConsumeM1ReceiptStrictRealSU3False :
  U2Gate3ConsumeM1Receipt.strictRealSU3Promoted
    canonicalU2Gate3ConsumeM1Receipt
  ≡
  false
yangMillsU2Gate3ConsumeM1ReceiptStrictRealSU3False =
  refl

yangMillsU2Gate3ConsumeM1ReceiptTransportBlockerIsExact :
  U2Gate3ConsumeM1Receipt.fieldStrengthTransportBlocker
    canonicalU2Gate3ConsumeM1Receipt
  ≡
  YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
yangMillsU2Gate3ConsumeM1ReceiptTransportBlockerIsExact =
  refl

------------------------------------------------------------------------
-- upper6 u2 latest-state instantiation decision.
--
-- The latest obstruction-side wave adds more finite arithmetic, but it still
-- does not provide the three strict inhabitants required to instantiate
-- U2Gate3ConsumeM1: a selected real/user non-flat curvature bridge, selected
-- Lie carrier, and field-strength transport law.  This receipt records that
-- decision boundary while naming the finite laws already ready for handoff.

data U2Gate3LatestInstantiationDecisionStatus : Set where
  u2Gate3LatestInstantiationBlockedNoStrictInputs :
    U2Gate3LatestInstantiationDecisionStatus

record U2Gate3LatestInstantiationDecisionReceipt : Set₁ where
  field
    status :
      U2Gate3LatestInstantiationDecisionStatus

    consumeM1ParametricReceipt :
      U2Gate3ConsumeM1Receipt

    consumeM1ParametricReceiptIsCanonical :
      consumeM1ParametricReceipt
      ≡
      canonicalU2Gate3ConsumeM1Receipt

    latestFiniteAttempt :
      YMObs.YMSFGCLatestFirstMissingConcreteAttemptReceipt

    latestFiniteAttemptIsCanonical :
      latestFiniteAttempt
      ≡
      YMObs.canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt

    finiteDASquaredBracketLawReady :
      (A : SFGC.GaugeField) →
      (section : YMObs.YMSFGCLocalFiniteLie3Carrier) →
      YMObs.localFiniteLie3DA0Form
        A
        (YMObs.localFiniteLie3DA0Form A (YMObs.lieValued0 section))
      ≡
      YMObs.localFiniteLie3CurvatureBracketActionOn0Form
        (YMObs.localFiniteLie3FA2Form A)
        (YMObs.lieValued0 section)

    finiteDASquaredBracketLawReadyIsCanonical :
      finiteDASquaredBracketLawReady
      ≡
      YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms

    m1FiniteWilsonLoopReady :
      SFGC.sfgcSite2DEvaluate2
        (YMObs.YMSFGCLatestFirstMissingConcreteAttemptReceipt.referenceNonFlatWilsonCurvature
          latestFiniteAttempt)
        YMObs.sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    m1FiniteWilsonLoopReadyIsLatestAttemptField :
      m1FiniteWilsonLoopReady
      ≡
      YMObs.YMSFGCLatestFirstMissingConcreteAttemptReceipt.referenceNonFlatWilsonCurvatureAtReference
        latestFiniteAttempt

    m2FiniteHodgeProbeReady :
      YMObs.YMSFGCLatestFirstMissingConcreteAttemptReceipt.m2HodgeLowerCandidate
        latestFiniteAttempt
      ≡
      YMObs.sfgcSelectedHodgeStarLowerCandidate

    m2FiniteHodgeProbeReadyIsLatestAttemptField :
      m2FiniteHodgeProbeReady
      ≡
      YMObs.YMSFGCLatestFirstMissingConcreteAttemptReceipt.m2HodgeLowerCandidateIsIdentity
        latestFiniteAttempt

    m1NonFlatCurvatureStillAbsent :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    m1NonFlatCurvatureStillAbsentIsExact :
      m1NonFlatCurvatureStillAbsent
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    m1SelectedLieCarrierStillAbsent :
      YMObs.YMSFGCRealKillingAdInvarianceIrreducibility

    m1SelectedLieCarrierStillAbsentIsExact :
      m1SelectedLieCarrierStillAbsent
      ≡
      YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    u2FieldStrengthTransportStillAbsent :
      YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    u2FieldStrengthTransportStillAbsentIsExact :
      u2FieldStrengthTransportStillAbsent
      ≡
      YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    m2CurrentSourceStillAbsent :
      YMObs.YangMillsFieldEquationMissingPrerequisite

    m2CurrentSourceStillAbsentIsExact :
      m2CurrentSourceStillAbsent
      ≡
      YMObs.missingCurrentSourceAndCoupling

    m2VariationPairingStillAbsent :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    m2VariationPairingStillAbsentIsExact :
      m2VariationPairingStillAbsent
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    u2ConsumeM1Instantiated :
      Bool

    u2ConsumeM1InstantiatedIsFalse :
      u2ConsumeM1Instantiated ≡ false

    strictRealSU3Promoted :
      Bool

    strictRealSU3PromotedIsFalse :
      strictRealSU3Promoted ≡ false

    strictHodgeOrVariationPromoted :
      Bool

    strictHodgeOrVariationPromotedIsFalse :
      strictHodgeOrVariationPromoted ≡ false

    currentFrontier :
      List String

canonicalU2Gate3LatestInstantiationDecisionReceipt :
  U2Gate3LatestInstantiationDecisionReceipt
canonicalU2Gate3LatestInstantiationDecisionReceipt =
  record
    { status =
        u2Gate3LatestInstantiationBlockedNoStrictInputs
    ; consumeM1ParametricReceipt =
        canonicalU2Gate3ConsumeM1Receipt
    ; consumeM1ParametricReceiptIsCanonical =
        refl
    ; latestFiniteAttempt =
        YMObs.canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt
    ; latestFiniteAttemptIsCanonical =
        refl
    ; finiteDASquaredBracketLawReady =
        YMObs.localFiniteLie3DASquaredEqualsBracketFAOn0Forms
    ; finiteDASquaredBracketLawReadyIsCanonical =
        refl
    ; m1FiniteWilsonLoopReady =
        YMObs.YMSFGCLatestFirstMissingConcreteAttemptReceipt.referenceNonFlatWilsonCurvatureAtReference
          YMObs.canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt
    ; m1FiniteWilsonLoopReadyIsLatestAttemptField =
        refl
    ; m2FiniteHodgeProbeReady =
        YMObs.YMSFGCLatestFirstMissingConcreteAttemptReceipt.m2HodgeLowerCandidateIsIdentity
          YMObs.canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt
    ; m2FiniteHodgeProbeReadyIsLatestAttemptField =
        refl
    ; m1NonFlatCurvatureStillAbsent =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; m1NonFlatCurvatureStillAbsentIsExact =
        refl
    ; m1SelectedLieCarrierStillAbsent =
        YMObs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; m1SelectedLieCarrierStillAbsentIsExact =
        refl
    ; u2FieldStrengthTransportStillAbsent =
        YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; u2FieldStrengthTransportStillAbsentIsExact =
        refl
    ; m2CurrentSourceStillAbsent =
        YMObs.missingCurrentSourceAndCoupling
    ; m2CurrentSourceStillAbsentIsExact =
        refl
    ; m2VariationPairingStillAbsent =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; m2VariationPairingStillAbsentIsExact =
        refl
    ; u2ConsumeM1Instantiated =
        false
    ; u2ConsumeM1InstantiatedIsFalse =
        refl
    ; strictRealSU3Promoted =
        false
    ; strictRealSU3PromotedIsFalse =
        refl
    ; strictHodgeOrVariationPromoted =
        false
    ; strictHodgeOrVariationPromotedIsFalse =
        refl
    ; currentFrontier =
        "U2Gate3ConsumeM1 is not instantiated in the latest state because its strict real inputs are still absent"
        ∷ "Ready internally: localFiniteLie3DASquaredEqualsBracketFAOn0Forms for finite D_A^2=[F_A,_]"
        ∷ "Ready internally: the m1 finite reference Wilson-loop curvature is phi1 on sfgcReferencePlaquette"
        ∷ "Ready internally: the m2 selected Hodge probe is the identity lower candidate"
        ∷ "Still absent from m1: a discharged missingNonFlatSFGCSite2DConnectionCurvature token and missingLieAlgebraCarrierForSelectedFiniteGaugeSector"
        ∷ "Still absent from u2/m2: missingFieldStrengthTransportActionOnSelectedGaugeBundle, missingCurrentSourceAndCoupling, and missingVariationPairingForSelectedHodgeStar"
        ∷ "No strict real SU3, selected Hodge, Route B variation, or Yang-Mills promotion is performed here"
        ∷ []
    }

yangMillsU2Gate3LatestInstantiationDecisionIsBlocked :
  U2Gate3LatestInstantiationDecisionReceipt.u2ConsumeM1Instantiated
    canonicalU2Gate3LatestInstantiationDecisionReceipt
  ≡
  false
yangMillsU2Gate3LatestInstantiationDecisionIsBlocked =
  refl

yangMillsU2Gate3LatestInstantiationDecisionNonFlatBlockerIsExact :
  U2Gate3LatestInstantiationDecisionReceipt.m1NonFlatCurvatureStillAbsent
    canonicalU2Gate3LatestInstantiationDecisionReceipt
  ≡
  YMObs.missingNonFlatSFGCSite2DConnectionCurvature
yangMillsU2Gate3LatestInstantiationDecisionNonFlatBlockerIsExact =
  refl

------------------------------------------------------------------------
-- lower6 YM/u1/u2/m1/m2 wave checkpoint.

data Lower6YMU1U2M1M2WaveCheckpointStatus : Set where
  lower6WaveFiniteReceiptsConsumedStrictPromotionBlocked :
    Lower6YMU1U2M1M2WaveCheckpointStatus

record Lower6YMU1U2M1M2WaveCheckpointReceipt : Set₁ where
  field
    status :
      Lower6YMU1U2M1M2WaveCheckpointStatus

    u1LocalFiniteCarrierSpectralGapAvailable :
      Bool

    u1LocalFiniteCarrierSpectralGapAvailableIsBalabanCanonical :
      u1LocalFiniteCarrierSpectralGapAvailable
      ≡
      YMGap.BalabanRGMassGapReceiptSurface.localFiniteCarrierSpectralGapPromoted
        YMGap.canonicalBalabanRGMassGapReceiptSurface

    u1LocalFiniteCarrierSpectralGapAvailableIsTrue :
      u1LocalFiniteCarrierSpectralGapAvailable ≡ true

    u1ContinuumMassGapPromoted :
      Bool

    u1ContinuumMassGapPromotedIsBalabanCanonical :
      u1ContinuumMassGapPromoted
      ≡
      YMGap.BalabanRGMassGapReceiptSurface.continuumMassGapPromotedByDASHI
        YMGap.canonicalBalabanRGMassGapReceiptSurface

    u1ContinuumMassGapPromotedIsFalse :
      u1ContinuumMassGapPromoted ≡ false

    u2ConsumeM1Decision :
      U2Gate3LatestInstantiationDecisionReceipt

    u2ConsumeM1DecisionIsCanonical :
      u2ConsumeM1Decision
      ≡
      canonicalU2Gate3LatestInstantiationDecisionReceipt

    u2ConsumeM1Instantiated :
      Bool

    u2ConsumeM1InstantiatedIsCanonicalDecision :
      u2ConsumeM1Instantiated
      ≡
      U2Gate3LatestInstantiationDecisionReceipt.u2ConsumeM1Instantiated
        u2ConsumeM1Decision

    u2ConsumeM1InstantiatedIsFalse :
      u2ConsumeM1Instantiated ≡ false

    m1FiniteWilsonLoopReady :
      SFGC.sfgcSite2DEvaluate2
        (YMObs.YMSFGCLatestFirstMissingConcreteAttemptReceipt.referenceNonFlatWilsonCurvature
          YMObs.canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt)
        YMObs.sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    m2FiniteHodgeProbeReady :
      YMObs.YMSFGCLatestFirstMissingConcreteAttemptReceipt.m2HodgeLowerCandidate
        YMObs.canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt
      ≡
      YMObs.sfgcSelectedHodgeStarLowerCandidate

    sfgcStokesBoundaryOfBoundaryWordReady :
      List StokesObs.CRTMonodromy1Edge

    sfgcStokesBoundaryOfBoundaryWordReadyIsEmpty :
      sfgcStokesBoundaryOfBoundaryWordReady ≡ []

    sfgcIBPZeroVariationLawReady :
      (A δA : SFGC.GaugeField) →
      YMObs.sfgcZeroVariationOfAction A δA
        ≡
      _+ℤ_
        (YMObs.sfgcZeroEulerLagrangePairing A δA)
        (YMObs.sfgcZeroBoundaryTerm A δA)

    firstStrictBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictBlockerIsNonFlatCurvature :
      firstStrictBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    strictYangMillsPromoted :
      Bool

    strictYangMillsPromotedIsFalse :
      strictYangMillsPromoted ≡ false

    checkpointBoundary :
      List String

canonicalLower6YMU1U2M1M2WaveCheckpointReceipt :
  Lower6YMU1U2M1M2WaveCheckpointReceipt
canonicalLower6YMU1U2M1M2WaveCheckpointReceipt =
  record
    { status =
        lower6WaveFiniteReceiptsConsumedStrictPromotionBlocked
    ; u1LocalFiniteCarrierSpectralGapAvailable =
        YMGap.BalabanRGMassGapReceiptSurface.localFiniteCarrierSpectralGapPromoted
          YMGap.canonicalBalabanRGMassGapReceiptSurface
    ; u1LocalFiniteCarrierSpectralGapAvailableIsBalabanCanonical =
        refl
    ; u1LocalFiniteCarrierSpectralGapAvailableIsTrue =
        YMGap.BalabanRGMassGapReceiptSurface.localFiniteCarrierSpectralGapPromotedIsTrue
          YMGap.canonicalBalabanRGMassGapReceiptSurface
    ; u1ContinuumMassGapPromoted =
        YMGap.BalabanRGMassGapReceiptSurface.continuumMassGapPromotedByDASHI
          YMGap.canonicalBalabanRGMassGapReceiptSurface
    ; u1ContinuumMassGapPromotedIsBalabanCanonical =
        refl
    ; u1ContinuumMassGapPromotedIsFalse =
        YMGap.BalabanRGMassGapReceiptSurface.continuumMassGapPromotedByDASHIIsFalse
          YMGap.canonicalBalabanRGMassGapReceiptSurface
    ; u2ConsumeM1Decision =
        canonicalU2Gate3LatestInstantiationDecisionReceipt
    ; u2ConsumeM1DecisionIsCanonical =
        refl
    ; u2ConsumeM1Instantiated =
        U2Gate3LatestInstantiationDecisionReceipt.u2ConsumeM1Instantiated
          canonicalU2Gate3LatestInstantiationDecisionReceipt
    ; u2ConsumeM1InstantiatedIsCanonicalDecision =
        refl
    ; u2ConsumeM1InstantiatedIsFalse =
        U2Gate3LatestInstantiationDecisionReceipt.u2ConsumeM1InstantiatedIsFalse
          canonicalU2Gate3LatestInstantiationDecisionReceipt
    ; m1FiniteWilsonLoopReady =
        YMObs.YMSFGCLatestFirstMissingConcreteAttemptReceipt.referenceNonFlatWilsonCurvatureAtReference
          YMObs.canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt
    ; m2FiniteHodgeProbeReady =
        YMObs.YMSFGCLatestFirstMissingConcreteAttemptReceipt.m2HodgeLowerCandidateIsIdentity
          YMObs.canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt
    ; sfgcStokesBoundaryOfBoundaryWordReady =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryOfBoundaryWord
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; sfgcStokesBoundaryOfBoundaryWordReadyIsEmpty =
        refl
    ; sfgcIBPZeroVariationLawReady =
        YMObs.sfgcZeroDiscreteVariationIBPLaw
    ; firstStrictBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; firstStrictBlockerIsNonFlatCurvature =
        refl
    ; strictYangMillsPromoted =
        false
    ; strictYangMillsPromotedIsFalse =
        refl
    ; checkpointBoundary =
        "u1 finite-carrier spectral gap is consumed only as the Balaban local finite-carrier receipt; continuum mass-gap promotion remains false"
        ∷ "m1 finite Wilson-loop curvature at the reference SFGCSite2D plaquette is φ1 and now feeds the user-supplied non-flat connection adapter; strict holonomy and transport laws remain unpromoted"
        ∷ "u2 U2Gate3ConsumeM1 remains uninstantiated because the selected Lie carrier bridge and field-strength transport law are absent beyond the finite Site2D connection adapter"
        ∷ "m2 consumes only the selected identity Hodge probe and the zero discrete variation/IBP law"
        ∷ "SFGC Stokes evidence consumed here is the typed CRT boundary-of-boundary empty word from DiscreteStokesBianchiObstruction"
        ∷ "First strict blocker remains missingNonFlatSFGCSite2DConnectionCurvature; no Yang-Mills, spectral, mass-gap, Clay, or terminal promotion is introduced"
        ∷ []
    }

yangMillsLower6WaveCheckpointStrictPromotionFalse :
  Lower6YMU1U2M1M2WaveCheckpointReceipt.strictYangMillsPromoted
    canonicalLower6YMU1U2M1M2WaveCheckpointReceipt
  ≡
  false
yangMillsLower6WaveCheckpointStrictPromotionFalse =
  refl

yangMillsLower6WaveCheckpointFirstBlockerIsNonFlatCurvature :
  Lower6YMU1U2M1M2WaveCheckpointReceipt.firstStrictBlocker
    canonicalLower6YMU1U2M1M2WaveCheckpointReceipt
  ≡
  YMObs.missingNonFlatSFGCSite2DConnectionCurvature
yangMillsLower6WaveCheckpointFirstBlockerIsNonFlatCurvature =
  refl

------------------------------------------------------------------------
-- l4/u1 finite spectral and Wilson-continuum checkpoint.
--
-- `finiteYMSpectralGap` is intentionally only the finite-depth/local
-- Balaban-carrier flag.  The Wilson receipt is consumed as continuum-limit
-- scoping authority, not as a local continuum Yang-Mills construction or Clay
-- mass-gap proof.

finiteYMSpectralGap :
  Bool
finiteYMSpectralGap =
  YMGap.BalabanRGMassGapReceiptSurface.localFiniteCarrierSpectralGapPromoted
    YMGap.canonicalBalabanRGMassGapReceiptSurface

finiteYMSpectralGapIsLocalFiniteCarrier :
  finiteYMSpectralGap ≡ true
finiteYMSpectralGapIsLocalFiniteCarrier =
  YMGap.BalabanRGMassGapReceiptSurface.localFiniteCarrierSpectralGapPromotedIsTrue
    YMGap.canonicalBalabanRGMassGapReceiptSurface

finiteYMSpectralGapContinuumPromotion :
  Bool
finiteYMSpectralGapContinuumPromotion =
  YMGap.BalabanRGMassGapReceiptSurface.continuumMassGapPromotedByDASHI
    YMGap.canonicalBalabanRGMassGapReceiptSurface

finiteYMSpectralGapContinuumPromotionIsFalse :
  finiteYMSpectralGapContinuumPromotion ≡ false
finiteYMSpectralGapContinuumPromotionIsFalse =
  YMGap.BalabanRGMassGapReceiptSurface.continuumMassGapPromotedByDASHIIsFalse
    YMGap.canonicalBalabanRGMassGapReceiptSurface

data YMSFGCL4WilsonContinuumCheckpointStatus : Set where
  l4WilsonContinuumAuthorityConsumedNoPromotion :
    YMSFGCL4WilsonContinuumCheckpointStatus

record YMSFGCL4WilsonContinuumCheckpointReceipt : Set₁ where
  field
    status :
      YMSFGCL4WilsonContinuumCheckpointStatus

    finiteSpectralGapFlag :
      Bool

    finiteSpectralGapFlagIsFiniteYMSpectralGap :
      finiteSpectralGapFlag ≡ finiteYMSpectralGap

    finiteSpectralGapFlagIsTrue :
      finiteSpectralGapFlag ≡ true

    wilsonContinuumAuthority :
      Clay.Wilson1974ContinuumLimitAuthorityReceipt

    wilsonContinuumAuthorityIsCanonical :
      wilsonContinuumAuthority
      ≡
      Clay.canonicalWilson1974ContinuumLimitAuthorityReceipt

    wilsonLocalContinuumProofSupplied :
      Bool

    wilsonLocalContinuumProofSuppliedIsCanonical :
      wilsonLocalContinuumProofSupplied
      ≡
      Clay.Wilson1974ContinuumLimitAuthorityReceipt.localContinuumProofSupplied
        wilsonContinuumAuthority

    wilsonLocalContinuumProofSuppliedIsFalse :
      wilsonLocalContinuumProofSupplied ≡ false

    lower6Checkpoint :
      Lower6YMU1U2M1M2WaveCheckpointReceipt

    lower6CheckpointIsCanonical :
      lower6Checkpoint
      ≡
      canonicalLower6YMU1U2M1M2WaveCheckpointReceipt

    u2ConsumeM1Decision :
      U2Gate3LatestInstantiationDecisionReceipt

    u2ConsumeM1DecisionIsCanonical :
      u2ConsumeM1Decision
      ≡
      canonicalU2Gate3LatestInstantiationDecisionReceipt

    sfgcStokesBoundaryOfBoundaryWord :
      List StokesObs.CRTMonodromy1Edge

    sfgcStokesBoundaryOfBoundaryWordIsEmpty :
      sfgcStokesBoundaryOfBoundaryWord ≡ []

    sfgcIBPZeroVariationLaw :
      (A δA : SFGC.GaugeField) →
      YMObs.sfgcZeroVariationOfAction A δA
        ≡
      _+ℤ_
        (YMObs.sfgcZeroEulerLagrangePairing A δA)
        (YMObs.sfgcZeroBoundaryTerm A δA)

    firstStrictBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictBlockerIsNonFlatCurvature :
      firstStrictBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ true

    clayOrTerminalPromoted :
      Bool

    clayOrTerminalPromotedIsFalse :
      clayOrTerminalPromoted ≡ false

    checkpointBoundary :
      List String

canonicalYMSFGCL4WilsonContinuumCheckpointReceipt :
  YMSFGCL4WilsonContinuumCheckpointReceipt
canonicalYMSFGCL4WilsonContinuumCheckpointReceipt =
  record
    { status =
        l4WilsonContinuumAuthorityConsumedNoPromotion
    ; finiteSpectralGapFlag =
        finiteYMSpectralGap
    ; finiteSpectralGapFlagIsFiniteYMSpectralGap =
        refl
    ; finiteSpectralGapFlagIsTrue =
        finiteYMSpectralGapIsLocalFiniteCarrier
    ; wilsonContinuumAuthority =
        Clay.canonicalWilson1974ContinuumLimitAuthorityReceipt
    ; wilsonContinuumAuthorityIsCanonical =
        refl
    ; wilsonLocalContinuumProofSupplied =
        Clay.Wilson1974ContinuumLimitAuthorityReceipt.localContinuumProofSupplied
          Clay.canonicalWilson1974ContinuumLimitAuthorityReceipt
    ; wilsonLocalContinuumProofSuppliedIsCanonical =
        refl
    ; wilsonLocalContinuumProofSuppliedIsFalse =
        Clay.Wilson1974ContinuumLimitAuthorityReceipt.localContinuumProofSuppliedIsFalse
          Clay.canonicalWilson1974ContinuumLimitAuthorityReceipt
    ; lower6Checkpoint =
        canonicalLower6YMU1U2M1M2WaveCheckpointReceipt
    ; lower6CheckpointIsCanonical =
        refl
    ; u2ConsumeM1Decision =
        canonicalU2Gate3LatestInstantiationDecisionReceipt
    ; u2ConsumeM1DecisionIsCanonical =
        refl
    ; sfgcStokesBoundaryOfBoundaryWord =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryOfBoundaryWord
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; sfgcStokesBoundaryOfBoundaryWordIsEmpty =
        refl
    ; sfgcIBPZeroVariationLaw =
        YMObs.sfgcZeroDiscreteVariationIBPLaw
    ; firstStrictBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; firstStrictBlockerIsNonFlatCurvature =
        refl
    ; continuumYangMillsConstructed =
        true
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayOrTerminalPromoted =
        false
    ; clayOrTerminalPromotedIsFalse =
        refl
    ; checkpointBoundary =
        "finiteYMSpectralGap is the finite-depth Balaban local carrier flag only"
        ∷ "Wilson 1974 continuum-limit authority is consumed as scoping authority, not as a local continuum proof"
        ∷ "u2 Gate 3 ConsumeM1 remains blocked by absent selected Lie carrier and field-strength transport inputs beyond the finite Site2D connection adapter"
        ∷ "SFGC Stokes evidence remains the empty CRT boundary-of-boundary word; SFGC IBP evidence remains the zero-variation law"
        ∷ "First strict YM blocker remains missingNonFlatSFGCSite2DConnectionCurvature"
        ∷ "No continuum Yang-Mills construction, Clay mass-gap theorem, spectral theorem, or terminal promotion is introduced"
        ∷ []
    }

yangMillsL4WilsonContinuumCheckpointNoClayPromotion :
  YMSFGCL4WilsonContinuumCheckpointReceipt.clayOrTerminalPromoted
    canonicalYMSFGCL4WilsonContinuumCheckpointReceipt
  ≡
  false
yangMillsL4WilsonContinuumCheckpointNoClayPromotion =
  refl

yangMillsL4WilsonContinuumCheckpointFirstBlockerIsNonFlatCurvature :
  YMSFGCL4WilsonContinuumCheckpointReceipt.firstStrictBlocker
    canonicalYMSFGCL4WilsonContinuumCheckpointReceipt
  ≡
  YMObs.missingNonFlatSFGCSite2DConnectionCurvature
yangMillsL4WilsonContinuumCheckpointFirstBlockerIsNonFlatCurvature =
  refl

------------------------------------------------------------------------
-- YM-chain u1/u2/m1 single-edge T3 finite bridge receipt.
--
-- This consumes the obstruction-side finite `singleEdgeT3Connection` bridge:
-- a Trit-valued single reference edge maps into SFGCSite2DDiscrete1Form, then
-- into YMSFGCUserSuppliedNonFlatConnectionCarrier, with φ1 curvature/holonomy
-- at the reference plaquette for the positive trit.  It is deliberately a
-- finite Gate 3 receipt only.

data YMSFGCSingleEdgeT3Gate3InspectionStatus : Set where
  singleEdgeT3Gate3FiniteBridgeConsumedNoPromotion :
    YMSFGCSingleEdgeT3Gate3InspectionStatus

record YMSFGCSingleEdgeT3Gate3InspectionReceipt : Set₁ where
  field
    status :
      YMSFGCSingleEdgeT3Gate3InspectionStatus

    singleEdgeT3Bridge :
      YMObs.YMSFGCSingleEdgeT3ConnectionBridgeReceipt

    singleEdgeT3BridgeIsCanonical :
      singleEdgeT3Bridge
      ≡
      YMObs.canonicalYMSFGCSingleEdgeT3ConnectionBridgeReceipt

    positiveCurvatureAtReference :
      SFGC.sfgcSite2DEvaluate2
        (SFGC.sfgcSite2Dδ₁
          (YMObs.singleEdgeT3Connection Trit.pos))
        YMObs.sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    positiveHolonomyAtReference :
      SFGC.sfgcSite2DWilsonLoopPhase
        (YMObs.singleEdgeT3Connection Trit.pos)
        YMObs.sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    userSuppliedPositiveCurvatureAtReference :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        (YMObs.ymSFGCUserSuppliedConnectionCurvature
          (YMObs.singleEdgeT3UserSuppliedConnection Trit.pos)
          YMObs.sfgcReferencePlaquette)
        YMObs.sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    lower6Checkpoint :
      Lower6YMU1U2M1M2WaveCheckpointReceipt

    lower6CheckpointIsCanonical :
      lower6Checkpoint
      ≡
      canonicalLower6YMU1U2M1M2WaveCheckpointReceipt

    exactStrictBlocker :
      YMObs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    exactStrictBlockerIsNonFlatCurvature :
      exactStrictBlocker
      ≡
      YMObs.missingNonFlatSFGCSite2DConnectionCurvature

    strictYangMillsPromoted :
      Bool

    strictYangMillsPromotedIsFalse :
      strictYangMillsPromoted ≡ false

    inspectionBoundary :
      List String

canonicalYMSFGCSingleEdgeT3Gate3InspectionReceipt :
  YMSFGCSingleEdgeT3Gate3InspectionReceipt
canonicalYMSFGCSingleEdgeT3Gate3InspectionReceipt =
  record
    { status =
        singleEdgeT3Gate3FiniteBridgeConsumedNoPromotion
    ; singleEdgeT3Bridge =
        YMObs.canonicalYMSFGCSingleEdgeT3ConnectionBridgeReceipt
    ; singleEdgeT3BridgeIsCanonical =
        refl
    ; positiveCurvatureAtReference =
        YMObs.singleEdgeT3ConnectionPosCurvatureAtReference
    ; positiveHolonomyAtReference =
        YMObs.singleEdgeT3PosHolonomyAtReference
    ; userSuppliedPositiveCurvatureAtReference =
        YMObs.singleEdgeT3UserSuppliedPosCurvatureAtReference
    ; lower6Checkpoint =
        canonicalLower6YMU1U2M1M2WaveCheckpointReceipt
    ; lower6CheckpointIsCanonical =
        refl
    ; exactStrictBlocker =
        YMObs.missingNonFlatSFGCSite2DConnectionCurvature
    ; exactStrictBlockerIsNonFlatCurvature =
        refl
    ; strictYangMillsPromoted =
        false
    ; strictYangMillsPromotedIsFalse =
        refl
    ; inspectionBoundary =
        "Consumes the obstruction-side singleEdgeT3Connection bridge into the Gate 3 receipt ledger"
        ∷ "The finite positive T3 edge has φ1 curvature/holonomy at the reference plaquette and adapts into YMSFGCUserSuppliedNonFlatConnectionCarrier"
        ∷ "u1 finite spectral, u2 D_A^2, m1 finite nonflatness, and m2 zero IBP remain finite/local receipts"
        ∷ "Strict Yang-Mills promotion remains blocked by missingNonFlatSFGCSite2DConnectionCurvature"
        ∷ []
    }

yangMillsSingleEdgeT3Gate3InspectionNonPromoting :
  YMSFGCSingleEdgeT3Gate3InspectionReceipt.strictYangMillsPromoted
    canonicalYMSFGCSingleEdgeT3Gate3InspectionReceipt
  ≡
  false
yangMillsSingleEdgeT3Gate3InspectionNonPromoting =
  refl

yangMillsReceiptMiddle6IBPVariationFirstMissingIsSelectedActionPairing :
  YangMillsFieldEquationReceipt.middle6VariationPairingFirstMissingDependency
    canonicalYangMillsFieldEquationReceipt
  ≡
  YMObs.missingSelectedActionVariationPairingIntoUserActionScalarCarrier
yangMillsReceiptMiddle6IBPVariationFirstMissingIsSelectedActionPairing =
  refl

yangMillsReceiptMiddle6IBPVariationDoesNotPromote :
  YMObs.YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt.variationPairingPromoted
    (YangMillsFieldEquationReceipt.middle6DiscreteIBPVariationPairingProgress
      canonicalYangMillsFieldEquationReceipt)
  ≡
  false
yangMillsReceiptMiddle6IBPVariationDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Gate 3 pure-YM finite carrier-level receipt.
--
-- This consumes the obstruction-side zero-current surface.  It is a concrete
-- D * F = J inhabitant with J definitionally equal to the zero Site2D
-- field-strength bridge, and it remains explicitly non-promoting.

data YMSFGCPureZeroCurrentFiniteReceiptStatus : Set where
  pureZeroCurrentFiniteDStarFEqualsJInhabitedNoPromotion :
    YMSFGCPureZeroCurrentFiniteReceiptStatus

record YMSFGCPureZeroCurrentFiniteReceipt : Set₁ where
  field
    status :
      YMSFGCPureZeroCurrentFiniteReceiptStatus

    obstructionPureZeroSurface :
      YMObs.YMSFGCPureZeroCurrentDStarFEqualsJFiniteSurface

    obstructionPureZeroSurfaceIsCanonical :
      obstructionPureZeroSurface
      ≡
      YMObs.canonicalYMSFGCPureZeroCurrentDStarFEqualsJFiniteSurface

    pureZeroSupply :
      YMObs.YMSFGCDiscreteHodgeCovariantDerivativePrimitiveSupply

    pureZeroSupplyIsCanonical :
      pureZeroSupply
      ≡
      YMObs.canonicalYMSFGCPureZeroCurrentDiscreteHodgeCovariantDerivativeSupply

    pureZeroCurrentSource :
      SFGC.GaugeField →
      SFGC.SFGCSite2DFieldStrengthBridge

    pureZeroCurrentSourceIsCanonical :
      pureZeroCurrentSource
      ≡
      YMObs.sfgcPureZeroCurrentSource

    pureZeroCurrentSourceIsZeroBridge :
      (A : SFGC.GaugeField) →
      pureZeroCurrentSource A
      ≡
      YMObs.sfgcZeroFieldStrengthBridge

    pureDStarFEqualsJWithJZero :
      (A : SFGC.GaugeField) →
      YMObs.sfgcPureZeroCovariantDerivativeOnDualCurvature
        A
        (YMObs.sfgcPureZeroHodgeStarCandidate
          (SFGC.sfgcSite2DFieldStrengthFromCurvature
            (SFGC.sfgcSite2Dδ₁
              (SFGC.sfgcSite2DConnectionTo1Form A))))
      ≡
      YMObs.sfgcPureZeroCurrentSource A

    pureDStarFEqualsJWithJZeroIsCanonical :
      pureDStarFEqualsJWithJZero
      ≡
      YMObs.sfgcPureZeroDStarFEqualsJLaw

    lowerHodgeCurrentSurface :
      YMSFGCRouteBLowerHodgeCurrentSurface

    lowerHodgeCurrentSurfaceIsCanonical :
      lowerHodgeCurrentSurface
      ≡
      canonicalYMSFGCRouteBLowerHodgeCurrentSurface

    strictHodgeVariationBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    strictHodgeVariationBlockerIsVariationPairing :
      strictHodgeVariationBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    receiptPromoted :
      Bool

    receiptPromotedIsFalse :
      receiptPromoted ≡ false

    receiptBoundary :
      List String

canonicalYMSFGCPureZeroCurrentFiniteReceipt :
  YMSFGCPureZeroCurrentFiniteReceipt
canonicalYMSFGCPureZeroCurrentFiniteReceipt =
  record
    { status =
        pureZeroCurrentFiniteDStarFEqualsJInhabitedNoPromotion
    ; obstructionPureZeroSurface =
        YMObs.canonicalYMSFGCPureZeroCurrentDStarFEqualsJFiniteSurface
    ; obstructionPureZeroSurfaceIsCanonical =
        refl
    ; pureZeroSupply =
        YMObs.canonicalYMSFGCPureZeroCurrentDiscreteHodgeCovariantDerivativeSupply
    ; pureZeroSupplyIsCanonical =
        refl
    ; pureZeroCurrentSource =
        YMObs.sfgcPureZeroCurrentSource
    ; pureZeroCurrentSourceIsCanonical =
        refl
    ; pureZeroCurrentSourceIsZeroBridge =
        λ _ → refl
    ; pureDStarFEqualsJWithJZero =
        YMObs.sfgcPureZeroDStarFEqualsJLaw
    ; pureDStarFEqualsJWithJZeroIsCanonical =
        refl
    ; lowerHodgeCurrentSurface =
        canonicalYMSFGCRouteBLowerHodgeCurrentSurface
    ; lowerHodgeCurrentSurfaceIsCanonical =
        refl
    ; strictHodgeVariationBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; strictHodgeVariationBlockerIsVariationPairing =
        refl
    ; receiptPromoted =
        false
    ; receiptPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Consumes the obstruction-side pure zero-current finite surface"
        ∷ "The inhabited finite equation is D * F = J with J definitionally equal to SFGC.sfgcSite2DZero2Form via sfgcZeroFieldStrengthBridge"
        ∷ "The receipt also points back to the Route B lower Hodge/current surface, but does not reinterpret it as a strict selected Hodge law"
        ∷ "Strict promotion remains blocked by missingVariationPairingForSelectedHodgeStar and the absent metric Hodge/current variation package"
        ∷ []
    }

yangMillsPureZeroCurrentFiniteReceiptInhabitsJZero :
  (A : SFGC.GaugeField) →
  YMSFGCPureZeroCurrentFiniteReceipt.pureZeroCurrentSource
    canonicalYMSFGCPureZeroCurrentFiniteReceipt
    A
  ≡
  YMObs.sfgcZeroFieldStrengthBridge
yangMillsPureZeroCurrentFiniteReceiptInhabitsJZero A =
  refl

yangMillsPureZeroCurrentFiniteReceiptDoesNotPromote :
  YMSFGCPureZeroCurrentFiniteReceipt.receiptPromoted
    canonicalYMSFGCPureZeroCurrentFiniteReceipt
  ≡
  false
yangMillsPureZeroCurrentFiniteReceiptDoesNotPromote =
  refl
