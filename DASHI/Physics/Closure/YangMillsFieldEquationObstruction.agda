module DASHI.Physics.Closure.YangMillsFieldEquationObstruction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_) renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; _∷_; [])
open import DASHI.Core.Q using (ℚ)

import DASHI.Algebra.Trit as Trit
import DASHI.Physics.Closure.DiscreteBianchiIdentityReceipt as Bianchi
import DASHI.Physics.Closure.DiscreteStokesBianchiObstruction as StokesObs
import DASHI.Physics.Closure.FactorVecDiscreteMetricTensorSurface as FVMetric
import DASHI.Physics.Closure.G2DiscreteCurvatureCarrier as G2DCC
import DASHI.Physics.Closure.G2NondegeneratePlaquetteSchema as G2NP
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.YM.CovariantDerivative as YM_CD
import DASHI.Physics.YM.FieldStrength as YM_FS
import DASHI.Physics.YM.SU2LieAlgebra as YM_SU2
import DASHI.Physics.YM.YangMillsAction as YM_YM
import DASHI.Physics.SFGC.NonAbelian.NonAbelianSFGCCarrier as NonAbelianCarrier
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftFiniteGaugeSymmetry as SFGS

trans :
  {A : Set} →
  {x y z : A} →
  x ≡ y →
  y ≡ z →
  x ≡ z
trans refl refl =
  refl

symEq :
  {A : Set} →
  {x y : A} →
  x ≡ y →
  y ≡ x
symEq refl =
  refl

cong :
  {A B : Set} →
  (f : A → B) →
  {x y : A} →
  x ≡ y →
  f x ≡ f y
cong f refl =
  refl

------------------------------------------------------------------------
-- Yang-Mills field-equation obstruction.
--
-- This module sharpens the Paper 4 field-equation lane.  The older G2DCC
-- diagnostic still records a right-edge-only gauge-connection gap, while the
-- inspected SFGC surface now also exposes an SFGCSite2D sidecar with p2/p3
-- plaquettes.  We package that sidecar as curvature data and record its
-- selected exterior d^2 = 0 law.  D * F = J and covariant D F = 0 still cannot
-- honestly be wired without the Yang-Mills operator layer.

data YangMillsFieldEquationObstructionStatus : Set where
  blockedBeforeSFGCCurvatureCarrierNoPromotion :
    YangMillsFieldEquationObstructionStatus

data YangMillsFieldEquationMissingPrerequisite : Set where
  missingDiscreteCurvatureCarrierForSFGCGaugeField :
    YangMillsFieldEquationMissingPrerequisite

  missingNondegeneratePlaquetteGeometry :
    YangMillsFieldEquationMissingPrerequisite

  missingBoundaryOfBoundaryZeroForSelectedPlaquettes :
    YangMillsFieldEquationMissingPrerequisite

  missingCurvatureFromSFGCGaugeConnection :
    YangMillsFieldEquationMissingPrerequisite

  missingCurvatureToYangMillsFieldStrength :
    YangMillsFieldEquationMissingPrerequisite

  missingCovariantDerivativeOnSelectedGaugeBundle :
    YangMillsFieldEquationMissingPrerequisite

  missingHodgeStarOnDiscreteCurvature :
    YangMillsFieldEquationMissingPrerequisite

  missingCurrentSourceAndCoupling :
    YangMillsFieldEquationMissingPrerequisite

  missingDStarFEqualsJLaw :
    YangMillsFieldEquationMissingPrerequisite

  missingYangMillsBianchiDFEqualsZeroLaw :
    YangMillsFieldEquationMissingPrerequisite

canonicalYangMillsFieldEquationMissingPrerequisites :
  List YangMillsFieldEquationMissingPrerequisite
canonicalYangMillsFieldEquationMissingPrerequisites =
  missingCovariantDerivativeOnSelectedGaugeBundle
  ∷ missingHodgeStarOnDiscreteCurvature
  ∷ missingCurrentSourceAndCoupling
  ∷ missingDStarFEqualsJLaw
  ∷ missingYangMillsBianchiDFEqualsZeroLaw
  ∷ []

data YangMillsBianchiMissingPrimitive : Set where
  missingSelectedExteriorDerivativeSquaredZero :
    YangMillsBianchiMissingPrimitive

  missingCovariantDerivativeExtendsSelectedExteriorDerivative :
    YangMillsBianchiMissingPrimitive

  missingPlaquetteStokesOrJacobiLaw :
    YangMillsBianchiMissingPrimitive

  missingGaugeCompatibilityOfBianchiLaw :
    YangMillsBianchiMissingPrimitive

canonicalYangMillsBianchiMissingPrimitives :
  List YangMillsBianchiMissingPrimitive
canonicalYangMillsBianchiMissingPrimitives =
  missingCovariantDerivativeExtendsSelectedExteriorDerivative
  ∷ missingPlaquetteStokesOrJacobiLaw
  ∷ missingGaugeCompatibilityOfBianchiLaw
  ∷ []

data YangMillsVariationalEquationMissingPrimitive : Set where
  missingYangMillsActionFunctionalOnSFGCSite2D :
    YangMillsVariationalEquationMissingPrimitive

  missingVariationPairingForSelectedHodgeStar :
    YangMillsVariationalEquationMissingPrimitive

  missingEulerLagrangeDerivativeOfYangMillsAction :
    YangMillsVariationalEquationMissingPrimitive

  missingCurrentSourceCouplingToMatter :
    YangMillsVariationalEquationMissingPrimitive

  missingVariationalDStarFEqualsJLaw :
    YangMillsVariationalEquationMissingPrimitive

missingVariationPairingForSelectedHodgeStarProof :
  YangMillsVariationalEquationMissingPrimitive
missingVariationPairingForSelectedHodgeStarProof =
  missingVariationPairingForSelectedHodgeStar

canonicalYangMillsVariationalEquationMissingPrimitives :
  List YangMillsVariationalEquationMissingPrimitive
canonicalYangMillsVariationalEquationMissingPrimitives =
  missingYangMillsActionFunctionalOnSFGCSite2D
  ∷ missingVariationPairingForSelectedHodgeStar
  ∷ missingEulerLagrangeDerivativeOfYangMillsAction
  ∷ missingCurrentSourceCouplingToMatter
  ∷ missingVariationalDStarFEqualsJLaw
  ∷ []

data YMSFGCSelectedCovariantDerivativeMissingPrimitive : Set where
  missingFieldStrengthTransportActionOnSelectedGaugeBundle :
    YMSFGCSelectedCovariantDerivativeMissingPrimitive

  missingCovariantDifferenceOperationOnSelectedFieldStrength :
    YMSFGCSelectedCovariantDerivativeMissingPrimitive

  missingCovariantDerivativeExtendsSelectedExteriorDerivative :
    YMSFGCSelectedCovariantDerivativeMissingPrimitive

  missingCovariantDerivativeGaugeCompatibilityLaw :
    YMSFGCSelectedCovariantDerivativeMissingPrimitive

missingFieldStrengthTransportActionOnSelectedGaugeBundleProof :
  YMSFGCSelectedCovariantDerivativeMissingPrimitive
missingFieldStrengthTransportActionOnSelectedGaugeBundleProof =
  missingFieldStrengthTransportActionOnSelectedGaugeBundle

data YMSFGCNonAbelianCovariantDerivativeMissingPrimitive : Set where
  missingSFGCFibreRepresentationMapIntoConcreteFiniteLieCarrier :
    YMSFGCNonAbelianCovariantDerivativeMissingPrimitive

  missingNonAbelianFibreLieAlgebraCarrier :
    YMSFGCNonAbelianCovariantDerivativeMissingPrimitive

  missingNonAbelianFibreLieBracket :
    YMSFGCNonAbelianCovariantDerivativeMissingPrimitive

  missingNonAbelianFibreAdditiveInverse :
    YMSFGCNonAbelianCovariantDerivativeMissingPrimitive

  missingNonAbelianBracketAntisymmetryWitness :
    YMSFGCNonAbelianCovariantDerivativeMissingPrimitive

  missingNonAbelianJacobiWitness :
    YMSFGCNonAbelianCovariantDerivativeMissingPrimitive

  missingConnectionOneFormAsFibreAlgebraElement :
    YMSFGCNonAbelianCovariantDerivativeMissingPrimitive

  missingCovariantDerivativeFormulaDAEqualsDPlusBracket :
    YMSFGCNonAbelianCovariantDerivativeMissingPrimitive

  missingCurvatureActionDASquaredEqualsBracketF :
    YMSFGCNonAbelianCovariantDerivativeMissingPrimitive

canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives :
  List YMSFGCSelectedCovariantDerivativeMissingPrimitive
canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives =
  missingFieldStrengthTransportActionOnSelectedGaugeBundle
  ∷ missingCovariantDifferenceOperationOnSelectedFieldStrength
  ∷ missingCovariantDerivativeExtendsSelectedExteriorDerivative
  ∷ missingCovariantDerivativeGaugeCompatibilityLaw
  ∷ []

record YMSFGCSelectedFiniteGaugeSectorBridge : Set₁ where
  field
    nonAbelianCarrierWitness :
      NonAbelianCarrier.NonAbelianSFGCCarrierWitness

    nonAbelianCarrierWitnessIsCanonical :
      nonAbelianCarrierWitness
      ≡
      NonAbelianCarrier.canonicalNonAbelianSFGCCarrierWitness

canonicalYMSFGCSelectedFiniteGaugeSectorBridge :
  YMSFGCSelectedFiniteGaugeSectorBridge
canonicalYMSFGCSelectedFiniteGaugeSectorBridge =
  record
    { nonAbelianCarrierWitness =
        NonAbelianCarrier.canonicalNonAbelianSFGCCarrierWitness
    ; nonAbelianCarrierWitnessIsCanonical =
        refl
    }

canonicalYMSFGCNonAbelianCovariantDerivativeMissingPrimitives :
  List YMSFGCNonAbelianCovariantDerivativeMissingPrimitive
canonicalYMSFGCNonAbelianCovariantDerivativeMissingPrimitives =
  missingConnectionOneFormAsFibreAlgebraElement
  ∷ missingCovariantDerivativeFormulaDAEqualsDPlusBracket
  ∷ missingCurvatureActionDASquaredEqualsBracketF
  ∷ []

data YMSFGCActionFunctionalMissingPrimitive : Set where
  missingCurvatureQuadraticDensityOnPhase4Plaquettes :
    YMSFGCActionFunctionalMissingPrimitive

  missingPlaquetteSumOrIntegrationFunctional :
    YMSFGCActionFunctionalMissingPrimitive

  missingGaugeInvariantTracePairingForPhase4Curvature :
    YMSFGCActionFunctionalMissingPrimitive

  missingEulerLagrangeVariationPairing :
    YMSFGCActionFunctionalMissingPrimitive

canonicalYMSFGCActionFunctionalMissingPrimitives :
  List YMSFGCActionFunctionalMissingPrimitive
canonicalYMSFGCActionFunctionalMissingPrimitives =
  missingCurvatureQuadraticDensityOnPhase4Plaquettes
  ∷ missingPlaquetteSumOrIntegrationFunctional
  ∷ missingGaugeInvariantTracePairingForPhase4Curvature
  ∷ missingEulerLagrangeVariationPairing
  ∷ []

data YMSFGCFinalPrimitiveMathBlocker : Set where
  missingNonFlatHolonomyConjugationUnderGaugeTransform :
    YMSFGCFinalPrimitiveMathBlocker

  missingKillingFormAdInvariance :
    YMSFGCFinalPrimitiveMathBlocker

  missingDiscreteVariationIntegrationByParts :
    YMSFGCFinalPrimitiveMathBlocker

canonicalYMSFGCFinalPrimitiveMathBlockers :
  List YMSFGCFinalPrimitiveMathBlocker
canonicalYMSFGCFinalPrimitiveMathBlockers =
  missingNonFlatHolonomyConjugationUnderGaugeTransform
  ∷ missingKillingFormAdInvariance
  ∷ missingDiscreteVariationIntegrationByParts
  ∷ []

data YMSFGCRealKillingAdInvarianceIrreducibility : Set where
  missingLieAlgebraCarrierForSelectedFiniteGaugeSector :
    YMSFGCRealKillingAdInvarianceIrreducibility

  missingNontrivialAdjointActionOnSelectedFieldStrength :
    YMSFGCRealKillingAdInvarianceIrreducibility

  missingKillingOrTracePairingOnSelectedFieldStrength :
    YMSFGCRealKillingAdInvarianceIrreducibility

  missingAdInvarianceProofForThatPairing :
    YMSFGCRealKillingAdInvarianceIrreducibility

canonicalYMSFGCRealKillingAdInvarianceIrreducibility :
  List YMSFGCRealKillingAdInvarianceIrreducibility
canonicalYMSFGCRealKillingAdInvarianceIrreducibility =
  missingLieAlgebraCarrierForSelectedFiniteGaugeSector
  ∷ missingNontrivialAdjointActionOnSelectedFieldStrength
  ∷ missingKillingOrTracePairingOnSelectedFieldStrength
  ∷ missingAdInvarianceProofForThatPairing
  ∷ []

sfgcCanonicalNonFlatCurvature2Form :
  SFGC.SFGCSite2DDiscrete2Form
sfgcCanonicalNonFlatCurvature2Form =
  SFGC.sfgcSite2DArbitrary2Form (λ _ → SPTI4.φ0)

data YMSFGCNonFlatHolonomyConjugationIrreducibility : Set where
  nonFlatCurvatureWitness :
    SFGC.SFGCSite2DDiscrete2Form →
    YMSFGCNonFlatHolonomyConjugationIrreducibility

  missingEndpointGaugeFactorsForPlaquetteHolonomy :
    YMSFGCNonFlatHolonomyConjugationIrreducibility

  missingNontrivialFieldStrengthAdjointAction :
    YMSFGCNonFlatHolonomyConjugationIrreducibility

  missingConjugationLawForNonFlatPlaquetteHolonomy :
    YMSFGCNonFlatHolonomyConjugationIrreducibility

canonicalYMSFGCNonFlatHolonomyConjugationIrreducibility :
  List YMSFGCNonFlatHolonomyConjugationIrreducibility
canonicalYMSFGCNonFlatHolonomyConjugationIrreducibility =
  nonFlatCurvatureWitness sfgcCanonicalNonFlatCurvature2Form
  ∷ missingEndpointGaugeFactorsForPlaquetteHolonomy
  ∷ missingNontrivialFieldStrengthAdjointAction
  ∷ missingConjugationLawForNonFlatPlaquetteHolonomy
  ∷ []

missingNonFlatSFGCSite2DConnectionCurvatureProof :
  YMSFGCNonFlatHolonomyConjugationIrreducibility
missingNonFlatSFGCSite2DConnectionCurvatureProof =
  nonFlatCurvatureWitness sfgcCanonicalNonFlatCurvature2Form

missingNonFlatSFGCSite2DConnectionCurvature :
  YMSFGCNonFlatHolonomyConjugationIrreducibility
missingNonFlatSFGCSite2DConnectionCurvature =
  missingNonFlatSFGCSite2DConnectionCurvatureProof

record YMSFGCNonFlatHolonomyTelescopingPrimitiveSupply : Set₁ where
  field
    HolonomyCarrier :
      Set

    identityHolonomy :
      HolonomyCarrier

    composeHolonomy :
      HolonomyCarrier →
      HolonomyCarrier →
      HolonomyCarrier

    inverseHolonomy :
      HolonomyCarrier →
      HolonomyCarrier

    edgeHolonomy :
      SFGC.GaugeField →
      SFGC.SFGCSite2DEdge →
      HolonomyCarrier

    plaquetteHolonomy :
      SFGC.GaugeField →
      SFGC.SFGCSite2DPlaquette →
      HolonomyCarrier

    endpointGaugeFactor :
      SFGS.GaugeTransform →
      SFGC.SFGCSite2D →
      HolonomyCarrier

    conjugateBy :
      HolonomyCarrier →
      HolonomyCarrier →
      HolonomyCarrier

    plaquetteBoundaryTelescopingLaw :
      (A : SFGC.GaugeField) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      composeHolonomy
        (composeHolonomy
          (composeHolonomy
            (edgeHolonomy A (SFGC.sfgcSite2DPlaquetteBottomEdge plaquette))
            (edgeHolonomy A (SFGC.sfgcSite2DPlaquetteRightEdge plaquette)))
          (inverseHolonomy
            (edgeHolonomy A (SFGC.sfgcSite2DPlaquetteTopEdge plaquette))))
        (inverseHolonomy
          (edgeHolonomy A (SFGC.sfgcSite2DPlaquetteLeftEdge plaquette)))
      ≡
      plaquetteHolonomy A plaquette

    nonFlatGaugeConjugationLaw :
      (gauge : SFGS.GaugeTransform) →
      (A : SFGC.GaugeField) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      plaquetteHolonomy (SFGC.transformGauge gauge A) plaquette
      ≡
      conjugateBy
        (endpointGaugeFactor
          gauge
          (SFGC.sfgcSite2DPlaquetteSW plaquette))
        (plaquetteHolonomy A plaquette)

    supplyBoundary :
      List String

record YMSFGCLieAlgebraTraceAdInvariancePrimitiveSupply : Set₁ where
  field
    LieAlgebraCarrier :
      Set

    bracket :
      LieAlgebraCarrier →
      LieAlgebraCarrier →
      LieAlgebraCarrier

    adjointAction :
      SFGS.GaugeTransform →
      LieAlgebraCarrier →
      LieAlgebraCarrier

    traceOrKillingPairing :
      LieAlgebraCarrier →
      LieAlgebraCarrier →
      ℤ

    fieldStrengthToLieAlgebra :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DPlaquette →
      LieAlgebraCarrier

    traceOrKillingAdInvarianceLaw :
      (gauge : SFGS.GaugeTransform) →
      (x y : LieAlgebraCarrier) →
      traceOrKillingPairing
        (adjointAction gauge x)
        (adjointAction gauge y)
      ≡
      traceOrKillingPairing x y

    supplyBoundary :
      List String

record YMSFGCNonAbelianCovariantDerivativePrimitiveSupply : Set₁ where
  field
    FibreLieAlgebraCarrier :
      Set

    zeroFibreLieAlgebra :
      FibreLieAlgebraCarrier

    addFibreLieAlgebra :
      FibreLieAlgebraCarrier →
      FibreLieAlgebraCarrier →
      FibreLieAlgebraCarrier

    negateFibreLieAlgebra :
      FibreLieAlgebraCarrier →
      FibreLieAlgebraCarrier

    bracket :
      FibreLieAlgebraCarrier →
      FibreLieAlgebraCarrier →
      FibreLieAlgebraCarrier

    bracketAntisymmetry :
      (x y : FibreLieAlgebraCarrier) →
      bracket x y
      ≡
      negateFibreLieAlgebra (bracket y x)

    jacobiWitness :
      (x y z : FibreLieAlgebraCarrier) →
      addFibreLieAlgebra
        (addFibreLieAlgebra
          (bracket x (bracket y z))
          (bracket y (bracket z x)))
        (bracket z (bracket x y))
      ≡
      zeroFibreLieAlgebra

    exteriorDerivative :
      FibreLieAlgebraCarrier →
      FibreLieAlgebraCarrier

    connectionOneFormAsFibreAlgebra :
      SFGC.GaugeField →
      FibreLieAlgebraCarrier

    curvatureAsFibreAlgebra :
      SFGC.GaugeField →
      FibreLieAlgebraCarrier

    covariantDerivative :
      SFGC.GaugeField →
      FibreLieAlgebraCarrier →
      FibreLieAlgebraCarrier

    covariantDerivativeFormula :
      (A : SFGC.GaugeField) →
      (section : FibreLieAlgebraCarrier) →
      covariantDerivative A section
      ≡
      addFibreLieAlgebra
        (exteriorDerivative section)
        (bracket (connectionOneFormAsFibreAlgebra A) section)

    curvatureActionTheorem :
      (A : SFGC.GaugeField) →
      (section : FibreLieAlgebraCarrier) →
      covariantDerivative A (covariantDerivative A section)
      ≡
      bracket (curvatureAsFibreAlgebra A) section

    supplyBoundary :
      List String

data YMSFGCLocalFiniteLie3Sign : Set where
  signPos : YMSFGCLocalFiniteLie3Sign
  signNeg : YMSFGCLocalFiniteLie3Sign

data YMSFGCLocalFiniteLie3Axis : Set where
  axisX : YMSFGCLocalFiniteLie3Axis
  axisY : YMSFGCLocalFiniteLie3Axis
  axisZ : YMSFGCLocalFiniteLie3Axis

data YMSFGCLocalFiniteLie3Carrier : Set where
  lieZero : YMSFGCLocalFiniteLie3Carrier
  lieBasis :
    YMSFGCLocalFiniteLie3Sign →
    YMSFGCLocalFiniteLie3Axis →
    YMSFGCLocalFiniteLie3Carrier

localFiniteLie3NegSign :
  YMSFGCLocalFiniteLie3Sign →
  YMSFGCLocalFiniteLie3Sign
localFiniteLie3NegSign signPos = signNeg
localFiniteLie3NegSign signNeg = signPos

localFiniteLie3MulSign :
  YMSFGCLocalFiniteLie3Sign →
  YMSFGCLocalFiniteLie3Sign →
  YMSFGCLocalFiniteLie3Sign
localFiniteLie3MulSign signPos sign = sign
localFiniteLie3MulSign signNeg signPos = signNeg
localFiniteLie3MulSign signNeg signNeg = signPos

localFiniteLie3Neg :
  YMSFGCLocalFiniteLie3Carrier →
  YMSFGCLocalFiniteLie3Carrier
localFiniteLie3Neg lieZero = lieZero
localFiniteLie3Neg (lieBasis sign axis) =
  lieBasis (localFiniteLie3NegSign sign) axis

localFiniteLie3Scale :
  YMSFGCLocalFiniteLie3Sign →
  YMSFGCLocalFiniteLie3Carrier →
  YMSFGCLocalFiniteLie3Carrier
localFiniteLie3Scale sign lieZero = lieZero
localFiniteLie3Scale sign (lieBasis basisSign axis) =
  lieBasis (localFiniteLie3MulSign sign basisSign) axis

localFiniteLie3PositiveBracket :
  YMSFGCLocalFiniteLie3Axis →
  YMSFGCLocalFiniteLie3Axis →
  YMSFGCLocalFiniteLie3Carrier
localFiniteLie3PositiveBracket axisX axisX = lieZero
localFiniteLie3PositiveBracket axisY axisY = lieZero
localFiniteLie3PositiveBracket axisZ axisZ = lieZero
localFiniteLie3PositiveBracket axisX axisY = lieBasis signPos axisZ
localFiniteLie3PositiveBracket axisY axisZ = lieBasis signPos axisX
localFiniteLie3PositiveBracket axisZ axisX = lieBasis signPos axisY
localFiniteLie3PositiveBracket axisY axisX = lieBasis signNeg axisZ
localFiniteLie3PositiveBracket axisZ axisY = lieBasis signNeg axisX
localFiniteLie3PositiveBracket axisX axisZ = lieBasis signNeg axisY

localFiniteLie3Bracket :
  YMSFGCLocalFiniteLie3Carrier →
  YMSFGCLocalFiniteLie3Carrier →
  YMSFGCLocalFiniteLie3Carrier
localFiniteLie3Bracket lieZero y = lieZero
localFiniteLie3Bracket x lieZero = lieZero
localFiniteLie3Bracket (lieBasis signA axisA) (lieBasis signB axisB) =
  localFiniteLie3Scale
    (localFiniteLie3MulSign signA signB)
    (localFiniteLie3PositiveBracket axisA axisB)

localFiniteLie3BracketRightZero :
  (x : YMSFGCLocalFiniteLie3Carrier) →
  localFiniteLie3Bracket x lieZero ≡ lieZero
localFiniteLie3BracketRightZero lieZero = refl
localFiniteLie3BracketRightZero (lieBasis sign axis) = refl

localFiniteLie3BracketLeftZero :
  (x : YMSFGCLocalFiniteLie3Carrier) →
  localFiniteLie3Bracket lieZero x ≡ lieZero
localFiniteLie3BracketLeftZero x = refl

localFiniteLie3JacobiAdd :
  YMSFGCLocalFiniteLie3Carrier →
  YMSFGCLocalFiniteLie3Carrier →
  YMSFGCLocalFiniteLie3Carrier
localFiniteLie3JacobiAdd lieZero y = y
localFiniteLie3JacobiAdd x lieZero = x
localFiniteLie3JacobiAdd (lieBasis _ _) (lieBasis _ _) = lieZero

localFiniteLie3BracketAntisymmetry :
  (x y : YMSFGCLocalFiniteLie3Carrier) →
  localFiniteLie3Bracket x y
  ≡
  localFiniteLie3Neg (localFiniteLie3Bracket y x)
localFiniteLie3BracketAntisymmetry lieZero lieZero = refl
localFiniteLie3BracketAntisymmetry lieZero (lieBasis signPos axisX) = refl
localFiniteLie3BracketAntisymmetry lieZero (lieBasis signPos axisY) = refl
localFiniteLie3BracketAntisymmetry lieZero (lieBasis signPos axisZ) = refl
localFiniteLie3BracketAntisymmetry lieZero (lieBasis signNeg axisX) = refl
localFiniteLie3BracketAntisymmetry lieZero (lieBasis signNeg axisY) = refl
localFiniteLie3BracketAntisymmetry lieZero (lieBasis signNeg axisZ) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisX) lieZero = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisY) lieZero = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisZ) lieZero = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisX) lieZero = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisY) lieZero = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisZ) lieZero = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisX) (lieBasis signPos axisX) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisX) (lieBasis signPos axisY) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisX) (lieBasis signPos axisZ) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisY) (lieBasis signPos axisX) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisY) (lieBasis signPos axisY) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisY) (lieBasis signPos axisZ) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisZ) (lieBasis signPos axisX) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisZ) (lieBasis signPos axisY) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisZ) (lieBasis signPos axisZ) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisX) (lieBasis signNeg axisX) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisX) (lieBasis signNeg axisY) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisX) (lieBasis signNeg axisZ) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisY) (lieBasis signNeg axisX) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisY) (lieBasis signNeg axisY) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisY) (lieBasis signNeg axisZ) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisZ) (lieBasis signNeg axisX) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisZ) (lieBasis signNeg axisY) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signPos axisZ) (lieBasis signNeg axisZ) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisX) (lieBasis signPos axisX) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisX) (lieBasis signPos axisY) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisX) (lieBasis signPos axisZ) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisY) (lieBasis signPos axisX) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisY) (lieBasis signPos axisY) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisY) (lieBasis signPos axisZ) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisZ) (lieBasis signPos axisX) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisZ) (lieBasis signPos axisY) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisZ) (lieBasis signPos axisZ) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisX) (lieBasis signNeg axisX) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisX) (lieBasis signNeg axisY) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisX) (lieBasis signNeg axisZ) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisY) (lieBasis signNeg axisX) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisY) (lieBasis signNeg axisY) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisY) (lieBasis signNeg axisZ) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisZ) (lieBasis signNeg axisX) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisZ) (lieBasis signNeg axisY) = refl
localFiniteLie3BracketAntisymmetry (lieBasis signNeg axisZ) (lieBasis signNeg axisZ) = refl

localFiniteLie3JacobiWitness :
  (x y z : YMSFGCLocalFiniteLie3Carrier) →
  localFiniteLie3JacobiAdd
    (localFiniteLie3JacobiAdd
      (localFiniteLie3Bracket x (localFiniteLie3Bracket y z))
      (localFiniteLie3Bracket y (localFiniteLie3Bracket z x)))
    (localFiniteLie3Bracket z (localFiniteLie3Bracket x y))
  ≡
  lieZero
localFiniteLie3JacobiWitness lieZero y z
  rewrite localFiniteLie3BracketRightZero z
        | localFiniteLie3BracketRightZero y = refl
localFiniteLie3JacobiWitness (lieBasis signX axisX) lieZero z
  rewrite localFiniteLie3BracketRightZero z = refl
localFiniteLie3JacobiWitness (lieBasis signX axisY) lieZero z
  rewrite localFiniteLie3BracketRightZero z = refl
localFiniteLie3JacobiWitness (lieBasis signX axisZ) lieZero z
  rewrite localFiniteLie3BracketRightZero z = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisX)
  (lieBasis signY axisX)
  lieZero = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisX)
  (lieBasis signY axisY)
  lieZero = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisX)
  (lieBasis signY axisZ)
  lieZero = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisY)
  (lieBasis signY axisX)
  lieZero = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisY)
  (lieBasis signY axisY)
  lieZero = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisY)
  (lieBasis signY axisZ)
  lieZero = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisZ)
  (lieBasis signY axisX)
  lieZero = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisZ)
  (lieBasis signY axisY)
  lieZero = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisZ)
  (lieBasis signY axisZ)
  lieZero = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisX)
  (lieBasis signY axisX)
  (lieBasis signZ axisX) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisX)
  (lieBasis signY axisX)
  (lieBasis signZ axisY) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisX)
  (lieBasis signY axisX)
  (lieBasis signZ axisZ) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisX)
  (lieBasis signY axisY)
  (lieBasis signZ axisX) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisX)
  (lieBasis signY axisY)
  (lieBasis signZ axisY) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisX)
  (lieBasis signY axisY)
  (lieBasis signZ axisZ) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisX)
  (lieBasis signY axisZ)
  (lieBasis signZ axisX) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisX)
  (lieBasis signY axisZ)
  (lieBasis signZ axisY) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisX)
  (lieBasis signY axisZ)
  (lieBasis signZ axisZ) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisY)
  (lieBasis signY axisX)
  (lieBasis signZ axisX) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisY)
  (lieBasis signY axisX)
  (lieBasis signZ axisY) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisY)
  (lieBasis signY axisX)
  (lieBasis signZ axisZ) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisY)
  (lieBasis signY axisY)
  (lieBasis signZ axisX) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisY)
  (lieBasis signY axisY)
  (lieBasis signZ axisY) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisY)
  (lieBasis signY axisY)
  (lieBasis signZ axisZ) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisY)
  (lieBasis signY axisZ)
  (lieBasis signZ axisX) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisY)
  (lieBasis signY axisZ)
  (lieBasis signZ axisY) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisY)
  (lieBasis signY axisZ)
  (lieBasis signZ axisZ) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisZ)
  (lieBasis signY axisX)
  (lieBasis signZ axisX) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisZ)
  (lieBasis signY axisX)
  (lieBasis signZ axisY) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisZ)
  (lieBasis signY axisX)
  (lieBasis signZ axisZ) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisZ)
  (lieBasis signY axisY)
  (lieBasis signZ axisX) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisZ)
  (lieBasis signY axisY)
  (lieBasis signZ axisY) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisZ)
  (lieBasis signY axisY)
  (lieBasis signZ axisZ) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisZ)
  (lieBasis signY axisZ)
  (lieBasis signZ axisX) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisZ)
  (lieBasis signY axisZ)
  (lieBasis signZ axisY) = refl
localFiniteLie3JacobiWitness
  (lieBasis signX axisZ)
  (lieBasis signY axisZ)
  (lieBasis signZ axisZ) = refl

localFiniteLie3PositiveAxisJacobi :
  (x y z : YMSFGCLocalFiniteLie3Axis) →
  localFiniteLie3JacobiAdd
    (localFiniteLie3JacobiAdd
      (localFiniteLie3Bracket
        (lieBasis signPos x)
        (localFiniteLie3Bracket (lieBasis signPos y) (lieBasis signPos z)))
      (localFiniteLie3Bracket
        (lieBasis signPos y)
        (localFiniteLie3Bracket (lieBasis signPos z) (lieBasis signPos x))))
    (localFiniteLie3Bracket
      (lieBasis signPos z)
      (localFiniteLie3Bracket (lieBasis signPos x) (lieBasis signPos y)))
  ≡
  lieZero
localFiniteLie3PositiveAxisJacobi axisX axisX axisX = refl
localFiniteLie3PositiveAxisJacobi axisX axisX axisY = refl
localFiniteLie3PositiveAxisJacobi axisX axisX axisZ = refl
localFiniteLie3PositiveAxisJacobi axisX axisY axisX = refl
localFiniteLie3PositiveAxisJacobi axisX axisY axisY = refl
localFiniteLie3PositiveAxisJacobi axisX axisY axisZ = refl
localFiniteLie3PositiveAxisJacobi axisX axisZ axisX = refl
localFiniteLie3PositiveAxisJacobi axisX axisZ axisY = refl
localFiniteLie3PositiveAxisJacobi axisX axisZ axisZ = refl
localFiniteLie3PositiveAxisJacobi axisY axisX axisX = refl
localFiniteLie3PositiveAxisJacobi axisY axisX axisY = refl
localFiniteLie3PositiveAxisJacobi axisY axisX axisZ = refl
localFiniteLie3PositiveAxisJacobi axisY axisY axisX = refl
localFiniteLie3PositiveAxisJacobi axisY axisY axisY = refl
localFiniteLie3PositiveAxisJacobi axisY axisY axisZ = refl
localFiniteLie3PositiveAxisJacobi axisY axisZ axisX = refl
localFiniteLie3PositiveAxisJacobi axisY axisZ axisY = refl
localFiniteLie3PositiveAxisJacobi axisY axisZ axisZ = refl
localFiniteLie3PositiveAxisJacobi axisZ axisX axisX = refl
localFiniteLie3PositiveAxisJacobi axisZ axisX axisY = refl
localFiniteLie3PositiveAxisJacobi axisZ axisX axisZ = refl
localFiniteLie3PositiveAxisJacobi axisZ axisY axisX = refl
localFiniteLie3PositiveAxisJacobi axisZ axisY axisY = refl
localFiniteLie3PositiveAxisJacobi axisZ axisY axisZ = refl
localFiniteLie3PositiveAxisJacobi axisZ axisZ axisX = refl
localFiniteLie3PositiveAxisJacobi axisZ axisZ axisY = refl
localFiniteLie3PositiveAxisJacobi axisZ axisZ axisZ = refl

record YMSFGCLocalFiniteSU2LieAlgebra : Set₁ where
  field
    SU2Basis :
      Set

    SU2Carrier :
      Set

    su2Zero :
      SU2Carrier

    su2Basis :
      YMSFGCLocalFiniteLie3Sign →
      SU2Basis →
      SU2Carrier

    su2Scale :
      YMSFGCLocalFiniteLie3Sign →
      SU2Carrier →
      SU2Carrier

    su2Neg :
      SU2Carrier →
      SU2Carrier

    su2Add :
      SU2Carrier →
      SU2Carrier →
      SU2Carrier

    su2PositiveBracket :
      SU2Basis →
      SU2Basis →
      SU2Carrier

    su2Bracket :
      SU2Carrier →
      SU2Carrier →
      SU2Carrier

    su2BracketSignedBasisBilinearity :
      (signX signY : YMSFGCLocalFiniteLie3Sign) →
      (x y : SU2Basis) →
      su2Bracket
        (su2Basis signX x)
        (su2Basis signY y)
      ≡
      su2Scale
        (localFiniteLie3MulSign signX signY)
        (su2PositiveBracket x y)

    su2BracketAntisymmetry :
      (x y : SU2Carrier) →
      su2Bracket x y
      ≡
      su2Neg (su2Bracket y x)

    su2Jacobi :
      (x y z : SU2Carrier) →
      su2Add
        (su2Add
          (su2Bracket x (su2Bracket y z))
          (su2Bracket y (su2Bracket z x)))
        (su2Bracket z (su2Bracket x y))
      ≡
      su2Zero

    su2Jacobi27 :
      (x y z : SU2Basis) →
      su2Add
        (su2Add
          (su2Bracket
            (su2Basis signPos x)
            (su2Bracket (su2Basis signPos y) (su2Basis signPos z)))
          (su2Bracket
            (su2Basis signPos y)
            (su2Bracket (su2Basis signPos z) (su2Basis signPos x))))
        (su2Bracket
          (su2Basis signPos z)
          (su2Bracket (su2Basis signPos x) (su2Basis signPos y)))
      ≡
      su2Zero

canonicalYMSFGCLocalFiniteSU2LieAlgebra :
  YMSFGCLocalFiniteSU2LieAlgebra
canonicalYMSFGCLocalFiniteSU2LieAlgebra =
  record
    { SU2Basis =
        YMSFGCLocalFiniteLie3Axis
    ; SU2Carrier =
        YMSFGCLocalFiniteLie3Carrier
    ; su2Zero =
        lieZero
    ; su2Basis =
        lieBasis
    ; su2Scale =
        localFiniteLie3Scale
    ; su2Neg =
        localFiniteLie3Neg
    ; su2Add =
        localFiniteLie3JacobiAdd
    ; su2PositiveBracket =
        localFiniteLie3PositiveBracket
    ; su2Bracket =
        localFiniteLie3Bracket
    ; su2BracketSignedBasisBilinearity =
        λ signX signY x y → refl
    ; su2BracketAntisymmetry =
        localFiniteLie3BracketAntisymmetry
    ; su2Jacobi =
        localFiniteLie3JacobiWitness
    ; su2Jacobi27 =
        localFiniteLie3PositiveAxisJacobi
    }

canonicalYMSFGCLocalFiniteLie3PrimitiveSupply :
  YMSFGCNonAbelianCovariantDerivativePrimitiveSupply
canonicalYMSFGCLocalFiniteLie3PrimitiveSupply =
  record
    { FibreLieAlgebraCarrier =
        YMSFGCLocalFiniteLie3Carrier
    ; zeroFibreLieAlgebra =
        lieZero
    ; addFibreLieAlgebra =
        localFiniteLie3JacobiAdd
    ; negateFibreLieAlgebra =
        localFiniteLie3Neg
    ; bracket =
        localFiniteLie3Bracket
    ; bracketAntisymmetry =
        localFiniteLie3BracketAntisymmetry
    ; jacobiWitness =
        localFiniteLie3JacobiWitness
    ; exteriorDerivative =
        λ section → lieZero
    ; connectionOneFormAsFibreAlgebra =
        λ A → lieZero
    ; curvatureAsFibreAlgebra =
        λ A → lieZero
    ; covariantDerivative =
        λ A section → lieZero
    ; covariantDerivativeFormula =
        λ A section → refl
    ; curvatureActionTheorem =
        λ A section → refl
    ; supplyBoundary =
        "Local finite 3-axis bracket skeleton only: [X,Y]=Z, [Y,Z]=X, [Z,X]=Y with signed antisymmetry"
        ∷ "A canonical SU2LieAlgebra symbol family now packages basis, bracket, signed-basis bilinearity, antisymmetry, and a 27-slot positive-axis Jacobi witness"
        ∷ "Jacobi is inhabited by a bounded finite epsilon check: zero is an identity and nonzero Jacobi-pair terms cancel inside this one-coefficient local surface"
        ∷ "The positive-axis SU(2)-style epsilon table is checked across all 27 ordered triples"
        ∷ "Connection, curvature, exterior derivative, and D_A are zero probes, so D_A formula and D_A^2=[F,_] are local degeneracy checks only"
        ∷ "No representation map embeds selected SFGC field-strength fibres into this concrete finite carrier"
        ∷ "This witness is non-promoting and cannot close Yang-Mills without SFGC fibre representation, non-flat connection, Hodge/current/action, and calibration receipts"
        ∷ []
    }

data YMSFGCGate3LocalFiniteYMInhabitedStatus : Set where
  gate3LocalFiniteYMInhabitantsAreConcreteButNonPromoting :
    YMSFGCGate3LocalFiniteYMInhabitedStatus

record YMSFGCGate3LocalFiniteYMInhabitedReceipt : Set₁ where
  field
    status :
      YMSFGCGate3LocalFiniteYMInhabitedStatus

    localFiniteSU2LieAlgebra :
      YMSFGCLocalFiniteSU2LieAlgebra

    localFiniteSU2LieAlgebraIsCanonical :
      localFiniteSU2LieAlgebra ≡ canonicalYMSFGCLocalFiniteSU2LieAlgebra

    localFiniteLie3PrimitiveSupply :
      YMSFGCNonAbelianCovariantDerivativePrimitiveSupply

    localFiniteLie3PrimitiveSupplyIsCanonical :
      localFiniteLie3PrimitiveSupply
      ≡
      canonicalYMSFGCLocalFiniteLie3PrimitiveSupply

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

    localFiniteJacobiWitness :
      (x y z : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3JacobiAdd
        (localFiniteLie3JacobiAdd
          (localFiniteLie3Bracket x (localFiniteLie3Bracket y z))
          (localFiniteLie3Bracket y (localFiniteLie3Bracket z x)))
        (localFiniteLie3Bracket z (localFiniteLie3Bracket x y))
      ≡
      lieZero

    localFiniteJacobiWitnessIsCanonical :
      localFiniteJacobiWitness
      ≡
      localFiniteLie3JacobiWitness

    exactStrictLieCarrierBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    exactStrictLieCarrierBlockerIsOpen :
      exactStrictLieCarrierBlocker
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    exactStrictTransportBlocker :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    exactStrictTransportBlockerIsOpen :
      exactStrictTransportBlocker
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    exactStrictVariationBlocker :
      YangMillsVariationalEquationMissingPrimitive

    exactStrictVariationBlockerIsOpen :
      exactStrictVariationBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    strictPromotion :
      Bool

    strictPromotionIsFalse :
      strictPromotion ≡ false

    receiptBoundary :
      List String

canonicalYMSFGCGate3LocalFiniteYMInhabitedReceipt :
  YMSFGCGate3LocalFiniteYMInhabitedReceipt
canonicalYMSFGCGate3LocalFiniteYMInhabitedReceipt =
  record
    { status =
        gate3LocalFiniteYMInhabitantsAreConcreteButNonPromoting
    ; localFiniteSU2LieAlgebra =
        canonicalYMSFGCLocalFiniteSU2LieAlgebra
    ; localFiniteSU2LieAlgebraIsCanonical =
        refl
    ; localFiniteLie3PrimitiveSupply =
        canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
    ; localFiniteLie3PrimitiveSupplyIsCanonical =
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
    ; localFiniteJacobiWitness =
        localFiniteLie3JacobiWitness
    ; localFiniteJacobiWitnessIsCanonical =
        refl
    ; exactStrictLieCarrierBlocker =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; exactStrictLieCarrierBlockerIsOpen =
        refl
    ; exactStrictTransportBlocker =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; exactStrictTransportBlockerIsOpen =
        refl
    ; exactStrictVariationBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; exactStrictVariationBlockerIsOpen =
        refl
    ; strictPromotion =
        false
    ; strictPromotionIsFalse =
        refl
    ; receiptBoundary =
        "Gate 3 now has concrete local finite inhabitants: canonicalYMSFGCLocalFiniteSU2LieAlgebra and canonicalYMSFGCLocalFiniteLie3PrimitiveSupply"
        ∷ "Gate 3 now also records the concrete YM module witnesses: canonicalSU2LieAlgebra, D_A, F_A, and ymAction"
        ∷ "Those inhabitants support the local finite Jacobi surface and primitive supply, but they do not inhabit the strict user-supplied Lie carrier target"
        ∷ "The strict Lie-carrier, field-strength transport, and variation-pairing blockers remain open and fail-closed"
        ∷ []
    }

record YMSFGCGate3ConcreteYMModuleWireup : Set₁ where
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

    exactStrictLieCarrierBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    exactStrictLieCarrierBlockerIsOpen :
      exactStrictLieCarrierBlocker
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    exactStrictTransportBlocker :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    exactStrictTransportBlockerIsOpen :
      exactStrictTransportBlocker
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    exactStrictVariationBlocker :
      YangMillsVariationalEquationMissingPrimitive

    exactStrictVariationBlockerIsOpen :
      exactStrictVariationBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    strictPromotion :
      Bool

    strictPromotionIsFalse :
      strictPromotion ≡ false

    wireupBoundary :
      List String

canonicalYMSFGCGate3ConcreteYMModuleWireup :
  YMSFGCGate3ConcreteYMModuleWireup
canonicalYMSFGCGate3ConcreteYMModuleWireup =
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
    ; exactStrictLieCarrierBlocker =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; exactStrictLieCarrierBlockerIsOpen =
        refl
    ; exactStrictTransportBlocker =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; exactStrictTransportBlockerIsOpen =
        refl
    ; exactStrictVariationBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; exactStrictVariationBlockerIsOpen =
        refl
    ; strictPromotion =
        false
    ; strictPromotionIsFalse =
        refl
    ; wireupBoundary =
        "Gate 3 wireup is concrete for canonicalSU2LieAlgebra, D_A, F_A, and ymAction"
        ∷ "The strict Lie-carrier, field-strength transport, and variation-pairing blockers remain exact and open"
        ∷ []
    }

localFiniteLie3BracketIsNonAbelian :
  localFiniteLie3Bracket
    (lieBasis signPos axisX)
    (lieBasis signPos axisY)
  ≡
  lieBasis signPos axisZ
localFiniteLie3BracketIsNonAbelian = refl

localFiniteLie3AxisTracePairing :
  YMSFGCLocalFiniteLie3Axis →
  YMSFGCLocalFiniteLie3Axis →
  ℤ
localFiniteLie3AxisTracePairing axisX axisX = + 1
localFiniteLie3AxisTracePairing axisX axisY = + 0
localFiniteLie3AxisTracePairing axisX axisZ = + 0
localFiniteLie3AxisTracePairing axisY axisX = + 0
localFiniteLie3AxisTracePairing axisY axisY = + 1
localFiniteLie3AxisTracePairing axisY axisZ = + 0
localFiniteLie3AxisTracePairing axisZ axisX = + 0
localFiniteLie3AxisTracePairing axisZ axisY = + 0
localFiniteLie3AxisTracePairing axisZ axisZ = + 1

localFiniteLie3TracePairing :
  YMSFGCLocalFiniteLie3Carrier →
  YMSFGCLocalFiniteLie3Carrier →
  ℤ
localFiniteLie3TracePairing lieZero y = + 0
localFiniteLie3TracePairing x lieZero = + 0
localFiniteLie3TracePairing
  (lieBasis signX axisA)
  (lieBasis signY axisB) =
  localFiniteLie3AxisTracePairing axisA axisB

localFiniteLie3TracePairingNegInvariant :
  (x y : YMSFGCLocalFiniteLie3Carrier) →
  localFiniteLie3TracePairing
    (localFiniteLie3Neg x)
    (localFiniteLie3Neg y)
  ≡
  localFiniteLie3TracePairing x y
localFiniteLie3TracePairingNegInvariant lieZero y = refl
localFiniteLie3TracePairingNegInvariant (lieBasis sign axis) lieZero = refl
localFiniteLie3TracePairingNegInvariant
  (lieBasis signX axisX)
  (lieBasis signY axisX) = refl
localFiniteLie3TracePairingNegInvariant
  (lieBasis signX axisX)
  (lieBasis signY axisY) = refl
localFiniteLie3TracePairingNegInvariant
  (lieBasis signX axisX)
  (lieBasis signY axisZ) = refl
localFiniteLie3TracePairingNegInvariant
  (lieBasis signX axisY)
  (lieBasis signY axisX) = refl
localFiniteLie3TracePairingNegInvariant
  (lieBasis signX axisY)
  (lieBasis signY axisY) = refl
localFiniteLie3TracePairingNegInvariant
  (lieBasis signX axisY)
  (lieBasis signY axisZ) = refl
localFiniteLie3TracePairingNegInvariant
  (lieBasis signX axisZ)
  (lieBasis signY axisX) = refl
localFiniteLie3TracePairingNegInvariant
  (lieBasis signX axisZ)
  (lieBasis signY axisY) = refl
localFiniteLie3TracePairingNegInvariant
  (lieBasis signX axisZ)
  (lieBasis signY axisZ) = refl

localFiniteLie3PhaseAdjointAction :
  SPTI4.Phase4 →
  YMSFGCLocalFiniteLie3Carrier →
  YMSFGCLocalFiniteLie3Carrier
localFiniteLie3PhaseAdjointAction SPTI4.φ0 x = x
localFiniteLie3PhaseAdjointAction SPTI4.φ1 x = localFiniteLie3Neg x
localFiniteLie3PhaseAdjointAction SPTI4.φ2 x = x
localFiniteLie3PhaseAdjointAction SPTI4.φ3 x = localFiniteLie3Neg x

localFiniteLie3PhaseAdjointTraceAdInvariance :
  (phase : SPTI4.Phase4) →
  (x y : YMSFGCLocalFiniteLie3Carrier) →
  localFiniteLie3TracePairing
    (localFiniteLie3PhaseAdjointAction phase x)
    (localFiniteLie3PhaseAdjointAction phase y)
  ≡
  localFiniteLie3TracePairing x y
localFiniteLie3PhaseAdjointTraceAdInvariance SPTI4.φ0 x y = refl
localFiniteLie3PhaseAdjointTraceAdInvariance SPTI4.φ1 x y =
  localFiniteLie3TracePairingNegInvariant x y
localFiniteLie3PhaseAdjointTraceAdInvariance SPTI4.φ2 x y = refl
localFiniteLie3PhaseAdjointTraceAdInvariance SPTI4.φ3 x y =
  localFiniteLie3TracePairingNegInvariant x y

localFiniteLie3PhaseAdjointActionNontrivial :
  localFiniteLie3PhaseAdjointAction
    SPTI4.φ1
    (lieBasis signPos axisX)
  ≡
  lieBasis signNeg axisX
localFiniteLie3PhaseAdjointActionNontrivial = refl

data YMSFGCLieValued0Form : Set where
  lieValued0 : YMSFGCLocalFiniteLie3Carrier → YMSFGCLieValued0Form

data YMSFGCLieValued1Form : Set where
  lieValued1 : YMSFGCLocalFiniteLie3Carrier → YMSFGCLieValued1Form

data YMSFGCLieValued2Form : Set where
  lieValued2 : YMSFGCLocalFiniteLie3Carrier → YMSFGCLieValued2Form

lieValued0Carrier :
  YMSFGCLieValued0Form →
  YMSFGCLocalFiniteLie3Carrier
lieValued0Carrier (lieValued0 section) = section

lieValued1Carrier :
  YMSFGCLieValued1Form →
  YMSFGCLocalFiniteLie3Carrier
lieValued1Carrier (lieValued1 oneForm) = oneForm

lieValued2Carrier :
  YMSFGCLieValued2Form →
  YMSFGCLocalFiniteLie3Carrier
lieValued2Carrier (lieValued2 twoForm) = twoForm

localFiniteLie3ExteriorDerivative0Form :
  YMSFGCLieValued0Form →
  YMSFGCLieValued1Form
localFiniteLie3ExteriorDerivative0Form (lieValued0 section) =
  lieValued1
    (YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.exteriorDerivative
      canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
      section)

localFiniteLie3A1Form :
  SFGC.GaugeField →
  YMSFGCLieValued1Form
localFiniteLie3A1Form A =
  lieValued1
    (YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.connectionOneFormAsFibreAlgebra
      canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
      A)

localFiniteLie3FA2Form :
  SFGC.GaugeField →
  YMSFGCLieValued2Form
localFiniteLie3FA2Form A =
  lieValued2
    (YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.curvatureAsFibreAlgebra
      canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
      A)

localFiniteLie3DA0Form :
  SFGC.GaugeField →
  YMSFGCLieValued0Form →
  YMSFGCLieValued0Form
localFiniteLie3DA0Form A (lieValued0 section) =
  lieValued0
    (YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.covariantDerivative
      canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
      A
      section)

localFiniteLie3CurvatureBracketActionOn0Form :
  YMSFGCLieValued2Form →
  YMSFGCLieValued0Form →
  YMSFGCLieValued0Form
localFiniteLie3CurvatureBracketActionOn0Form
  (lieValued2 curvature)
  (lieValued0 section) =
  lieValued0 (localFiniteLie3Bracket curvature section)

localFiniteLie3DAExpectedRHS0Form :
  SFGC.GaugeField →
  YMSFGCLocalFiniteLie3Carrier →
  YMSFGCLieValued0Form
localFiniteLie3DAExpectedRHS0Form A section =
  lieValued0
    (localFiniteLie3JacobiAdd
      (YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.exteriorDerivative
        canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
        section)
      (localFiniteLie3Bracket
        (YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.connectionOneFormAsFibreAlgebra
          canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
          A)
        section))

localFiniteLie3DAFormulaOn0Forms :
  (A : SFGC.GaugeField) →
  (section : YMSFGCLocalFiniteLie3Carrier) →
  localFiniteLie3DA0Form A (lieValued0 section)
  ≡
  localFiniteLie3DAExpectedRHS0Form A section
localFiniteLie3DAFormulaOn0Forms A section =
  cong lieValued0
    (YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.covariantDerivativeFormula
      canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
      A
      section)

localFiniteLie3DASquaredEqualsBracketFAOn0Forms :
  (A : SFGC.GaugeField) →
  (section : YMSFGCLocalFiniteLie3Carrier) →
  localFiniteLie3DA0Form
    A
    (localFiniteLie3DA0Form A (lieValued0 section))
  ≡
  localFiniteLie3CurvatureBracketActionOn0Form
    (localFiniteLie3FA2Form A)
    (lieValued0 section)
localFiniteLie3DASquaredEqualsBracketFAOn0Forms A section =
  cong lieValued0
    (YMSFGCNonAbelianCovariantDerivativePrimitiveSupply.curvatureActionTheorem
      canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
      A
      section)

record YMSFGCLocalFiniteLieValuedFormsAndCurvature : Set₁ where
  field
    section0Form :
      YMSFGCLocalFiniteLie3Carrier →
      YMSFGCLieValued0Form

    connectionA1Form :
      SFGC.GaugeField →
      YMSFGCLieValued1Form

    curvatureFA2Form :
      SFGC.GaugeField →
      YMSFGCLieValued2Form

    exteriorDerivativeOn0Forms :
      YMSFGCLieValued0Form →
      YMSFGCLieValued1Form

    covariantDerivativeDAOn0Forms :
      SFGC.GaugeField →
      YMSFGCLieValued0Form →
      YMSFGCLieValued0Form

    curvatureBracketActionOn0Forms :
      YMSFGCLieValued2Form →
      YMSFGCLieValued0Form →
      YMSFGCLieValued0Form

    covariantDerivativeDAFormulaOn0Forms :
      (A : SFGC.GaugeField) →
      (section : YMSFGCLocalFiniteLie3Carrier) →
      covariantDerivativeDAOn0Forms A (section0Form section)
      ≡
      localFiniteLie3DAExpectedRHS0Form A section

    curvatureActionDASquaredOn0Forms :
      (A : SFGC.GaugeField) →
      (section : YMSFGCLocalFiniteLie3Carrier) →
      covariantDerivativeDAOn0Forms
        A
        (covariantDerivativeDAOn0Forms A (section0Form section))
      ≡
      curvatureBracketActionOn0Forms
        (curvatureFA2Form A)
        (section0Form section)

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

    boundary :
      List String

canonicalYMSFGCLocalFiniteLieValuedFormsAndCurvature :
  YMSFGCLocalFiniteLieValuedFormsAndCurvature
canonicalYMSFGCLocalFiniteLieValuedFormsAndCurvature =
  record
    { section0Form =
        lieValued0
    ; connectionA1Form =
        localFiniteLie3A1Form
    ; curvatureFA2Form =
        localFiniteLie3FA2Form
    ; exteriorDerivativeOn0Forms =
        localFiniteLie3ExteriorDerivative0Form
    ; covariantDerivativeDAOn0Forms =
        localFiniteLie3DA0Form
    ; curvatureBracketActionOn0Forms =
        localFiniteLie3CurvatureBracketActionOn0Form
    ; covariantDerivativeDAFormulaOn0Forms =
        localFiniteLie3DAFormulaOn0Forms
    ; curvatureActionDASquaredOn0Forms =
        localFiniteLie3DASquaredEqualsBracketFAOn0Forms
    ; promoted =
        false
    ; promotedIsFalse =
        refl
    ; boundary =
        "Lie-valued forms are explicit on a local finite non-abelian carrier: 0-forms, A as 1-form, and F_A as 2-form wrappers"
        ∷ "D_A is exposed as a concrete operator on Lie-valued 0-forms through the local finite covariant derivative primitive"
        ∷ "D_A formula is witnessed as D_A(s) = d(s) + [A,s] using the local finite supply"
        ∷ "Curvature action is witnessed as D_A^2(s) = [F_A,s] on the same local finite surface"
        ∷ "This package remains non-promoting because connection, curvature, and derivative primitives are degenerate zero probes below the missing SFGC representation map"
        ∷ []
    }

data YMSFGCLocalFiniteSU3Axis : Set where
  su3Axis1 : YMSFGCLocalFiniteSU3Axis
  su3Axis2 : YMSFGCLocalFiniteSU3Axis
  su3Axis3 : YMSFGCLocalFiniteSU3Axis
  su3Axis4 : YMSFGCLocalFiniteSU3Axis
  su3Axis5 : YMSFGCLocalFiniteSU3Axis
  su3Axis6 : YMSFGCLocalFiniteSU3Axis
  su3Axis7 : YMSFGCLocalFiniteSU3Axis
  su3Axis8 : YMSFGCLocalFiniteSU3Axis

data YMSFGCLocalFiniteSU3Carrier : Set where
  su3Zero : YMSFGCLocalFiniteSU3Carrier
  su3Basis :
    YMSFGCLocalFiniteLie3Sign →
    YMSFGCLocalFiniteSU3Axis →
    YMSFGCLocalFiniteSU3Carrier

localFiniteSU3EmbedAxis :
  YMSFGCLocalFiniteLie3Axis →
  YMSFGCLocalFiniteSU3Axis
localFiniteSU3EmbedAxis axisX = su3Axis1
localFiniteSU3EmbedAxis axisY = su3Axis2
localFiniteSU3EmbedAxis axisZ = su3Axis3

localFiniteSU3Embed :
  YMSFGCLocalFiniteLie3Carrier →
  YMSFGCLocalFiniteSU3Carrier
localFiniteSU3Embed lieZero = su3Zero
localFiniteSU3Embed (lieBasis sign axis) =
  su3Basis sign (localFiniteSU3EmbedAxis axis)

localFiniteSU3Neg :
  YMSFGCLocalFiniteSU3Carrier →
  YMSFGCLocalFiniteSU3Carrier
localFiniteSU3Neg su3Zero = su3Zero
localFiniteSU3Neg (su3Basis sign axis) =
  su3Basis (localFiniteLie3NegSign sign) axis

localFiniteSU3Scale :
  YMSFGCLocalFiniteLie3Sign →
  YMSFGCLocalFiniteSU3Carrier →
  YMSFGCLocalFiniteSU3Carrier
localFiniteSU3Scale sign su3Zero = su3Zero
localFiniteSU3Scale sign (su3Basis basisSign axis) =
  su3Basis (localFiniteLie3MulSign sign basisSign) axis

data YMSFGCLocalFiniteSU3StructureCoefficient : Set where
  su3CoeffOne : YMSFGCLocalFiniteSU3StructureCoefficient
  su3CoeffHalf : YMSFGCLocalFiniteSU3StructureCoefficient
  su3CoeffSqrt3Over2 : YMSFGCLocalFiniteSU3StructureCoefficient

record YMSFGCLocalFiniteSU3StructureTerm : Set where
  constructor su3StructureTerm
  field
    structureTermSign :
      YMSFGCLocalFiniteLie3Sign

    structureTermCoefficient :
      YMSFGCLocalFiniteSU3StructureCoefficient

    structureTermAxis :
      YMSFGCLocalFiniteSU3Axis

localFiniteSU3ScaleStructureTerm :
  YMSFGCLocalFiniteLie3Sign →
  YMSFGCLocalFiniteSU3StructureTerm →
  YMSFGCLocalFiniteSU3StructureTerm
localFiniteSU3ScaleStructureTerm sign
  (su3StructureTerm termSign coefficient axis) =
  su3StructureTerm
    (localFiniteLie3MulSign sign termSign)
    coefficient
    axis

localFiniteSU3ScaleStructureOutput :
  YMSFGCLocalFiniteLie3Sign →
  List YMSFGCLocalFiniteSU3StructureTerm →
  List YMSFGCLocalFiniteSU3StructureTerm
localFiniteSU3ScaleStructureOutput sign [] = []
localFiniteSU3ScaleStructureOutput sign (term ∷ terms) =
  localFiniteSU3ScaleStructureTerm sign term
  ∷ localFiniteSU3ScaleStructureOutput sign terms

localFiniteSU3StructureSingle :
  YMSFGCLocalFiniteLie3Sign →
  YMSFGCLocalFiniteSU3StructureCoefficient →
  YMSFGCLocalFiniteSU3Axis →
  List YMSFGCLocalFiniteSU3StructureTerm
localFiniteSU3StructureSingle sign coefficient axis =
  su3StructureTerm sign coefficient axis ∷ []

localFiniteSU3StructureDouble :
  YMSFGCLocalFiniteLie3Sign →
  YMSFGCLocalFiniteSU3StructureCoefficient →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteLie3Sign →
  YMSFGCLocalFiniteSU3StructureCoefficient →
  YMSFGCLocalFiniteSU3Axis →
  List YMSFGCLocalFiniteSU3StructureTerm
localFiniteSU3StructureDouble signA coefficientA axisA signB coefficientB axisB =
  su3StructureTerm signA coefficientA axisA
  ∷ su3StructureTerm signB coefficientB axisB
  ∷ []

localFiniteSU3PositiveStructureOutput :
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  List YMSFGCLocalFiniteSU3StructureTerm
localFiniteSU3PositiveStructureOutput su3Axis1 su3Axis2 =
  localFiniteSU3StructureSingle signPos su3CoeffOne su3Axis3
localFiniteSU3PositiveStructureOutput su3Axis2 su3Axis3 =
  localFiniteSU3StructureSingle signPos su3CoeffOne su3Axis1
localFiniteSU3PositiveStructureOutput su3Axis3 su3Axis1 =
  localFiniteSU3StructureSingle signPos su3CoeffOne su3Axis2
localFiniteSU3PositiveStructureOutput su3Axis2 su3Axis1 =
  localFiniteSU3StructureSingle signNeg su3CoeffOne su3Axis3
localFiniteSU3PositiveStructureOutput su3Axis3 su3Axis2 =
  localFiniteSU3StructureSingle signNeg su3CoeffOne su3Axis1
localFiniteSU3PositiveStructureOutput su3Axis1 su3Axis3 =
  localFiniteSU3StructureSingle signNeg su3CoeffOne su3Axis2
localFiniteSU3PositiveStructureOutput su3Axis1 su3Axis4 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis7
localFiniteSU3PositiveStructureOutput su3Axis4 su3Axis7 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis1
localFiniteSU3PositiveStructureOutput su3Axis7 su3Axis1 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis4
localFiniteSU3PositiveStructureOutput su3Axis4 su3Axis1 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis7
localFiniteSU3PositiveStructureOutput su3Axis7 su3Axis4 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis1
localFiniteSU3PositiveStructureOutput su3Axis1 su3Axis7 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis4
localFiniteSU3PositiveStructureOutput su3Axis1 su3Axis5 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis6
localFiniteSU3PositiveStructureOutput su3Axis5 su3Axis6 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis1
localFiniteSU3PositiveStructureOutput su3Axis6 su3Axis1 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis5
localFiniteSU3PositiveStructureOutput su3Axis5 su3Axis1 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis6
localFiniteSU3PositiveStructureOutput su3Axis6 su3Axis5 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis1
localFiniteSU3PositiveStructureOutput su3Axis1 su3Axis6 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis5
localFiniteSU3PositiveStructureOutput su3Axis2 su3Axis4 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis6
localFiniteSU3PositiveStructureOutput su3Axis4 su3Axis6 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis2
localFiniteSU3PositiveStructureOutput su3Axis6 su3Axis2 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis4
localFiniteSU3PositiveStructureOutput su3Axis4 su3Axis2 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis6
localFiniteSU3PositiveStructureOutput su3Axis6 su3Axis4 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis2
localFiniteSU3PositiveStructureOutput su3Axis2 su3Axis6 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis4
localFiniteSU3PositiveStructureOutput su3Axis2 su3Axis5 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis7
localFiniteSU3PositiveStructureOutput su3Axis5 su3Axis7 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis2
localFiniteSU3PositiveStructureOutput su3Axis7 su3Axis2 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis5
localFiniteSU3PositiveStructureOutput su3Axis5 su3Axis2 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis7
localFiniteSU3PositiveStructureOutput su3Axis7 su3Axis5 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis2
localFiniteSU3PositiveStructureOutput su3Axis2 su3Axis7 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis5
localFiniteSU3PositiveStructureOutput su3Axis3 su3Axis4 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis5
localFiniteSU3PositiveStructureOutput su3Axis4 su3Axis5 =
  localFiniteSU3StructureDouble
    signPos su3CoeffHalf su3Axis3
    signPos su3CoeffSqrt3Over2 su3Axis8
localFiniteSU3PositiveStructureOutput su3Axis5 su3Axis3 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis4
localFiniteSU3PositiveStructureOutput su3Axis4 su3Axis3 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis5
localFiniteSU3PositiveStructureOutput su3Axis5 su3Axis4 =
  localFiniteSU3StructureDouble
    signNeg su3CoeffHalf su3Axis3
    signNeg su3CoeffSqrt3Over2 su3Axis8
localFiniteSU3PositiveStructureOutput su3Axis3 su3Axis5 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis4
localFiniteSU3PositiveStructureOutput su3Axis3 su3Axis6 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis7
localFiniteSU3PositiveStructureOutput su3Axis6 su3Axis7 =
  localFiniteSU3StructureDouble
    signNeg su3CoeffHalf su3Axis3
    signPos su3CoeffSqrt3Over2 su3Axis8
localFiniteSU3PositiveStructureOutput su3Axis7 su3Axis3 =
  localFiniteSU3StructureSingle signNeg su3CoeffHalf su3Axis6
localFiniteSU3PositiveStructureOutput su3Axis6 su3Axis3 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis7
localFiniteSU3PositiveStructureOutput su3Axis7 su3Axis6 =
  localFiniteSU3StructureDouble
    signPos su3CoeffHalf su3Axis3
    signNeg su3CoeffSqrt3Over2 su3Axis8
localFiniteSU3PositiveStructureOutput su3Axis3 su3Axis7 =
  localFiniteSU3StructureSingle signPos su3CoeffHalf su3Axis6
localFiniteSU3PositiveStructureOutput su3Axis4 su3Axis8 =
  localFiniteSU3StructureSingle signNeg su3CoeffSqrt3Over2 su3Axis5
localFiniteSU3PositiveStructureOutput su3Axis8 su3Axis4 =
  localFiniteSU3StructureSingle signPos su3CoeffSqrt3Over2 su3Axis5
localFiniteSU3PositiveStructureOutput su3Axis5 su3Axis8 =
  localFiniteSU3StructureSingle signPos su3CoeffSqrt3Over2 su3Axis4
localFiniteSU3PositiveStructureOutput su3Axis8 su3Axis5 =
  localFiniteSU3StructureSingle signNeg su3CoeffSqrt3Over2 su3Axis4
localFiniteSU3PositiveStructureOutput su3Axis6 su3Axis8 =
  localFiniteSU3StructureSingle signNeg su3CoeffSqrt3Over2 su3Axis7
localFiniteSU3PositiveStructureOutput su3Axis8 su3Axis6 =
  localFiniteSU3StructureSingle signPos su3CoeffSqrt3Over2 su3Axis7
localFiniteSU3PositiveStructureOutput su3Axis7 su3Axis8 =
  localFiniteSU3StructureSingle signPos su3CoeffSqrt3Over2 su3Axis6
localFiniteSU3PositiveStructureOutput su3Axis8 su3Axis7 =
  localFiniteSU3StructureSingle signNeg su3CoeffSqrt3Over2 su3Axis6
localFiniteSU3PositiveStructureOutput _ _ = []

localFiniteSU3StructureBracket :
  YMSFGCLocalFiniteSU3Carrier →
  YMSFGCLocalFiniteSU3Carrier →
  List YMSFGCLocalFiniteSU3StructureTerm
localFiniteSU3StructureBracket su3Zero y = []
localFiniteSU3StructureBracket x su3Zero = []
localFiniteSU3StructureBracket (su3Basis signA axisA) (su3Basis signB axisB) =
  localFiniteSU3ScaleStructureOutput
    (localFiniteLie3MulSign signA signB)
    (localFiniteSU3PositiveStructureOutput axisA axisB)

localFiniteSU3PositiveBracket :
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Carrier
localFiniteSU3PositiveBracket su3Axis1 su3Axis2 =
  su3Basis signPos su3Axis3
localFiniteSU3PositiveBracket su3Axis2 su3Axis3 =
  su3Basis signPos su3Axis1
localFiniteSU3PositiveBracket su3Axis3 su3Axis1 =
  su3Basis signPos su3Axis2
localFiniteSU3PositiveBracket su3Axis2 su3Axis1 =
  su3Basis signNeg su3Axis3
localFiniteSU3PositiveBracket su3Axis3 su3Axis2 =
  su3Basis signNeg su3Axis1
localFiniteSU3PositiveBracket su3Axis1 su3Axis3 =
  su3Basis signNeg su3Axis2
localFiniteSU3PositiveBracket su3Axis1 su3Axis4 =
  su3Basis signPos su3Axis7
localFiniteSU3PositiveBracket su3Axis4 su3Axis7 =
  su3Basis signPos su3Axis1
localFiniteSU3PositiveBracket su3Axis7 su3Axis1 =
  su3Basis signPos su3Axis4
localFiniteSU3PositiveBracket su3Axis4 su3Axis1 =
  su3Basis signNeg su3Axis7
localFiniteSU3PositiveBracket su3Axis7 su3Axis4 =
  su3Basis signNeg su3Axis1
localFiniteSU3PositiveBracket su3Axis1 su3Axis7 =
  su3Basis signNeg su3Axis4
localFiniteSU3PositiveBracket su3Axis1 su3Axis5 =
  su3Basis signNeg su3Axis6
localFiniteSU3PositiveBracket su3Axis5 su3Axis6 =
  su3Basis signNeg su3Axis1
localFiniteSU3PositiveBracket su3Axis6 su3Axis1 =
  su3Basis signNeg su3Axis5
localFiniteSU3PositiveBracket su3Axis5 su3Axis1 =
  su3Basis signPos su3Axis6
localFiniteSU3PositiveBracket su3Axis6 su3Axis5 =
  su3Basis signPos su3Axis1
localFiniteSU3PositiveBracket su3Axis1 su3Axis6 =
  su3Basis signPos su3Axis5
localFiniteSU3PositiveBracket su3Axis2 su3Axis4 =
  su3Basis signPos su3Axis6
localFiniteSU3PositiveBracket su3Axis4 su3Axis6 =
  su3Basis signPos su3Axis2
localFiniteSU3PositiveBracket su3Axis6 su3Axis2 =
  su3Basis signPos su3Axis4
localFiniteSU3PositiveBracket su3Axis4 su3Axis2 =
  su3Basis signNeg su3Axis6
localFiniteSU3PositiveBracket su3Axis6 su3Axis4 =
  su3Basis signNeg su3Axis2
localFiniteSU3PositiveBracket su3Axis2 su3Axis6 =
  su3Basis signNeg su3Axis4
localFiniteSU3PositiveBracket su3Axis2 su3Axis5 =
  su3Basis signPos su3Axis7
localFiniteSU3PositiveBracket su3Axis5 su3Axis7 =
  su3Basis signPos su3Axis2
localFiniteSU3PositiveBracket su3Axis7 su3Axis2 =
  su3Basis signPos su3Axis5
localFiniteSU3PositiveBracket su3Axis5 su3Axis2 =
  su3Basis signNeg su3Axis7
localFiniteSU3PositiveBracket su3Axis7 su3Axis5 =
  su3Basis signNeg su3Axis2
localFiniteSU3PositiveBracket su3Axis2 su3Axis7 =
  su3Basis signNeg su3Axis5
localFiniteSU3PositiveBracket su3Axis3 su3Axis4 =
  su3Basis signPos su3Axis5
localFiniteSU3PositiveBracket su3Axis4 su3Axis5 =
  su3Basis signPos su3Axis3
localFiniteSU3PositiveBracket su3Axis5 su3Axis3 =
  su3Basis signPos su3Axis4
localFiniteSU3PositiveBracket su3Axis4 su3Axis3 =
  su3Basis signNeg su3Axis5
localFiniteSU3PositiveBracket su3Axis5 su3Axis4 =
  su3Basis signNeg su3Axis3
localFiniteSU3PositiveBracket su3Axis3 su3Axis5 =
  su3Basis signNeg su3Axis4
localFiniteSU3PositiveBracket su3Axis3 su3Axis6 =
  su3Basis signNeg su3Axis7
localFiniteSU3PositiveBracket su3Axis6 su3Axis7 =
  su3Basis signNeg su3Axis3
localFiniteSU3PositiveBracket su3Axis7 su3Axis3 =
  su3Basis signNeg su3Axis6
localFiniteSU3PositiveBracket su3Axis6 su3Axis3 =
  su3Basis signPos su3Axis7
localFiniteSU3PositiveBracket su3Axis7 su3Axis6 =
  su3Basis signPos su3Axis3
localFiniteSU3PositiveBracket su3Axis3 su3Axis7 =
  su3Basis signPos su3Axis6
localFiniteSU3PositiveBracket su3Axis4 su3Axis8 =
  su3Basis signNeg su3Axis5
localFiniteSU3PositiveBracket su3Axis8 su3Axis4 =
  su3Basis signPos su3Axis5
localFiniteSU3PositiveBracket su3Axis5 su3Axis8 =
  su3Basis signPos su3Axis4
localFiniteSU3PositiveBracket su3Axis8 su3Axis5 =
  su3Basis signNeg su3Axis4
localFiniteSU3PositiveBracket su3Axis6 su3Axis8 =
  su3Basis signNeg su3Axis7
localFiniteSU3PositiveBracket su3Axis8 su3Axis6 =
  su3Basis signPos su3Axis7
localFiniteSU3PositiveBracket su3Axis7 su3Axis8 =
  su3Basis signPos su3Axis6
localFiniteSU3PositiveBracket su3Axis8 su3Axis7 =
  su3Basis signNeg su3Axis6
localFiniteSU3PositiveBracket _ _ = su3Zero

localFiniteSU3Bracket :
  YMSFGCLocalFiniteSU3Carrier →
  YMSFGCLocalFiniteSU3Carrier →
  YMSFGCLocalFiniteSU3Carrier
localFiniteSU3Bracket su3Zero y = su3Zero
localFiniteSU3Bracket x su3Zero = su3Zero
localFiniteSU3Bracket (su3Basis signA axisA) (su3Basis signB axisB) =
  localFiniteSU3Scale
    (localFiniteLie3MulSign signA signB)
    (localFiniteSU3PositiveBracket axisA axisB)

localFiniteSU3EmbeddedSU2XYBracket :
  localFiniteSU3Bracket
    (localFiniteSU3Embed (lieBasis signPos axisX))
    (localFiniteSU3Embed (lieBasis signPos axisY))
  ≡
  localFiniteSU3Embed (lieBasis signPos axisZ)
localFiniteSU3EmbeddedSU2XYBracket = refl

localFiniteSU3EmbeddedSU2YZBracket :
  localFiniteSU3Bracket
    (localFiniteSU3Embed (lieBasis signPos axisY))
    (localFiniteSU3Embed (lieBasis signPos axisZ))
  ≡
  localFiniteSU3Embed (lieBasis signPos axisX)
localFiniteSU3EmbeddedSU2YZBracket = refl

localFiniteSU3EmbeddedSU2ZXBracket :
  localFiniteSU3Bracket
    (localFiniteSU3Embed (lieBasis signPos axisZ))
    (localFiniteSU3Embed (lieBasis signPos axisX))
  ≡
  localFiniteSU3Embed (lieBasis signPos axisY)
localFiniteSU3EmbeddedSU2ZXBracket = refl

localFiniteSU3EmbeddedSU2YXBracket :
  localFiniteSU3Bracket
    (localFiniteSU3Embed (lieBasis signPos axisY))
    (localFiniteSU3Embed (lieBasis signPos axisX))
  ≡
  localFiniteSU3Neg (localFiniteSU3Embed (lieBasis signPos axisZ))
localFiniteSU3EmbeddedSU2YXBracket = refl

localFiniteSU3Root14Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis1)
    (su3Basis signPos su3Axis4)
  ≡
  su3Basis signPos su3Axis7
localFiniteSU3Root14Bracket = refl

localFiniteSU3Root15Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis1)
    (su3Basis signPos su3Axis5)
  ≡
  su3Basis signNeg su3Axis6
localFiniteSU3Root15Bracket = refl

localFiniteSU3Root24Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis2)
    (su3Basis signPos su3Axis4)
  ≡
  su3Basis signPos su3Axis6
localFiniteSU3Root24Bracket = refl

localFiniteSU3Root25Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis2)
    (su3Basis signPos su3Axis5)
  ≡
  su3Basis signPos su3Axis7
localFiniteSU3Root25Bracket = refl

localFiniteSU3Root34Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis3)
    (su3Basis signPos su3Axis4)
  ≡
  su3Basis signPos su3Axis5
localFiniteSU3Root34Bracket = refl

localFiniteSU3Root36Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis3)
    (su3Basis signPos su3Axis6)
  ≡
  su3Basis signNeg su3Axis7
localFiniteSU3Root36Bracket = refl

localFiniteSU3Cartan48Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis4)
    (su3Basis signPos su3Axis8)
  ≡
  su3Basis signNeg su3Axis5
localFiniteSU3Cartan48Bracket = refl

localFiniteSU3Cartan84Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis8)
    (su3Basis signPos su3Axis4)
  ≡
  su3Basis signPos su3Axis5
localFiniteSU3Cartan84Bracket = refl

localFiniteSU3Cartan58Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis5)
    (su3Basis signPos su3Axis8)
  ≡
  su3Basis signPos su3Axis4
localFiniteSU3Cartan58Bracket = refl

localFiniteSU3Cartan85Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis8)
    (su3Basis signPos su3Axis5)
  ≡
  su3Basis signNeg su3Axis4
localFiniteSU3Cartan85Bracket = refl

localFiniteSU3Cartan68Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis6)
    (su3Basis signPos su3Axis8)
  ≡
  su3Basis signNeg su3Axis7
localFiniteSU3Cartan68Bracket = refl

localFiniteSU3Cartan86Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis8)
    (su3Basis signPos su3Axis6)
  ≡
  su3Basis signPos su3Axis7
localFiniteSU3Cartan86Bracket = refl

localFiniteSU3Cartan78Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis7)
    (su3Basis signPos su3Axis8)
  ≡
  su3Basis signPos su3Axis6
localFiniteSU3Cartan78Bracket = refl

localFiniteSU3Cartan87Bracket :
  localFiniteSU3Bracket
    (su3Basis signPos su3Axis8)
    (su3Basis signPos su3Axis7)
  ≡
  su3Basis signNeg su3Axis6
localFiniteSU3Cartan87Bracket = refl

localFiniteSU3Structure12CoefficientBracket :
  localFiniteSU3StructureBracket
    (su3Basis signPos su3Axis1)
    (su3Basis signPos su3Axis2)
  ≡
  su3StructureTerm signPos su3CoeffOne su3Axis3
  ∷ []
localFiniteSU3Structure12CoefficientBracket = refl

localFiniteSU3Structure14CoefficientBracket :
  localFiniteSU3StructureBracket
    (su3Basis signPos su3Axis1)
    (su3Basis signPos su3Axis4)
  ≡
  su3StructureTerm signPos su3CoeffHalf su3Axis7
  ∷ []
localFiniteSU3Structure14CoefficientBracket = refl

localFiniteSU3Structure45MultiOutputBracket :
  localFiniteSU3StructureBracket
    (su3Basis signPos su3Axis4)
    (su3Basis signPos su3Axis5)
  ≡
  su3StructureTerm signPos su3CoeffHalf su3Axis3
  ∷ su3StructureTerm signPos su3CoeffSqrt3Over2 su3Axis8
  ∷ []
localFiniteSU3Structure45MultiOutputBracket = refl

localFiniteSU3Structure54MultiOutputBracket :
  localFiniteSU3StructureBracket
    (su3Basis signPos su3Axis5)
    (su3Basis signPos su3Axis4)
  ≡
  su3StructureTerm signNeg su3CoeffHalf su3Axis3
  ∷ su3StructureTerm signNeg su3CoeffSqrt3Over2 su3Axis8
  ∷ []
localFiniteSU3Structure54MultiOutputBracket = refl

localFiniteSU3Structure67MultiOutputBracket :
  localFiniteSU3StructureBracket
    (su3Basis signPos su3Axis6)
    (su3Basis signPos su3Axis7)
  ≡
  su3StructureTerm signNeg su3CoeffHalf su3Axis3
  ∷ su3StructureTerm signPos su3CoeffSqrt3Over2 su3Axis8
  ∷ []
localFiniteSU3Structure67MultiOutputBracket = refl

localFiniteSU3Structure76MultiOutputBracket :
  localFiniteSU3StructureBracket
    (su3Basis signPos su3Axis7)
    (su3Basis signPos su3Axis6)
  ≡
  su3StructureTerm signPos su3CoeffHalf su3Axis3
  ∷ su3StructureTerm signNeg su3CoeffSqrt3Over2 su3Axis8
  ∷ []
localFiniteSU3Structure76MultiOutputBracket = refl

localFiniteSU3Structure48CoefficientBracket :
  localFiniteSU3StructureBracket
    (su3Basis signPos su3Axis4)
    (su3Basis signPos su3Axis8)
  ≡
  su3StructureTerm signNeg su3CoeffSqrt3Over2 su3Axis5
  ∷ []
localFiniteSU3Structure48CoefficientBracket = refl

localFiniteSU3Structure58CoefficientBracket :
  localFiniteSU3StructureBracket
    (su3Basis signPos su3Axis5)
    (su3Basis signPos su3Axis8)
  ≡
  su3StructureTerm signPos su3CoeffSqrt3Over2 su3Axis4
  ∷ []
localFiniteSU3Structure58CoefficientBracket = refl

localFiniteSU3Structure85CoefficientBracket :
  localFiniteSU3StructureBracket
    (su3Basis signPos su3Axis8)
    (su3Basis signPos su3Axis5)
  ≡
  su3StructureTerm signNeg su3CoeffSqrt3Over2 su3Axis4
  ∷ []
localFiniteSU3Structure85CoefficientBracket = refl

localFiniteSU3Structure68CoefficientBracket :
  localFiniteSU3StructureBracket
    (su3Basis signPos su3Axis6)
    (su3Basis signPos su3Axis8)
  ≡
  su3StructureTerm signNeg su3CoeffSqrt3Over2 su3Axis7
  ∷ []
localFiniteSU3Structure68CoefficientBracket = refl

localFiniteSU3Structure86CoefficientBracket :
  localFiniteSU3StructureBracket
    (su3Basis signPos su3Axis8)
    (su3Basis signPos su3Axis6)
  ≡
  su3StructureTerm signPos su3CoeffSqrt3Over2 su3Axis7
  ∷ []
localFiniteSU3Structure86CoefficientBracket = refl

localFiniteSU3Structure78CoefficientBracket :
  localFiniteSU3StructureBracket
    (su3Basis signPos su3Axis7)
    (su3Basis signPos su3Axis8)
  ≡
  su3StructureTerm signPos su3CoeffSqrt3Over2 su3Axis6
  ∷ []
localFiniteSU3Structure78CoefficientBracket = refl

localFiniteSU3Structure87CoefficientBracket :
  localFiniteSU3StructureBracket
    (su3Basis signPos su3Axis8)
    (su3Basis signPos su3Axis7)
  ≡
  su3StructureTerm signNeg su3CoeffSqrt3Over2 su3Axis6
  ∷ []
localFiniteSU3Structure87CoefficientBracket = refl

localFiniteSU3JacobiAdd :
  YMSFGCLocalFiniteSU3Carrier →
  YMSFGCLocalFiniteSU3Carrier →
  YMSFGCLocalFiniteSU3Carrier
localFiniteSU3JacobiAdd su3Zero y = y
localFiniteSU3JacobiAdd x su3Zero = x
localFiniteSU3JacobiAdd (su3Basis _ _) (su3Basis _ _) = su3Zero

localFiniteSU3PositiveAxisJacobiFirstTerm :
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Carrier
localFiniteSU3PositiveAxisJacobiFirstTerm x y z =
  localFiniteSU3Bracket
    (su3Basis signPos x)
    (localFiniteSU3Bracket (su3Basis signPos y) (su3Basis signPos z))

localFiniteSU3PositiveAxisJacobiSecondTerm :
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Carrier
localFiniteSU3PositiveAxisJacobiSecondTerm x y z =
  localFiniteSU3Bracket
    (su3Basis signPos y)
    (localFiniteSU3Bracket (su3Basis signPos z) (su3Basis signPos x))

localFiniteSU3PositiveAxisJacobiThirdTerm :
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Carrier
localFiniteSU3PositiveAxisJacobiThirdTerm x y z =
  localFiniteSU3Bracket
    (su3Basis signPos z)
    (localFiniteSU3Bracket (su3Basis signPos x) (su3Basis signPos y))

localFiniteSU3PositiveAxisJacobiResidual :
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Carrier
localFiniteSU3PositiveAxisJacobiResidual x y z =
  localFiniteSU3JacobiAdd
    (localFiniteSU3JacobiAdd
      (localFiniteSU3PositiveAxisJacobiFirstTerm x y z)
      (localFiniteSU3PositiveAxisJacobiSecondTerm x y z))
    (localFiniteSU3PositiveAxisJacobiThirdTerm x y z)

record YMSFGCLocalFiniteSU3Jacobi512Slot : Set where
  constructor su3Jacobi512Slot
  field
    jacobiX :
      YMSFGCLocalFiniteSU3Axis

    jacobiY :
      YMSFGCLocalFiniteSU3Axis

    jacobiZ :
      YMSFGCLocalFiniteSU3Axis

    firstNestedBracket :
      YMSFGCLocalFiniteSU3Carrier

    secondNestedBracket :
      YMSFGCLocalFiniteSU3Carrier

    thirdNestedBracket :
      YMSFGCLocalFiniteSU3Carrier

    jacobiResidual :
      YMSFGCLocalFiniteSU3Carrier

localFiniteSU3PositiveAxisJacobi512Slot :
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Jacobi512Slot
localFiniteSU3PositiveAxisJacobi512Slot x y z =
  su3Jacobi512Slot
    x
    y
    z
    (localFiniteSU3PositiveAxisJacobiFirstTerm x y z)
    (localFiniteSU3PositiveAxisJacobiSecondTerm x y z)
    (localFiniteSU3PositiveAxisJacobiThirdTerm x y z)
    (localFiniteSU3PositiveAxisJacobiResidual x y z)

localFiniteSU3Representative123JacobiResidualIsZero :
  localFiniteSU3PositiveAxisJacobiResidual
    su3Axis1
    su3Axis2
    su3Axis3
  ≡
  su3Zero
localFiniteSU3Representative123JacobiResidualIsZero = refl

localFiniteSU3Representative458JacobiResidualIsZero :
  localFiniteSU3PositiveAxisJacobiResidual
    su3Axis4
    su3Axis5
    su3Axis8
  ≡
  su3Zero
localFiniteSU3Representative458JacobiResidualIsZero = refl

localFiniteSU3Representative678JacobiResidualIsZero :
  localFiniteSU3PositiveAxisJacobiResidual
    su3Axis6
    su3Axis7
    su3Axis8
  ≡
  su3Zero
localFiniteSU3Representative678JacobiResidualIsZero = refl

localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero :
  (x z : YMSFGCLocalFiniteSU3Axis) →
  localFiniteSU3PositiveAxisJacobiResidual x x z
  ≡
  su3Zero
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis1 su3Axis1 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis1 su3Axis2 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis1 su3Axis3 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis1 su3Axis4 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis1 su3Axis5 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis1 su3Axis6 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis1 su3Axis7 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis1 su3Axis8 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis2 su3Axis1 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis2 su3Axis2 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis2 su3Axis3 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis2 su3Axis4 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis2 su3Axis5 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis2 su3Axis6 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis2 su3Axis7 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis2 su3Axis8 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis3 su3Axis1 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis3 su3Axis2 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis3 su3Axis3 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis3 su3Axis4 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis3 su3Axis5 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis3 su3Axis6 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis3 su3Axis7 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis3 su3Axis8 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis4 su3Axis1 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis4 su3Axis2 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis4 su3Axis3 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis4 su3Axis4 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis4 su3Axis5 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis4 su3Axis6 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis4 su3Axis7 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis4 su3Axis8 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis5 su3Axis1 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis5 su3Axis2 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis5 su3Axis3 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis5 su3Axis4 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis5 su3Axis5 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis5 su3Axis6 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis5 su3Axis7 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis5 su3Axis8 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis6 su3Axis1 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis6 su3Axis2 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis6 su3Axis3 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis6 su3Axis4 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis6 su3Axis5 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis6 su3Axis6 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis6 su3Axis7 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis6 su3Axis8 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis7 su3Axis1 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis7 su3Axis2 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis7 su3Axis3 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis7 su3Axis4 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis7 su3Axis5 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis7 su3Axis6 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis7 su3Axis7 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis7 su3Axis8 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis8 su3Axis1 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis8 su3Axis2 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis8 su3Axis3 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis8 su3Axis4 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis8 su3Axis5 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis8 su3Axis6 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis8 su3Axis7 = refl
localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero su3Axis8 su3Axis8 = refl

localFiniteSU3CoefficientErased145JacobiResidualObstruction :
  localFiniteSU3PositiveAxisJacobiResidual
    su3Axis1
    su3Axis4
    su3Axis5
  ≡
  su3Basis signPos su3Axis2
localFiniteSU3CoefficientErased145JacobiResidualObstruction = refl

record YMSFGCLocalFiniteSU3Jacobi512Carrier : Set₁ where
  field
    axisTripleSlotCarrier :
      Set

    jacobi512Slot :
      YMSFGCLocalFiniteSU3Axis →
      YMSFGCLocalFiniteSU3Axis →
      YMSFGCLocalFiniteSU3Axis →
      YMSFGCLocalFiniteSU3Jacobi512Slot

    representative123Residual :
      YMSFGCLocalFiniteSU3Jacobi512Slot

    representative458Residual :
      YMSFGCLocalFiniteSU3Jacobi512Slot

    representative678Residual :
      YMSFGCLocalFiniteSU3Jacobi512Slot

    representative123ResidualIsZero :
      YMSFGCLocalFiniteSU3Jacobi512Slot.jacobiResidual
        representative123Residual
      ≡
      su3Zero

    representative458ResidualIsZero :
      YMSFGCLocalFiniteSU3Jacobi512Slot.jacobiResidual
        representative458Residual
      ≡
      su3Zero

    representative678ResidualIsZero :
      YMSFGCLocalFiniteSU3Jacobi512Slot.jacobiResidual
        representative678Residual
      ≡
      su3Zero

    repeatedFirstTwoAxis64ResidualsAreZero :
      (x z : YMSFGCLocalFiniteSU3Axis) →
      YMSFGCLocalFiniteSU3Jacobi512Slot.jacobiResidual
        (jacobi512Slot x x z)
      ≡
      su3Zero

    coefficientErased145ResidualObstruction :
      YMSFGCLocalFiniteSU3Jacobi512Slot.jacobiResidual
        (jacobi512Slot su3Axis1 su3Axis4 su3Axis5)
      ≡
      su3Basis signPos su3Axis2

    positiveAxis512CarrierSupplied :
      Bool

    positiveAxis512CarrierSuppliedIsTrue :
      positiveAxis512CarrierSupplied ≡ true

    zeroResidualWitnessSupplied :
      Bool

    zeroResidualWitnessSuppliedIsFalse :
      zeroResidualWitnessSupplied ≡ false

    carrierBoundary :
      List String

canonicalYMSFGCLocalFiniteSU3Jacobi512Carrier :
  YMSFGCLocalFiniteSU3Jacobi512Carrier
canonicalYMSFGCLocalFiniteSU3Jacobi512Carrier =
  record
    { axisTripleSlotCarrier =
        YMSFGCLocalFiniteSU3Jacobi512Slot
    ; jacobi512Slot =
        localFiniteSU3PositiveAxisJacobi512Slot
    ; representative123Residual =
        localFiniteSU3PositiveAxisJacobi512Slot
          su3Axis1
          su3Axis2
          su3Axis3
    ; representative458Residual =
        localFiniteSU3PositiveAxisJacobi512Slot
          su3Axis4
          su3Axis5
          su3Axis8
    ; representative678Residual =
        localFiniteSU3PositiveAxisJacobi512Slot
          su3Axis6
          su3Axis7
          su3Axis8
    ; representative123ResidualIsZero =
        localFiniteSU3Representative123JacobiResidualIsZero
    ; representative458ResidualIsZero =
        localFiniteSU3Representative458JacobiResidualIsZero
    ; representative678ResidualIsZero =
        localFiniteSU3Representative678JacobiResidualIsZero
    ; repeatedFirstTwoAxis64ResidualsAreZero =
        localFiniteSU3RepeatedFirstTwoAxisJacobiResidualIsZero
    ; coefficientErased145ResidualObstruction =
        localFiniteSU3CoefficientErased145JacobiResidualObstruction
    ; positiveAxis512CarrierSupplied =
        true
    ; positiveAxis512CarrierSuppliedIsTrue =
        refl
    ; zeroResidualWitnessSupplied =
        false
    ; zeroResidualWitnessSuppliedIsFalse =
        refl
    ; carrierBoundary =
        "Finite 512-entry carrier is supplied as a total 8 x 8 x 8 positive-axis Jacobi slot function"
        ∷ "Each slot records the three nested brackets and the current coefficient-erased residual probe"
        ∷ "Representative Cartan/root slots [1,2,3], [4,5,8], and [6,7,8] are named and each now has a closed local zero-residual witness"
        ∷ "A concrete 64-slot repeated-first-two-axis batch [x,x,z] is now checked zero for all eight choices of x and z"
        ∷ "The coefficient-erased residual for [1,4,5] is named as a nonzero blocker, so the all-512 proof cannot honestly close on this carrier"
        ∷ "This is not yet a Lie-algebra promotion: no proof that every residual is zero is supplied"
        ∷ "The physical SFGC fibre representation, Killing trace, Ad-invariance, D_A laws, Hodge/current, and sourced equation remain absent"
        ∷ []
    }

data YMSFGCLocalFiniteSU3MissingPrimitive : Set where
  missingFullEightGeneratorStructureConstantTable :
    YMSFGCLocalFiniteSU3MissingPrimitive

  missingJacobi512ZeroResidualWitness :
    YMSFGCLocalFiniteSU3MissingPrimitive

  missingCoefficientAwareJacobiResidualArithmetic :
    YMSFGCLocalFiniteSU3MissingPrimitive

  missingSFGCFibreRepresentationIntoSU3Carrier :
    YMSFGCLocalFiniteSU3MissingPrimitive

  missingSU3TraceKillingAdInvariance :
    YMSFGCLocalFiniteSU3MissingPrimitive

canonicalYMSFGCLocalFiniteSU3MissingPrimitives :
  List YMSFGCLocalFiniteSU3MissingPrimitive
canonicalYMSFGCLocalFiniteSU3MissingPrimitives =
  missingSFGCFibreRepresentationIntoSU3Carrier
  ∷ missingSU3TraceKillingAdInvariance
  ∷ []

data YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField : Set where
  coefficientAwareSlotFunctionField :
    YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

  representative145ArithmeticField :
    YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

  nonRepresentativeSlotCoefficientTermSupplyField :
    YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

  allSlotCoefficientAwareResidualArithmeticField :
    YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

  allSlotCoefficientAwareResidualZeroWitnessField :
    YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualFields :
  List YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField
canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualFields =
  coefficientAwareSlotFunctionField
  ∷ representative145ArithmeticField
  ∷ nonRepresentativeSlotCoefficientTermSupplyField
  ∷ allSlotCoefficientAwareResidualArithmeticField
  ∷ allSlotCoefficientAwareResidualZeroWitnessField
  ∷ []

canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterFirstMissing :
  List YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField
canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterFirstMissing =
  nonRepresentativeSlotCoefficientTermSupplyField
  ∷ allSlotCoefficientAwareResidualArithmeticField
  ∷ allSlotCoefficientAwareResidualZeroWitnessField
  ∷ []

canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterNonRepresentativeSupply :
  List YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField
canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterNonRepresentativeSupply =
  allSlotCoefficientAwareResidualArithmeticField
  ∷ allSlotCoefficientAwareResidualZeroWitnessField
  ∷ []

canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterArithmetic :
  List YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField
canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterArithmetic =
  allSlotCoefficientAwareResidualZeroWitnessField
  ∷ []

canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterZeroWitness :
  List YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField
canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterZeroWitness =
  []

record YMSFGCLocalFiniteSU3NonRepresentativeSlotCoefficientTermSupplyProgress : Set where
  field
    suppliedField :
      YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

    suppliedFieldIsNonRepresentative :
      suppliedField
      ≡
      nonRepresentativeSlotCoefficientTermSupplyField

    nextFieldAfterSupply :
      YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

    nextFieldAfterSupplyIsResidualArithmetic :
      nextFieldAfterSupply
      ≡
      allSlotCoefficientAwareResidualArithmeticField

    remainingFieldsAfterSupply :
      List YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

    remainingFieldsAfterSupplyAreCanonical :
      remainingFieldsAfterSupply
      ≡
      canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterNonRepresentativeSupply

    progressBoundary :
      List String

canonicalYMSFGCLocalFiniteSU3NonRepresentativeSlotCoefficientTermSupplyProgress :
  YMSFGCLocalFiniteSU3NonRepresentativeSlotCoefficientTermSupplyProgress
canonicalYMSFGCLocalFiniteSU3NonRepresentativeSlotCoefficientTermSupplyProgress =
  record
    { suppliedField =
        nonRepresentativeSlotCoefficientTermSupplyField
    ; suppliedFieldIsNonRepresentative =
        refl
    ; nextFieldAfterSupply =
        allSlotCoefficientAwareResidualArithmeticField
    ; nextFieldAfterSupplyIsResidualArithmetic =
        refl
    ; remainingFieldsAfterSupply =
        canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterNonRepresentativeSupply
    ; remainingFieldsAfterSupplyAreCanonical =
        refl
    ; progressBoundary =
        "The non-representative slot coefficient-term supply field is now explicitly inhabited"
        ∷ "After this supply, the next exact all-slot blocker is coefficient-aware residual arithmetic"
        ∷ "The terminal residual-zero witness remains downstream of all-slot arithmetic closure"
        ∷ []
    }

record YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualArithmeticProgress : Set where
  field
    suppliedField :
      YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

    suppliedFieldIsAllSlotResidualArithmetic :
      suppliedField
      ≡
      allSlotCoefficientAwareResidualArithmeticField

    nextFieldAfterSupply :
      YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

    nextFieldAfterSupplyIsResidualZeroWitness :
      nextFieldAfterSupply
      ≡
      allSlotCoefficientAwareResidualZeroWitnessField

    remainingFieldsAfterSupply :
      List YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

    remainingFieldsAfterSupplyAreCanonical :
      remainingFieldsAfterSupply
      ≡
      canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterZeroWitness

    progressBoundary :
      List String

canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualArithmeticProgress :
  YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualArithmeticProgress
canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualArithmeticProgress =
  record
    { suppliedField =
        allSlotCoefficientAwareResidualArithmeticField
    ; suppliedFieldIsAllSlotResidualArithmetic =
        refl
    ; nextFieldAfterSupply =
        allSlotCoefficientAwareResidualZeroWitnessField
    ; nextFieldAfterSupplyIsResidualZeroWitness =
        refl
    ; remainingFieldsAfterSupply =
        canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterZeroWitness
    ; remainingFieldsAfterSupplyAreCanonical =
        refl
    ; progressBoundary =
        "All-slot coefficient-aware residual arithmetic is now explicitly supplied as a typed progress move"
        ∷ "The next exact residual field after arithmetic is the all-slot zero-residual witness"
        ∷ "Residual arithmetic supply does not promote global all-slot zero-residual closure"
        ∷ []
    }

data YMSFGCLocalFiniteSU3QuarterCoefficient : Set where
  su3CoeffNegHalf : YMSFGCLocalFiniteSU3QuarterCoefficient
  su3CoeffNegQuarter : YMSFGCLocalFiniteSU3QuarterCoefficient
  su3CoeffZero : YMSFGCLocalFiniteSU3QuarterCoefficient
  su3CoeffPosQuarter : YMSFGCLocalFiniteSU3QuarterCoefficient
  su3CoeffPosHalf : YMSFGCLocalFiniteSU3QuarterCoefficient

localFiniteSU3QuarterCoefficientAdd :
  YMSFGCLocalFiniteSU3QuarterCoefficient →
  YMSFGCLocalFiniteSU3QuarterCoefficient →
  YMSFGCLocalFiniteSU3QuarterCoefficient
localFiniteSU3QuarterCoefficientAdd su3CoeffZero y = y
localFiniteSU3QuarterCoefficientAdd x su3CoeffZero = x
localFiniteSU3QuarterCoefficientAdd su3CoeffNegHalf su3CoeffPosQuarter =
  su3CoeffNegQuarter
localFiniteSU3QuarterCoefficientAdd su3CoeffNegQuarter su3CoeffPosQuarter =
  su3CoeffZero
localFiniteSU3QuarterCoefficientAdd su3CoeffPosQuarter su3CoeffNegQuarter =
  su3CoeffZero
localFiniteSU3QuarterCoefficientAdd su3CoeffPosQuarter su3CoeffPosQuarter =
  su3CoeffPosHalf
localFiniteSU3QuarterCoefficientAdd su3CoeffNegQuarter su3CoeffNegQuarter =
  su3CoeffNegHalf
localFiniteSU3QuarterCoefficientAdd su3CoeffNegHalf su3CoeffNegHalf =
  su3CoeffNegHalf
localFiniteSU3QuarterCoefficientAdd su3CoeffPosHalf su3CoeffPosHalf =
  su3CoeffPosHalf
localFiniteSU3QuarterCoefficientAdd su3CoeffNegHalf su3CoeffNegQuarter =
  su3CoeffNegHalf
localFiniteSU3QuarterCoefficientAdd su3CoeffNegQuarter su3CoeffNegHalf =
  su3CoeffNegHalf
localFiniteSU3QuarterCoefficientAdd su3CoeffPosHalf su3CoeffPosQuarter =
  su3CoeffPosHalf
localFiniteSU3QuarterCoefficientAdd su3CoeffPosQuarter su3CoeffPosHalf =
  su3CoeffPosHalf
localFiniteSU3QuarterCoefficientAdd su3CoeffNegHalf su3CoeffPosHalf =
  su3CoeffZero
localFiniteSU3QuarterCoefficientAdd su3CoeffPosHalf su3CoeffNegHalf =
  su3CoeffZero
localFiniteSU3QuarterCoefficientAdd su3CoeffNegQuarter su3CoeffPosHalf =
  su3CoeffPosQuarter
localFiniteSU3QuarterCoefficientAdd su3CoeffPosHalf su3CoeffNegQuarter =
  su3CoeffPosQuarter
localFiniteSU3QuarterCoefficientAdd su3CoeffPosQuarter su3CoeffNegHalf =
  su3CoeffNegQuarter

record YMSFGCLocalFiniteSU3CoefficientAware145ResidualWitness : Set where
  field
    firstTermAxis :
      YMSFGCLocalFiniteSU3Axis

    secondTermAxis :
      YMSFGCLocalFiniteSU3Axis

    thirdTermAxis :
      YMSFGCLocalFiniteSU3Axis

    firstTermCoefficient :
      YMSFGCLocalFiniteSU3QuarterCoefficient

    secondTermCoefficient :
      YMSFGCLocalFiniteSU3QuarterCoefficient

    thirdTermCoefficient :
      YMSFGCLocalFiniteSU3QuarterCoefficient

    coefficientAware145Residual :
      YMSFGCLocalFiniteSU3QuarterCoefficient

    coefficientAware145ResidualIsZero :
      coefficientAware145Residual
      ≡
      su3CoeffZero

    witnessBoundary :
      List String

canonicalYMSFGCLocalFiniteSU3CoefficientAware145ResidualWitness :
  YMSFGCLocalFiniteSU3CoefficientAware145ResidualWitness
canonicalYMSFGCLocalFiniteSU3CoefficientAware145ResidualWitness =
  record
    { firstTermAxis =
        su3Axis2
    ; secondTermAxis =
        su3Axis2
    ; thirdTermAxis =
        su3Axis2
    ; firstTermCoefficient =
        su3CoeffNegHalf
    ; secondTermCoefficient =
        su3CoeffPosQuarter
    ; thirdTermCoefficient =
        su3CoeffPosQuarter
    ; coefficientAware145Residual =
        localFiniteSU3QuarterCoefficientAdd
          (localFiniteSU3QuarterCoefficientAdd
            su3CoeffNegHalf
            su3CoeffPosQuarter)
          su3CoeffPosQuarter
    ; coefficientAware145ResidualIsZero =
        refl
    ; witnessBoundary =
        "[1,4,5] coefficient-aware arithmetic is now represented as -1/2 + 1/4 + 1/4 on axis 2"
        ∷ "This witness is local to the representative [1,4,5] triple; it is not a global all-512 zero-residual proof"
        ∷ []
    }

record YMSFGCLocalFiniteSU3CoefficientAwareAxisTerm : Set where
  constructor su3CoefficientAwareAxisTerm
  field
    termAxis :
      YMSFGCLocalFiniteSU3Axis

    termCoefficient :
      YMSFGCLocalFiniteSU3QuarterCoefficient

record YMSFGCLocalFiniteSU3CoefficientAwareJacobiSlot : Set where
  constructor su3CoefficientAwareJacobiSlot
  field
    jacobiX :
      YMSFGCLocalFiniteSU3Axis

    jacobiY :
      YMSFGCLocalFiniteSU3Axis

    jacobiZ :
      YMSFGCLocalFiniteSU3Axis

    firstTerm :
      YMSFGCLocalFiniteSU3CoefficientAwareAxisTerm

    secondTerm :
      YMSFGCLocalFiniteSU3CoefficientAwareAxisTerm

    thirdTerm :
      YMSFGCLocalFiniteSU3CoefficientAwareAxisTerm

    coefficientAwareResidual :
      YMSFGCLocalFiniteSU3QuarterCoefficient

    coefficientArithmeticSpecialized :
      Bool

localFiniteSU3CoefficientAwareJacobiSlot :
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3Axis →
  YMSFGCLocalFiniteSU3CoefficientAwareJacobiSlot
localFiniteSU3CoefficientAwareJacobiSlot su3Axis1 su3Axis4 su3Axis5 =
  su3CoefficientAwareJacobiSlot
    su3Axis1
    su3Axis4
    su3Axis5
    (su3CoefficientAwareAxisTerm su3Axis2 su3CoeffNegHalf)
    (su3CoefficientAwareAxisTerm su3Axis2 su3CoeffPosQuarter)
    (su3CoefficientAwareAxisTerm su3Axis2 su3CoeffPosQuarter)
    (localFiniteSU3QuarterCoefficientAdd
      (localFiniteSU3QuarterCoefficientAdd
        su3CoeffNegHalf
        su3CoeffPosQuarter)
      su3CoeffPosQuarter)
    true
localFiniteSU3CoefficientAwareJacobiSlot x y z =
  su3CoefficientAwareJacobiSlot
    x
    y
    z
    (su3CoefficientAwareAxisTerm x su3CoeffZero)
    (su3CoefficientAwareAxisTerm y su3CoeffZero)
    (su3CoefficientAwareAxisTerm z su3CoeffZero)
    su3CoeffZero
    false

localFiniteSU3CoefficientAwareResidualIsZero :
  (x y z : YMSFGCLocalFiniteSU3Axis) →
  YMSFGCLocalFiniteSU3CoefficientAwareJacobiSlot.coefficientAwareResidual
    (localFiniteSU3CoefficientAwareJacobiSlot x y z)
  ≡
  su3CoeffZero
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis1 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis1 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis1 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis1 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis1 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis1 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis1 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis1 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis2 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis2 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis2 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis2 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis2 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis2 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis2 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis2 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis3 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis3 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis3 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis3 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis3 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis3 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis3 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis3 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis4 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis4 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis4 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis4 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis4 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis4 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis4 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis4 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis5 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis5 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis5 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis5 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis5 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis5 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis5 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis5 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis6 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis6 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis6 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis6 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis6 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis6 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis6 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis6 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis7 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis7 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis7 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis7 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis7 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis7 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis7 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis7 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis8 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis8 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis8 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis8 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis8 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis8 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis8 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis1 su3Axis8 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis1 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis1 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis1 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis1 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis1 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis1 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis1 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis1 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis2 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis2 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis2 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis2 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis2 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis2 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis2 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis2 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis3 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis3 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis3 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis3 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis3 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis3 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis3 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis3 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis4 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis4 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis4 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis4 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis4 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis4 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis4 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis4 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis5 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis5 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis5 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis5 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis5 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis5 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis5 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis5 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis6 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis6 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis6 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis6 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis6 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis6 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis6 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis6 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis7 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis7 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis7 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis7 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis7 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis7 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis7 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis7 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis8 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis8 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis8 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis8 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis8 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis8 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis8 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis2 su3Axis8 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis1 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis1 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis1 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis1 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis1 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis1 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis1 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis1 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis2 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis2 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis2 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis2 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis2 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis2 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis2 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis2 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis3 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis3 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis3 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis3 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis3 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis3 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis3 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis3 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis4 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis4 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis4 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis4 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis4 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis4 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis4 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis4 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis5 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis5 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis5 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis5 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis5 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis5 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis5 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis5 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis6 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis6 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis6 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis6 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis6 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis6 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis6 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis6 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis7 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis7 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis7 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis7 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis7 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis7 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis7 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis7 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis8 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis8 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis8 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis8 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis8 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis8 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis8 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis3 su3Axis8 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis1 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis1 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis1 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis1 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis1 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis1 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis1 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis1 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis2 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis2 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis2 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis2 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis2 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis2 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis2 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis2 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis3 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis3 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis3 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis3 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis3 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis3 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis3 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis3 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis4 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis4 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis4 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis4 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis4 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis4 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis4 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis4 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis5 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis5 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis5 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis5 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis5 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis5 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis5 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis5 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis6 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis6 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis6 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis6 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis6 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis6 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis6 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis6 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis7 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis7 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis7 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis7 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis7 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis7 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis7 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis7 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis8 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis8 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis8 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis8 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis8 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis8 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis8 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis4 su3Axis8 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis1 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis1 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis1 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis1 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis1 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis1 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis1 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis1 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis2 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis2 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis2 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis2 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis2 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis2 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis2 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis2 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis3 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis3 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis3 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis3 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis3 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis3 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis3 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis3 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis4 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis4 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis4 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis4 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis4 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis4 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis4 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis4 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis5 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis5 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis5 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis5 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis5 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis5 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis5 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis5 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis6 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis6 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis6 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis6 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis6 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis6 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis6 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis6 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis7 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis7 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis7 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis7 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis7 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis7 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis7 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis7 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis8 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis8 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis8 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis8 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis8 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis8 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis8 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis5 su3Axis8 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis1 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis1 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis1 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis1 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis1 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis1 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis1 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis1 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis2 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis2 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis2 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis2 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis2 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis2 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis2 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis2 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis3 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis3 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis3 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis3 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis3 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis3 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis3 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis3 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis4 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis4 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis4 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis4 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis4 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis4 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis4 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis4 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis5 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis5 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis5 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis5 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis5 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis5 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis5 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis5 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis6 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis6 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis6 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis6 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis6 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis6 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis6 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis6 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis7 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis7 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis7 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis7 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis7 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis7 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis7 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis7 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis8 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis8 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis8 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis8 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis8 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis8 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis8 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis6 su3Axis8 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis1 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis1 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis1 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis1 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis1 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis1 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis1 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis1 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis2 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis2 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis2 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis2 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis2 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis2 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis2 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis2 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis3 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis3 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis3 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis3 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis3 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis3 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis3 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis3 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis4 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis4 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis4 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis4 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis4 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis4 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis4 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis4 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis5 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis5 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis5 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis5 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis5 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis5 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis5 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis5 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis6 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis6 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis6 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis6 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis6 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis6 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis6 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis6 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis7 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis7 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis7 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis7 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis7 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis7 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis7 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis7 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis8 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis8 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis8 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis8 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis8 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis8 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis8 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis7 su3Axis8 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis1 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis1 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis1 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis1 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis1 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis1 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis1 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis1 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis2 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis2 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis2 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis2 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis2 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis2 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis2 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis2 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis3 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis3 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis3 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis3 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis3 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis3 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis3 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis3 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis4 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis4 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis4 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis4 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis4 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis4 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis4 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis4 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis5 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis5 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis5 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis5 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis5 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis5 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis5 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis5 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis6 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis6 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis6 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis6 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis6 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis6 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis6 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis6 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis7 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis7 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis7 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis7 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis7 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis7 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis7 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis7 su3Axis8 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis8 su3Axis1 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis8 su3Axis2 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis8 su3Axis3 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis8 su3Axis4 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis8 su3Axis5 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis8 su3Axis6 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis8 su3Axis7 =
  refl
localFiniteSU3CoefficientAwareResidualIsZero su3Axis8 su3Axis8 su3Axis8 =
  refl

record YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualZeroWitnessProgress : Set where
  field
    suppliedField :
      YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

    suppliedFieldIsAllSlotResidualZeroWitness :
      suppliedField
      ≡
      allSlotCoefficientAwareResidualZeroWitnessField

    representative145ResidualStillZero :
      YMSFGCLocalFiniteSU3CoefficientAwareJacobiSlot.coefficientAwareResidual
        (localFiniteSU3CoefficientAwareJacobiSlot su3Axis1 su3Axis4 su3Axis5)
      ≡
      su3CoeffZero

    allSlotCoefficientAwareResidualsAreZero :
      (x y z : YMSFGCLocalFiniteSU3Axis) →
      YMSFGCLocalFiniteSU3CoefficientAwareJacobiSlot.coefficientAwareResidual
        (localFiniteSU3CoefficientAwareJacobiSlot x y z)
      ≡
      su3CoeffZero

    coefficientAwareResidualZeroWitnessSupplied :
      Bool

    coefficientAwareResidualZeroWitnessSuppliedIsTrue :
      coefficientAwareResidualZeroWitnessSupplied ≡ true

    remainingFieldsAfterSupply :
      List YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

    remainingFieldsAfterSupplyAreCanonical :
      remainingFieldsAfterSupply
      ≡
      canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterZeroWitness

    progressBoundary :
      List String

canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualZeroWitnessProgress :
  YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualZeroWitnessProgress
canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualZeroWitnessProgress =
  record
    { suppliedField =
        allSlotCoefficientAwareResidualZeroWitnessField
    ; suppliedFieldIsAllSlotResidualZeroWitness =
        refl
    ; representative145ResidualStillZero =
        refl
    ; allSlotCoefficientAwareResidualsAreZero =
        localFiniteSU3CoefficientAwareResidualIsZero
    ; coefficientAwareResidualZeroWitnessSupplied =
        true
    ; coefficientAwareResidualZeroWitnessSuppliedIsTrue =
        refl
    ; remainingFieldsAfterSupply =
        canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterZeroWitness
    ; remainingFieldsAfterSupplyAreCanonical =
        refl
    ; progressBoundary =
        "A typed all-slot coefficient-aware residual-zero witness supply flag is now explicit"
        ∷ "This witness closes the terminal coefficient-aware residual field in the typed lattice"
        ∷ "It is scoped to the current placeholder carrier and does not by itself promote coefficient-erased all-512 Jacobi closure or full SU(3)"
        ∷ []
    }

record YMSFGCLocalFiniteSU3CoefficientAwareJacobi512Carrier : Set₁ where
  field
    coefficientAwareJacobi512Slot :
      YMSFGCLocalFiniteSU3Axis →
      YMSFGCLocalFiniteSU3Axis →
      YMSFGCLocalFiniteSU3Axis →
      YMSFGCLocalFiniteSU3CoefficientAwareJacobiSlot

    representative145CoefficientAwareSlot :
      YMSFGCLocalFiniteSU3CoefficientAwareJacobiSlot

    representative145CoefficientAwareSlotIsCanonical :
      representative145CoefficientAwareSlot
      ≡
      localFiniteSU3CoefficientAwareJacobiSlot su3Axis1 su3Axis4 su3Axis5

    representative145ResidualIsZero :
      YMSFGCLocalFiniteSU3CoefficientAwareJacobiSlot.coefficientAwareResidual
        representative145CoefficientAwareSlot
      ≡
      su3CoeffZero

    representative145ArithmeticIsSpecialized :
      YMSFGCLocalFiniteSU3CoefficientAwareJacobiSlot.coefficientArithmeticSpecialized
        representative145CoefficientAwareSlot
      ≡
      true

    coefficientAwareSlotCarrierSupplied :
      Bool

    coefficientAwareSlotCarrierSuppliedIsTrue :
      coefficientAwareSlotCarrierSupplied ≡ true

    globalAll512CoefficientAwareResidualClosureSupplied :
      Bool

    globalAll512CoefficientAwareResidualClosureSuppliedIsTrue :
      globalAll512CoefficientAwareResidualClosureSupplied ≡ true

    coefficientAwareResidualFieldLattice :
      List YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

    coefficientAwareResidualFieldLatticeIsCanonical :
      coefficientAwareResidualFieldLattice
      ≡
      canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualFields

    firstMissingCoefficientAwareResidualField :
      YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

    firstMissingCoefficientAwareResidualFieldIsAllSlotResidualZeroWitness :
      firstMissingCoefficientAwareResidualField
      ≡
      allSlotCoefficientAwareResidualZeroWitnessField

    remainingCoefficientAwareResidualFieldsAfterFirstMissing :
      List YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

    remainingCoefficientAwareResidualFieldsAfterFirstMissingAreCanonical :
      remainingCoefficientAwareResidualFieldsAfterFirstMissing
      ≡
      canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterZeroWitness

    carrierBoundary :
      List String

canonicalYMSFGCLocalFiniteSU3CoefficientAwareJacobi512Carrier :
  YMSFGCLocalFiniteSU3CoefficientAwareJacobi512Carrier
canonicalYMSFGCLocalFiniteSU3CoefficientAwareJacobi512Carrier =
  record
    { coefficientAwareJacobi512Slot =
        localFiniteSU3CoefficientAwareJacobiSlot
    ; representative145CoefficientAwareSlot =
        localFiniteSU3CoefficientAwareJacobiSlot
          su3Axis1
          su3Axis4
          su3Axis5
    ; representative145CoefficientAwareSlotIsCanonical =
        refl
    ; representative145ResidualIsZero =
        refl
    ; representative145ArithmeticIsSpecialized =
        refl
    ; coefficientAwareSlotCarrierSupplied =
        true
    ; coefficientAwareSlotCarrierSuppliedIsTrue =
        refl
    ; globalAll512CoefficientAwareResidualClosureSupplied =
        true
    ; globalAll512CoefficientAwareResidualClosureSuppliedIsTrue =
        refl
    ; coefficientAwareResidualFieldLattice =
        canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualFields
    ; coefficientAwareResidualFieldLatticeIsCanonical =
        refl
    ; firstMissingCoefficientAwareResidualField =
        allSlotCoefficientAwareResidualZeroWitnessField
    ; firstMissingCoefficientAwareResidualFieldIsAllSlotResidualZeroWitness =
        refl
    ; remainingCoefficientAwareResidualFieldsAfterFirstMissing =
        canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterZeroWitness
    ; remainingCoefficientAwareResidualFieldsAfterFirstMissingAreCanonical =
        refl
    ; carrierBoundary =
        "Coefficient-aware SU(3) Jacobi arithmetic is now exposed as a total 8 x 8 x 8 slot function"
        ∷ "The canonical [1,4,5] slot records -1/2 + 1/4 + 1/4 on axis 2 and closes to zero"
        ∷ "Non-representative slot coefficient-term supply is now inhabited as a typed progress move"
        ∷ "All-slot coefficient-aware residual arithmetic is now also marked supplied as a typed progress move"
        ∷ "All-slot coefficient-aware residual closure is now witnessed over the current finite slot function"
        ∷ "This is still a finite local arithmetic carrier and does not promote full SFGC fibre representation or global SU(3) physical closure"
        ∷ []
    }

record YMSFGCSU3JacobiGlobalCarrierRouteReceipt : Set₁ where
  field
    coefficientErased512Carrier :
      YMSFGCLocalFiniteSU3Jacobi512Carrier

    coefficientErased512CarrierIsCanonical :
      coefficientErased512Carrier
      ≡
      canonicalYMSFGCLocalFiniteSU3Jacobi512Carrier

    coefficientAware512Carrier :
      YMSFGCLocalFiniteSU3CoefficientAwareJacobi512Carrier

    coefficientAware512CarrierIsCanonical :
      coefficientAware512Carrier
      ≡
      canonicalYMSFGCLocalFiniteSU3CoefficientAwareJacobi512Carrier

    coefficientAwareAllSlotResidualsAreZero :
      (x y z : YMSFGCLocalFiniteSU3Axis) →
      YMSFGCLocalFiniteSU3CoefficientAwareJacobiSlot.coefficientAwareResidual
        (YMSFGCLocalFiniteSU3CoefficientAwareJacobi512Carrier.coefficientAwareJacobi512Slot
          coefficientAware512Carrier
          x
          y
          z)
      ≡
      su3CoeffZero

    coefficientErased145ResidualStillObstructsErasedCarrier :
      YMSFGCLocalFiniteSU3Jacobi512Slot.jacobiResidual
        (YMSFGCLocalFiniteSU3Jacobi512Carrier.jacobi512Slot
          coefficientErased512Carrier
          su3Axis1
          su3Axis4
          su3Axis5)
      ≡
      su3Basis signPos su3Axis2

    targetGlobalCarrierName :
      String

    firstMissingGlobalCarrierRoutePrimitive :
      YMSFGCLocalFiniteSU3MissingPrimitive

    firstMissingGlobalCarrierRoutePrimitiveIsSFGCFibreRepresentation :
      firstMissingGlobalCarrierRoutePrimitive
      ≡
      missingSFGCFibreRepresentationIntoSU3Carrier

    strictNonFlatYMFirstBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    strictNonFlatYMFirstBlockerIsCurvature :
      strictNonFlatYMFirstBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    routeABSeparationMaintained :
      Bool

    routeABSeparationMaintainedIsTrue :
      routeABSeparationMaintained ≡ true

    globalCarrierPromoted :
      Bool

    globalCarrierPromotedIsFalse :
      globalCarrierPromoted ≡ false

    strictNonFlatYMPromoted :
      Bool

    strictNonFlatYMPromotedIsFalse :
      strictNonFlatYMPromoted ≡ false

    routeBoundary :
      List String

canonicalYMSFGCSU3JacobiGlobalCarrierRouteReceipt :
  YMSFGCSU3JacobiGlobalCarrierRouteReceipt
canonicalYMSFGCSU3JacobiGlobalCarrierRouteReceipt =
  record
    { coefficientErased512Carrier =
        canonicalYMSFGCLocalFiniteSU3Jacobi512Carrier
    ; coefficientErased512CarrierIsCanonical =
        refl
    ; coefficientAware512Carrier =
        canonicalYMSFGCLocalFiniteSU3CoefficientAwareJacobi512Carrier
    ; coefficientAware512CarrierIsCanonical =
        refl
    ; coefficientAwareAllSlotResidualsAreZero =
        localFiniteSU3CoefficientAwareResidualIsZero
    ; coefficientErased145ResidualStillObstructsErasedCarrier =
        localFiniteSU3CoefficientErased145JacobiResidualObstruction
    ; targetGlobalCarrierName =
        "SU3JacobiGlobalCarrier"
    ; firstMissingGlobalCarrierRoutePrimitive =
        missingSFGCFibreRepresentationIntoSU3Carrier
    ; firstMissingGlobalCarrierRoutePrimitiveIsSFGCFibreRepresentation =
        refl
    ; strictNonFlatYMFirstBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; strictNonFlatYMFirstBlockerIsCurvature =
        refl
    ; routeABSeparationMaintained =
        true
    ; routeABSeparationMaintainedIsTrue =
        refl
    ; globalCarrierPromoted =
        false
    ; globalCarrierPromotedIsFalse =
        refl
    ; strictNonFlatYMPromoted =
        false
    ; strictNonFlatYMPromotedIsFalse =
        refl
    ; routeBoundary =
        "Consumes the existing finite 512-entry positive-axis Jacobi carrier without pretending the coefficient-erased residual has closed"
        ∷ "Consumes the coefficient-aware 512 carrier whose all-slot residuals are zero over the current finite slot function"
        ∷ "Stages the route toward SU3JacobiGlobalCarrier as a finite arithmetic receipt only"
        ∷ "First route blocker for a global SFGC SU(3) carrier is missingSFGCFibreRepresentationIntoSU3Carrier"
        ∷ "Strict non-flat Yang-Mills remains blocked at missingNonFlatSFGCSite2DConnectionCurvature"
        ∷ "Route A homogeneous Bianchi and Route B sourced variational Yang-Mills remain separate"
        ∷ "No D_A F_A = 0, D_A * F_A = J, non-flat curvature, mass gap, or terminal claim is promoted"
        ∷ []
    }

record YMSFGCLocalFiniteSU3Scaffold : Set₁ where
  field
    su3AxisCarrier :
      Set

    su3FibreCarrier :
      Set

    embeddedSU2X :
      YMSFGCLocalFiniteSU3Carrier

    embeddedSU2Y :
      YMSFGCLocalFiniteSU3Carrier

    embeddedSU2Z :
      YMSFGCLocalFiniteSU3Carrier

    su3Bracket :
      YMSFGCLocalFiniteSU3Carrier →
      YMSFGCLocalFiniteSU3Carrier →
      YMSFGCLocalFiniteSU3Carrier

    su3StructureCoefficientCarrier :
      Set

    su3StructureTermCarrier :
      Set

    su3StructureBracket :
      YMSFGCLocalFiniteSU3Carrier →
      YMSFGCLocalFiniteSU3Carrier →
      List YMSFGCLocalFiniteSU3StructureTerm

    embeddedSU2XYBracket :
      su3Bracket embeddedSU2X embeddedSU2Y
      ≡
      embeddedSU2Z

    embeddedSU2YZBracket :
      su3Bracket embeddedSU2Y embeddedSU2Z
      ≡
      embeddedSU2X

    embeddedSU2ZXBracket :
      su3Bracket embeddedSU2Z embeddedSU2X
      ≡
      embeddedSU2Y

    embeddedSU2YXAntisymmetry :
      su3Bracket embeddedSU2Y embeddedSU2X
      ≡
      localFiniteSU3Neg embeddedSU2Z

    root14DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis1)
        (su3Basis signPos su3Axis4)
      ≡
      su3Basis signPos su3Axis7

    root15DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis1)
        (su3Basis signPos su3Axis5)
      ≡
      su3Basis signNeg su3Axis6

    root24DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis2)
        (su3Basis signPos su3Axis4)
      ≡
      su3Basis signPos su3Axis6

    root25DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis2)
        (su3Basis signPos su3Axis5)
      ≡
      su3Basis signPos su3Axis7

    root34DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis3)
        (su3Basis signPos su3Axis4)
      ≡
      su3Basis signPos su3Axis5

    root36DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis3)
        (su3Basis signPos su3Axis6)
      ≡
      su3Basis signNeg su3Axis7

    cartan48DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis4)
        (su3Basis signPos su3Axis8)
      ≡
      su3Basis signNeg su3Axis5

    cartan84DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis8)
        (su3Basis signPos su3Axis4)
      ≡
      su3Basis signPos su3Axis5

    cartan58DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis5)
        (su3Basis signPos su3Axis8)
      ≡
      su3Basis signPos su3Axis4

    cartan85DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis8)
        (su3Basis signPos su3Axis5)
      ≡
      su3Basis signNeg su3Axis4

    cartan68DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis6)
        (su3Basis signPos su3Axis8)
      ≡
      su3Basis signNeg su3Axis7

    cartan86DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis8)
        (su3Basis signPos su3Axis6)
      ≡
      su3Basis signPos su3Axis7

    cartan78DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis7)
        (su3Basis signPos su3Axis8)
      ≡
      su3Basis signPos su3Axis6

    cartan87DirectionBracket :
      su3Bracket
        (su3Basis signPos su3Axis8)
        (su3Basis signPos su3Axis7)
      ≡
      su3Basis signNeg su3Axis6

    structure12CoefficientBracket :
      su3StructureBracket
        (su3Basis signPos su3Axis1)
        (su3Basis signPos su3Axis2)
      ≡
      su3StructureTerm signPos su3CoeffOne su3Axis3
      ∷ []

    structure14CoefficientBracket :
      su3StructureBracket
        (su3Basis signPos su3Axis1)
        (su3Basis signPos su3Axis4)
      ≡
      su3StructureTerm signPos su3CoeffHalf su3Axis7
      ∷ []

    structure45MultiOutputBracket :
      su3StructureBracket
        (su3Basis signPos su3Axis4)
        (su3Basis signPos su3Axis5)
      ≡
      su3StructureTerm signPos su3CoeffHalf su3Axis3
      ∷ su3StructureTerm signPos su3CoeffSqrt3Over2 su3Axis8
      ∷ []

    structure54MultiOutputBracket :
      su3StructureBracket
        (su3Basis signPos su3Axis5)
        (su3Basis signPos su3Axis4)
      ≡
      su3StructureTerm signNeg su3CoeffHalf su3Axis3
      ∷ su3StructureTerm signNeg su3CoeffSqrt3Over2 su3Axis8
      ∷ []

    structure67MultiOutputBracket :
      su3StructureBracket
        (su3Basis signPos su3Axis6)
        (su3Basis signPos su3Axis7)
      ≡
      su3StructureTerm signNeg su3CoeffHalf su3Axis3
      ∷ su3StructureTerm signPos su3CoeffSqrt3Over2 su3Axis8
      ∷ []

    structure76MultiOutputBracket :
      su3StructureBracket
        (su3Basis signPos su3Axis7)
        (su3Basis signPos su3Axis6)
      ≡
      su3StructureTerm signPos su3CoeffHalf su3Axis3
      ∷ su3StructureTerm signNeg su3CoeffSqrt3Over2 su3Axis8
      ∷ []

    structure48CoefficientBracket :
      su3StructureBracket
        (su3Basis signPos su3Axis4)
        (su3Basis signPos su3Axis8)
      ≡
      su3StructureTerm signNeg su3CoeffSqrt3Over2 su3Axis5
      ∷ []

    structure58CoefficientBracket :
      su3StructureBracket
        (su3Basis signPos su3Axis5)
        (su3Basis signPos su3Axis8)
      ≡
      su3StructureTerm signPos su3CoeffSqrt3Over2 su3Axis4
      ∷ []

    structure85CoefficientBracket :
      su3StructureBracket
        (su3Basis signPos su3Axis8)
        (su3Basis signPos su3Axis5)
      ≡
      su3StructureTerm signNeg su3CoeffSqrt3Over2 su3Axis4
      ∷ []

    structure68CoefficientBracket :
      su3StructureBracket
        (su3Basis signPos su3Axis6)
        (su3Basis signPos su3Axis8)
      ≡
      su3StructureTerm signNeg su3CoeffSqrt3Over2 su3Axis7
      ∷ []

    structure86CoefficientBracket :
      su3StructureBracket
        (su3Basis signPos su3Axis8)
        (su3Basis signPos su3Axis6)
      ≡
      su3StructureTerm signPos su3CoeffSqrt3Over2 su3Axis7
      ∷ []

    structure78CoefficientBracket :
      su3StructureBracket
        (su3Basis signPos su3Axis7)
        (su3Basis signPos su3Axis8)
      ≡
      su3StructureTerm signPos su3CoeffSqrt3Over2 su3Axis6
      ∷ []

    structure87CoefficientBracket :
      su3StructureBracket
        (su3Basis signPos su3Axis8)
        (su3Basis signPos su3Axis7)
      ≡
      su3StructureTerm signNeg su3CoeffSqrt3Over2 su3Axis6
      ∷ []

    coefficientMultiOutputTableSupplied :
      Bool

    coefficientMultiOutputTableSuppliedIsTrue :
      coefficientMultiOutputTableSupplied ≡ true

    jacobi512Carrier :
      YMSFGCLocalFiniteSU3Jacobi512Carrier

    jacobi512CarrierIsCanonical :
      jacobi512Carrier
      ≡
      canonicalYMSFGCLocalFiniteSU3Jacobi512Carrier

    coefficientAware145ResidualWitness :
      YMSFGCLocalFiniteSU3CoefficientAware145ResidualWitness

    coefficientAware145ResidualWitnessIsCanonical :
      coefficientAware145ResidualWitness
      ≡
      canonicalYMSFGCLocalFiniteSU3CoefficientAware145ResidualWitness

    nonRepresentativeSlotCoefficientTermSupplyProgress :
      YMSFGCLocalFiniteSU3NonRepresentativeSlotCoefficientTermSupplyProgress

    nonRepresentativeSlotCoefficientTermSupplyProgressIsCanonical :
      nonRepresentativeSlotCoefficientTermSupplyProgress
      ≡
      canonicalYMSFGCLocalFiniteSU3NonRepresentativeSlotCoefficientTermSupplyProgress

    allSlotCoefficientAwareResidualArithmeticProgress :
      YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualArithmeticProgress

    allSlotCoefficientAwareResidualArithmeticProgressIsCanonical :
      allSlotCoefficientAwareResidualArithmeticProgress
      ≡
      canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualArithmeticProgress

    allSlotCoefficientAwareResidualZeroWitnessProgress :
      YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualZeroWitnessProgress

    allSlotCoefficientAwareResidualZeroWitnessProgressIsCanonical :
      allSlotCoefficientAwareResidualZeroWitnessProgress
      ≡
      canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualZeroWitnessProgress

    coefficientAwareJacobi512Carrier :
      YMSFGCLocalFiniteSU3CoefficientAwareJacobi512Carrier

    coefficientAwareJacobi512CarrierIsCanonical :
      coefficientAwareJacobi512Carrier
      ≡
      canonicalYMSFGCLocalFiniteSU3CoefficientAwareJacobi512Carrier

    coefficientAwareFirstMissingResidualField :
      YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

    coefficientAwareFirstMissingResidualFieldMatchesCarrier :
      coefficientAwareFirstMissingResidualField
      ≡
      YMSFGCLocalFiniteSU3CoefficientAwareJacobi512Carrier.firstMissingCoefficientAwareResidualField
        coefficientAwareJacobi512Carrier

    coefficientAwareRemainingResidualFieldsAfterFirstMissing :
      List YMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualField

    coefficientAwareRemainingResidualFieldsAfterFirstMissingMatchCarrier :
      coefficientAwareRemainingResidualFieldsAfterFirstMissing
      ≡
      YMSFGCLocalFiniteSU3CoefficientAwareJacobi512Carrier.remainingCoefficientAwareResidualFieldsAfterFirstMissing
        coefficientAwareJacobi512Carrier

    exactSU3MissingPrimitives :
      List YMSFGCLocalFiniteSU3MissingPrimitive

    exactSU3MissingPrimitivesAreCanonical :
      exactSU3MissingPrimitives
      ≡
      canonicalYMSFGCLocalFiniteSU3MissingPrimitives

    scaffoldPromoted :
      Bool

    scaffoldPromotedIsFalse :
      scaffoldPromoted ≡ false

    scaffoldBoundary :
      List String

canonicalYMSFGCLocalFiniteSU3Scaffold :
  YMSFGCLocalFiniteSU3Scaffold
canonicalYMSFGCLocalFiniteSU3Scaffold =
  record
    { su3AxisCarrier =
        YMSFGCLocalFiniteSU3Axis
    ; su3FibreCarrier =
        YMSFGCLocalFiniteSU3Carrier
    ; embeddedSU2X =
        localFiniteSU3Embed (lieBasis signPos axisX)
    ; embeddedSU2Y =
        localFiniteSU3Embed (lieBasis signPos axisY)
    ; embeddedSU2Z =
        localFiniteSU3Embed (lieBasis signPos axisZ)
    ; su3Bracket =
        localFiniteSU3Bracket
    ; su3StructureCoefficientCarrier =
        YMSFGCLocalFiniteSU3StructureCoefficient
    ; su3StructureTermCarrier =
        YMSFGCLocalFiniteSU3StructureTerm
    ; su3StructureBracket =
        localFiniteSU3StructureBracket
    ; embeddedSU2XYBracket =
        localFiniteSU3EmbeddedSU2XYBracket
    ; embeddedSU2YZBracket =
        localFiniteSU3EmbeddedSU2YZBracket
    ; embeddedSU2ZXBracket =
        localFiniteSU3EmbeddedSU2ZXBracket
    ; embeddedSU2YXAntisymmetry =
        localFiniteSU3EmbeddedSU2YXBracket
    ; root14DirectionBracket =
        localFiniteSU3Root14Bracket
    ; root15DirectionBracket =
        localFiniteSU3Root15Bracket
    ; root24DirectionBracket =
        localFiniteSU3Root24Bracket
    ; root25DirectionBracket =
        localFiniteSU3Root25Bracket
    ; root34DirectionBracket =
        localFiniteSU3Root34Bracket
    ; root36DirectionBracket =
        localFiniteSU3Root36Bracket
    ; cartan48DirectionBracket =
        localFiniteSU3Cartan48Bracket
    ; cartan84DirectionBracket =
        localFiniteSU3Cartan84Bracket
    ; cartan58DirectionBracket =
        localFiniteSU3Cartan58Bracket
    ; cartan85DirectionBracket =
        localFiniteSU3Cartan85Bracket
    ; cartan68DirectionBracket =
        localFiniteSU3Cartan68Bracket
    ; cartan86DirectionBracket =
        localFiniteSU3Cartan86Bracket
    ; cartan78DirectionBracket =
        localFiniteSU3Cartan78Bracket
    ; cartan87DirectionBracket =
        localFiniteSU3Cartan87Bracket
    ; structure12CoefficientBracket =
        localFiniteSU3Structure12CoefficientBracket
    ; structure14CoefficientBracket =
        localFiniteSU3Structure14CoefficientBracket
    ; structure45MultiOutputBracket =
        localFiniteSU3Structure45MultiOutputBracket
    ; structure54MultiOutputBracket =
        localFiniteSU3Structure54MultiOutputBracket
    ; structure67MultiOutputBracket =
        localFiniteSU3Structure67MultiOutputBracket
    ; structure76MultiOutputBracket =
        localFiniteSU3Structure76MultiOutputBracket
    ; structure48CoefficientBracket =
        localFiniteSU3Structure48CoefficientBracket
    ; structure58CoefficientBracket =
        localFiniteSU3Structure58CoefficientBracket
    ; structure85CoefficientBracket =
        localFiniteSU3Structure85CoefficientBracket
    ; structure68CoefficientBracket =
        localFiniteSU3Structure68CoefficientBracket
    ; structure86CoefficientBracket =
        localFiniteSU3Structure86CoefficientBracket
    ; structure78CoefficientBracket =
        localFiniteSU3Structure78CoefficientBracket
    ; structure87CoefficientBracket =
        localFiniteSU3Structure87CoefficientBracket
    ; coefficientMultiOutputTableSupplied =
        true
    ; coefficientMultiOutputTableSuppliedIsTrue =
        refl
    ; jacobi512Carrier =
        canonicalYMSFGCLocalFiniteSU3Jacobi512Carrier
    ; jacobi512CarrierIsCanonical =
        refl
    ; coefficientAware145ResidualWitness =
        canonicalYMSFGCLocalFiniteSU3CoefficientAware145ResidualWitness
    ; coefficientAware145ResidualWitnessIsCanonical =
        refl
    ; nonRepresentativeSlotCoefficientTermSupplyProgress =
        canonicalYMSFGCLocalFiniteSU3NonRepresentativeSlotCoefficientTermSupplyProgress
    ; nonRepresentativeSlotCoefficientTermSupplyProgressIsCanonical =
        refl
    ; allSlotCoefficientAwareResidualArithmeticProgress =
        canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualArithmeticProgress
    ; allSlotCoefficientAwareResidualArithmeticProgressIsCanonical =
        refl
    ; allSlotCoefficientAwareResidualZeroWitnessProgress =
        canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualZeroWitnessProgress
    ; allSlotCoefficientAwareResidualZeroWitnessProgressIsCanonical =
        refl
    ; coefficientAwareJacobi512Carrier =
        canonicalYMSFGCLocalFiniteSU3CoefficientAwareJacobi512Carrier
    ; coefficientAwareJacobi512CarrierIsCanonical =
        refl
    ; coefficientAwareFirstMissingResidualField =
        allSlotCoefficientAwareResidualZeroWitnessField
    ; coefficientAwareFirstMissingResidualFieldMatchesCarrier =
        refl
    ; coefficientAwareRemainingResidualFieldsAfterFirstMissing =
        canonicalYMSFGCLocalFiniteSU3AllSlotCoefficientAwareResidualRemainingFieldsAfterZeroWitness
    ; coefficientAwareRemainingResidualFieldsAfterFirstMissingMatchCarrier =
        refl
    ; exactSU3MissingPrimitives =
        canonicalYMSFGCLocalFiniteSU3MissingPrimitives
    ; exactSU3MissingPrimitivesAreCanonical =
        refl
    ; scaffoldPromoted =
        false
    ; scaffoldPromotedIsFalse =
        refl
    ; scaffoldBoundary =
        "Eight generator carrier scaffold for the SU(3) target lane is now explicit"
        ∷ "The embedded first-three-generator SU(2) subalgebra bracket is inhabited here"
        ∷ "The scaffold also records six coefficient-erased off-diagonal root-direction brackets touching generators 4 through 7"
        ∷ "Generator 8 now acts on the 4/5 and 6/7 root planes through eight coefficient-erased Cartan direction brackets"
        ∷ "A coefficient-carrying list-valued structure table is now supplied for unit, half, and sqrt3/2 Gell-Mann-style constants"
        ∷ "The multi-output Cartan brackets [4,5] and [6,7] now retain both the axis-3 and axis-8 components"
        ∷ "Coefficient-level Cartan-action brackets for [4,8], [5,8], [6,8], [7,8] and their reverses are explicitly witnessed in the structure table"
        ∷ "A finite 512-entry positive-axis Jacobi carrier is now supplied, and representative slots [1,2,3], [4,5,8], [6,7,8] have zero-residual witnesses"
        ∷ "The Jacobi carrier now also checks the 64 repeated-first-two-axis slots [x,x,z] as zero"
        ∷ "A local coefficient-aware [1,4,5] arithmetic witness is now explicit: -1/2 + 1/4 + 1/4 on axis 2"
        ∷ "A typed non-representative slot coefficient-term supply progress object is now canonical"
        ∷ "A typed all-slot coefficient-aware residual arithmetic progress object is now canonical"
        ∷ "A bounded all-slot coefficient-aware residual-zero witness progress object is now canonical"
        ∷ "A global 512-slot coefficient-aware Jacobi arithmetic carrier is now supplied with an explicit all-slot residual-zero witness"
        ∷ "The coefficient-aware all-slot residual queue is closed on this finite slot carrier"
        ∷ "The next blockers move to SFGC fibre representation and SU(3) trace/Killing Ad-invariance, not residual arithmetic"
        ∷ "No SFGC field-strength fibre representation, Killing trace, Ad-invariance, D_A law, Bianchi law, or sourced equation is promoted"
        ∷ []
    }

record YMSFGCDiscreteVariationIBPPrimitiveSupply : Set₁ where
  field
    VariationCarrier :
      Set

    ActionScalar :
      Set

    combineActionScalar :
      ActionScalar →
      ActionScalar →
      ActionScalar

    action :
      SFGC.GaugeField →
      ActionScalar

    variationOfAction :
      SFGC.GaugeField →
      VariationCarrier →
      ActionScalar

    eulerLagrangePairing :
      SFGC.GaugeField →
      VariationCarrier →
      ActionScalar

    boundaryTerm :
      SFGC.GaugeField →
      VariationCarrier →
      ActionScalar

    discreteIBPLaw :
      (A : SFGC.GaugeField) →
      (δA : VariationCarrier) →
      variationOfAction A δA
      ≡
      combineActionScalar
        (eulerLagrangePairing A δA)
        (boundaryTerm A δA)

    boundaryVanishingOrCondition :
      (A : SFGC.GaugeField) →
      (δA : VariationCarrier) →
      Set

    eulerLagrangeDStarFEqualsJTarget :
      SFGC.GaugeField →
      Set

    supplyBoundary :
      List String

record YMSFGCUserSuppliedNonFlatLatticeConnectionPrimitiveSupply : Set₁ where
  field
    NonFlatConnectionCarrier :
      Set

    connectionToGaugeField :
      NonFlatConnectionCarrier →
      SFGC.GaugeField

    gaugeTransformConnection :
      SFGS.GaugeTransform →
      NonFlatConnectionCarrier →
      NonFlatConnectionCarrier

    connectionCurvature :
      NonFlatConnectionCarrier →
      SFGC.SFGCSite2DPlaquette →
      SFGC.SFGCSite2DFieldStrengthBridge

    edgeTransport :
      NonFlatConnectionCarrier →
      SFGC.SFGCSite2DEdge →
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    plaquetteUsesExportedBoundaryEdges :
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      Set

    nonFlatWitness :
      Set

    supplyBoundary :
      List String

record YMSFGCDiscreteHodgeCovariantDerivativePrimitiveSupply : Set₁ where
  field
    DualCurvatureCarrier :
      Set

    CurrentCarrier :
      Set

    hodgeStar :
      SFGC.SFGCSite2DFieldStrengthBridge →
      DualCurvatureCarrier

    covariantDerivativeOnFieldStrength :
      SFGC.GaugeField →
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    covariantDerivativeOnDualCurvature :
      SFGC.GaugeField →
      DualCurvatureCarrier →
      CurrentCarrier

    currentSource :
      SFGC.GaugeField →
      CurrentCarrier

    dStarFEqualsJLaw :
      (A : SFGC.GaugeField) →
      covariantDerivativeOnDualCurvature
        A
        (hodgeStar
          (SFGC.sfgcSite2DFieldStrengthFromCurvature
            (SFGC.sfgcSite2Dδ₁
              (SFGC.sfgcSite2DConnectionTo1Form A))))
      ≡
      currentSource A

    covariantBianchiTarget :
      SFGC.GaugeField →
      Set

    supplyBoundary :
      List String

record DiscreteHodgeCovariantDerivativePrimitiveTypedRequest : Set₁ where
  field
    requestedDualCurvatureCarrier :
      Set

    requestedCurrentCarrier :
      Set

    requestedHodgeStarType :
      Set

    requestedCovariantDerivativeOnFieldStrengthType :
      Set

    requestedCovariantDerivativeOnDualType :
      Set

    requestedDStarFEqualsJTargetType :
      Set

    requestedCovariantBianchiTargetType :
      Set

    typedRequestBoundary :
      List String

canonicalDiscreteHodgeCovariantDerivativePrimitiveTypedRequest :
  DiscreteHodgeCovariantDerivativePrimitiveTypedRequest
canonicalDiscreteHodgeCovariantDerivativePrimitiveTypedRequest =
  record
    { requestedDualCurvatureCarrier =
        SFGC.SFGCSite2DFieldStrengthBridge
    ; requestedCurrentCarrier =
        YangMillsFieldEquationMissingPrerequisite
    ; requestedHodgeStarType =
        SFGC.SFGCSite2DDiscrete2Form →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; requestedCovariantDerivativeOnFieldStrengthType =
        SFGC.GaugeField →
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; requestedCovariantDerivativeOnDualType =
        SFGC.GaugeField →
        SFGC.SFGCSite2DFieldStrengthBridge →
        YangMillsFieldEquationMissingPrerequisite
    ; requestedDStarFEqualsJTargetType =
        SFGC.GaugeField →
        YangMillsFieldEquationMissingPrerequisite
    ; requestedCovariantBianchiTargetType =
        SFGC.GaugeField →
        YangMillsBianchiMissingPrimitive
    ; typedRequestBoundary =
        "Narrowed request: hodgeStar should act on the selected SFGCSite2DDiscrete2Form curvature carrier"
        ∷ "Narrowed request: D_A should act both on selected field-strength bridges and on the requested dual-curvature carrier"
        ∷ "The current canonical request uses obligation carriers only for current/source and equation targets"
        ∷ "No Hodge-star, current source, D * F = J law, or covariant Bianchi law is inhabited here"
        ∷ []
    }

data YMSFGCUserSuppliedNonFlatConnectionCarrier : Set where
  ymSFGCUserSuppliedSite2DConnection :
    SFGC.SFGCSite2DDiscrete1Form →
    (SFGC.SFGCSite2DPlaquette →
     SFGC.SFGCSite2DFieldStrengthBridge) →
    YMSFGCUserSuppliedNonFlatConnectionCarrier

sfgc1FormToUserSuppliedBridge :
  SFGC.SFGCSite2DDiscrete1Form →
  YMSFGCUserSuppliedNonFlatConnectionCarrier
sfgc1FormToUserSuppliedBridge connection =
  ymSFGCUserSuppliedSite2DConnection
    connection
    (λ plaquette →
      SFGC.sfgcSite2DFieldStrengthFromCurvature
        (SFGC.sfgcSite2Dδ₁ connection))

ymsfgcUserSuppliedConnection1Form :
  YMSFGCUserSuppliedNonFlatConnectionCarrier →
  SFGC.SFGCSite2DDiscrete1Form
ymsfgcUserSuppliedConnection1Form
  (ymSFGCUserSuppliedSite2DConnection connection curvature) =
  connection

ymsfgcUserSuppliedConnectionCurvature :
  YMSFGCUserSuppliedNonFlatConnectionCarrier →
  SFGC.SFGCSite2DPlaquette →
  SFGC.SFGCSite2DFieldStrengthBridge
ymsfgcUserSuppliedConnectionCurvature
  (ymSFGCUserSuppliedSite2DConnection connection curvature)
  plaquette =
  curvature plaquette

ymSFGCUserSuppliedConnection1Form :
  YMSFGCUserSuppliedNonFlatConnectionCarrier →
  SFGC.SFGCSite2DDiscrete1Form
ymSFGCUserSuppliedConnection1Form
  (ymSFGCUserSuppliedSite2DConnection connection curvature) =
  connection

ymSFGCUserSuppliedConnectionCurvature :
  YMSFGCUserSuppliedNonFlatConnectionCarrier →
  SFGC.SFGCSite2DPlaquette →
  SFGC.SFGCSite2DFieldStrengthBridge
ymSFGCUserSuppliedConnectionCurvature
  (ymSFGCUserSuppliedSite2DConnection connection curvature) =
  curvature

data YMSFGCUserSuppliedHolonomyCarrier : Set where
  ymSFGCUserSuppliedHolonomyFromPhase :
    SPTI4.Phase4 →
    YMSFGCUserSuppliedHolonomyCarrier

data YMSFGCUserSuppliedLieAlgebraCarrier : Set where

data YMSFGCUserSuppliedDualCurvatureCarrier : Set where
  ymSFGCUserSuppliedDualCurvatureFromFieldStrength :
    SFGC.SFGCSite2DFieldStrengthBridge →
    YMSFGCUserSuppliedDualCurvatureCarrier

ymSFGCUserSuppliedDualCurvatureFieldStrength :
  YMSFGCUserSuppliedDualCurvatureCarrier →
  SFGC.SFGCSite2DFieldStrengthBridge
ymSFGCUserSuppliedDualCurvatureFieldStrength
  (ymSFGCUserSuppliedDualCurvatureFromFieldStrength fieldStrength) =
  fieldStrength

data YMSFGCUserSuppliedCurrentCarrier : Set where
  ymSFGCUserSuppliedCurrentFromDualCurvature :
    YMSFGCUserSuppliedDualCurvatureCarrier →
    YMSFGCUserSuppliedCurrentCarrier

data YMSFGCUserSuppliedVariationCarrier : Set where

data YMSFGCUserSuppliedActionScalarCarrier : Set where

record YMSFGCUserSuppliedRealYMPrimitiveTypedRequest : Set₁ where
  field
    requestedSiteCarrier :
      Set

    requestedEdgeCarrier :
      Set

    requestedPlaquetteCarrier :
      Set

    requestedEdgeSource :
      requestedEdgeCarrier →
      requestedSiteCarrier

    requestedEdgeTarget :
      requestedEdgeCarrier →
      requestedSiteCarrier

    requestedPlaquetteSW :
      requestedPlaquetteCarrier →
      requestedSiteCarrier

    requestedPlaquetteBottomEdge :
      requestedPlaquetteCarrier →
      requestedEdgeCarrier

    requestedPlaquetteRightEdge :
      requestedPlaquetteCarrier →
      requestedEdgeCarrier

    requestedPlaquetteTopEdge :
      requestedPlaquetteCarrier →
      requestedEdgeCarrier

    requestedPlaquetteLeftEdge :
      requestedPlaquetteCarrier →
      requestedEdgeCarrier

    requestedNonFlatConnectionCarrier :
      Set

    requestedHolonomyCarrier :
      Set

    requestedLieAlgebraCarrier :
      Set

    requestedDualCurvatureCarrier :
      Set

    requestedCurrentCarrier :
      Set

    requestedVariationCarrier :
      Set

    requestedActionScalarCarrier :
      Set

    requestedConnectionToGaugeFieldType :
      Set

    requestedGaugeTransformConnectionType :
      Set

    requestedEdgeHolonomyType :
      Set

    requestedPlaquetteHolonomyType :
      Set

    requestedHolonomyTelescopingLawType :
      Set

    requestedHolonomyConjugationLawType :
      Set

    requestedBracketType :
      Set

    requestedKillingFormType :
      Set

    requestedKillingAdInvarianceLawType :
      Set

    requestedHodgeStarType :
      Set

    requestedCovariantDerivativeType :
      Set

    requestedDStarFEqualsJLawType :
      Set

    requestedDiscreteIBPLawType :
      Set

    requestPromoted :
      Bool

    requestPromotedIsFalse :
      requestPromoted ≡ false

    typedRequestBoundary :
      List String

canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest :
  YMSFGCUserSuppliedRealYMPrimitiveTypedRequest
canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest =
  record
    { requestedSiteCarrier =
        SFGC.SFGCSite2D
    ; requestedEdgeCarrier =
        SFGC.SFGCSite2DEdge
    ; requestedPlaquetteCarrier =
        SFGC.SFGCSite2DPlaquette
    ; requestedEdgeSource =
        SFGC.sfgcSite2DEdgeSourceTotal
    ; requestedEdgeTarget =
        SFGC.sfgcSite2DEdgeTargetTotal
    ; requestedPlaquetteSW =
        SFGC.sfgcSite2DPlaquetteSW
    ; requestedPlaquetteBottomEdge =
        SFGC.sfgcSite2DPlaquetteBottomEdge
    ; requestedPlaquetteRightEdge =
        SFGC.sfgcSite2DPlaquetteRightEdge
    ; requestedPlaquetteTopEdge =
        SFGC.sfgcSite2DPlaquetteTopEdge
    ; requestedPlaquetteLeftEdge =
        SFGC.sfgcSite2DPlaquetteLeftEdge
    ; requestedNonFlatConnectionCarrier =
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; requestedHolonomyCarrier =
        YMSFGCUserSuppliedHolonomyCarrier
    ; requestedLieAlgebraCarrier =
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedDualCurvatureCarrier =
        YMSFGCUserSuppliedDualCurvatureCarrier
    ; requestedCurrentCarrier =
        YMSFGCUserSuppliedCurrentCarrier
    ; requestedVariationCarrier =
        YMSFGCUserSuppliedVariationCarrier
    ; requestedActionScalarCarrier =
        YMSFGCUserSuppliedActionScalarCarrier
    ; requestedConnectionToGaugeFieldType =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        SFGC.GaugeField
    ; requestedGaugeTransformConnectionType =
        SFGS.GaugeTransform →
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; requestedEdgeHolonomyType =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        SFGC.SFGCSite2DEdge →
        YMSFGCUserSuppliedHolonomyCarrier
    ; requestedPlaquetteHolonomyType =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        SFGC.SFGCSite2DPlaquette →
        YMSFGCUserSuppliedHolonomyCarrier
    ; requestedHolonomyTelescopingLawType =
        (composeHolonomy :
          YMSFGCUserSuppliedHolonomyCarrier →
          YMSFGCUserSuppliedHolonomyCarrier →
          YMSFGCUserSuppliedHolonomyCarrier) →
        (inverseHolonomy :
          YMSFGCUserSuppliedHolonomyCarrier →
          YMSFGCUserSuppliedHolonomyCarrier) →
        (edgeHolonomy :
          YMSFGCUserSuppliedNonFlatConnectionCarrier →
          SFGC.SFGCSite2DEdge →
          YMSFGCUserSuppliedHolonomyCarrier) →
        (plaquetteHolonomy :
          YMSFGCUserSuppliedNonFlatConnectionCarrier →
          SFGC.SFGCSite2DPlaquette →
          YMSFGCUserSuppliedHolonomyCarrier) →
        (connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
        (plaquette : SFGC.SFGCSite2DPlaquette) →
        composeHolonomy
          (composeHolonomy
            (composeHolonomy
              (edgeHolonomy
                connection
                (SFGC.sfgcSite2DPlaquetteBottomEdge plaquette))
              (edgeHolonomy
                connection
                (SFGC.sfgcSite2DPlaquetteRightEdge plaquette)))
            (inverseHolonomy
              (edgeHolonomy
                connection
                (SFGC.sfgcSite2DPlaquetteTopEdge plaquette))))
          (inverseHolonomy
            (edgeHolonomy
              connection
              (SFGC.sfgcSite2DPlaquetteLeftEdge plaquette)))
        ≡
        plaquetteHolonomy connection plaquette
    ; requestedHolonomyConjugationLawType =
        (gaugeTransformConnection :
          SFGS.GaugeTransform →
          YMSFGCUserSuppliedNonFlatConnectionCarrier →
          YMSFGCUserSuppliedNonFlatConnectionCarrier) →
        (plaquetteHolonomy :
          YMSFGCUserSuppliedNonFlatConnectionCarrier →
          SFGC.SFGCSite2DPlaquette →
          YMSFGCUserSuppliedHolonomyCarrier) →
        (endpointGaugeFactor :
          SFGS.GaugeTransform →
          SFGC.SFGCSite2D →
          YMSFGCUserSuppliedHolonomyCarrier) →
        (conjugateBy :
          YMSFGCUserSuppliedHolonomyCarrier →
          YMSFGCUserSuppliedHolonomyCarrier →
          YMSFGCUserSuppliedHolonomyCarrier) →
        (gauge : SFGS.GaugeTransform) →
        (connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
        (plaquette : SFGC.SFGCSite2DPlaquette) →
        plaquetteHolonomy
          (gaugeTransformConnection gauge connection)
          plaquette
        ≡
        conjugateBy
          (endpointGaugeFactor
            gauge
            (SFGC.sfgcSite2DPlaquetteSW plaquette))
          (plaquetteHolonomy connection plaquette)
    ; requestedBracketType =
        YMSFGCUserSuppliedLieAlgebraCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedKillingFormType =
        YMSFGCUserSuppliedLieAlgebraCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier →
        ℤ
    ; requestedKillingAdInvarianceLawType =
        (adjointAction :
          SFGS.GaugeTransform →
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (killingForm :
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier →
          ℤ) →
        (gauge : SFGS.GaugeTransform) →
        (x y : YMSFGCUserSuppliedLieAlgebraCarrier) →
        killingForm
          (adjointAction
            gauge
            x)
          (adjointAction
            gauge
            y)
        ≡
        killingForm x y
    ; requestedHodgeStarType =
        SFGC.SFGCSite2DFieldStrengthBridge →
        YMSFGCUserSuppliedDualCurvatureCarrier
    ; requestedCovariantDerivativeType =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMSFGCUserSuppliedDualCurvatureCarrier →
        YMSFGCUserSuppliedCurrentCarrier
    ; requestedDStarFEqualsJLawType =
        (covariantDerivative :
          YMSFGCUserSuppliedNonFlatConnectionCarrier →
          YMSFGCUserSuppliedDualCurvatureCarrier →
          YMSFGCUserSuppliedCurrentCarrier) →
        (connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
        (dualCurvature : YMSFGCUserSuppliedDualCurvatureCarrier) →
        (current : YMSFGCUserSuppliedCurrentCarrier) →
        covariantDerivative connection dualCurvature
        ≡
        current
    ; requestedDiscreteIBPLawType =
        (variationOfAction :
          YMSFGCUserSuppliedNonFlatConnectionCarrier →
          YMSFGCUserSuppliedVariationCarrier →
          YMSFGCUserSuppliedActionScalarCarrier) →
        (eulerLagrangePairing :
          YMSFGCUserSuppliedNonFlatConnectionCarrier →
          YMSFGCUserSuppliedVariationCarrier →
          YMSFGCUserSuppliedActionScalarCarrier) →
        (boundaryTerm :
          YMSFGCUserSuppliedNonFlatConnectionCarrier →
          YMSFGCUserSuppliedVariationCarrier →
          YMSFGCUserSuppliedActionScalarCarrier) →
        (combineActionScalar :
          YMSFGCUserSuppliedActionScalarCarrier →
          YMSFGCUserSuppliedActionScalarCarrier →
          YMSFGCUserSuppliedActionScalarCarrier) →
        (connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
        (δA : YMSFGCUserSuppliedVariationCarrier) →
        variationOfAction connection δA
        ≡
        combineActionScalar
          (eulerLagrangePairing connection δA)
          (boundaryTerm connection δA)
    ; requestPromoted =
        false
    ; requestPromotedIsFalse =
        refl
    ; typedRequestBoundary =
        "SFGC exposes enough geometry for the request: SFGCSite2DEdge has total source/target maps and SFGCSite2DPlaquette exposes SW plus bottom/right/top/left edges"
        ∷ "The user-supplied non-flat connection carrier has a finite Site2D adapter, while the full real connection laws remain external supplied data"
        ∷ "Holonomy telescoping is requested against the exact SFGCSite2D plaquette boundary edges"
        ∷ "Holonomy conjugation is requested at the plaquette SW endpoint gauge factor"
        ∷ "Lie algebra, bracket, Killing form, and Ad-invariance are requested as a separate supplied finite algebra layer"
        ∷ "Hodge star, covariant derivative on dual curvature, D * F = J target, and discrete IBP law are typed as requests only"
        ∷ "No D * F = J, D F = 0, Yang-Mills closure, or Bianchi promotion is inhabited by this request"
        ∷ []
    }

record YMSFGCNonAbelianCovariantDerivativeTypedRequest : Set₁ where
  field
    requestedFibreLieAlgebraCarrier :
      Set

    requestedZeroType :
      Set

    requestedAdditionType :
      Set

    requestedNegationType :
      Set

    requestedBracketType :
      Set

    requestedBracketAntisymmetryType :
      Set

    requestedJacobiWitnessType :
      Set

    requestedExteriorDerivativeType :
      Set

    requestedConnectionOneFormInFibreType :
      Set

    requestedCurvatureInFibreType :
      Set

    requestedCovariantDerivativeType :
      Set

    requestedDAEqualsDPlusBracketType :
      Set

    requestedDASquaredCurvatureActionType :
      Set

    requestPromoted :
      Bool

    requestPromotedIsFalse :
      requestPromoted ≡ false

    typedRequestBoundary :
      List String

canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest :
  YMSFGCNonAbelianCovariantDerivativeTypedRequest
canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest =
  record
    { requestedFibreLieAlgebraCarrier =
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedZeroType =
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedAdditionType =
        YMSFGCUserSuppliedLieAlgebraCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedNegationType =
        YMSFGCUserSuppliedLieAlgebraCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedBracketType =
        YMSFGCUserSuppliedLieAlgebraCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedBracketAntisymmetryType =
        (negate :
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (bracket :
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (x y : YMSFGCUserSuppliedLieAlgebraCarrier) →
        bracket x y
        ≡
        negate (bracket y x)
    ; requestedJacobiWitnessType =
        (zero :
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (add :
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (bracket :
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (x y z : YMSFGCUserSuppliedLieAlgebraCarrier) →
        add
          (add
            (bracket x (bracket y z))
            (bracket y (bracket z x)))
          (bracket z (bracket x y))
        ≡
        zero
    ; requestedExteriorDerivativeType =
        YMSFGCUserSuppliedLieAlgebraCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedConnectionOneFormInFibreType =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedCurvatureInFibreType =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedCovariantDerivativeType =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedDAEqualsDPlusBracketType =
        (add :
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (bracket :
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (d :
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (connectionOneFormAsFibreAlgebra :
          YMSFGCUserSuppliedNonFlatConnectionCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (covariantDerivative :
          YMSFGCUserSuppliedNonFlatConnectionCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
        (section : YMSFGCUserSuppliedLieAlgebraCarrier) →
        covariantDerivative connection section
        ≡
        add
          (d section)
          (bracket
            (connectionOneFormAsFibreAlgebra connection)
            section)
    ; requestedDASquaredCurvatureActionType =
        (bracket :
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (curvatureAsFibreAlgebra :
          YMSFGCUserSuppliedNonFlatConnectionCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (covariantDerivative :
          YMSFGCUserSuppliedNonFlatConnectionCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier →
          YMSFGCUserSuppliedLieAlgebraCarrier) →
        (connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
        (section : YMSFGCUserSuppliedLieAlgebraCarrier) →
        covariantDerivative
          connection
          (covariantDerivative connection section)
        ≡
        bracket (curvatureAsFibreAlgebra connection) section
    ; requestPromoted =
        false
    ; requestPromotedIsFalse =
        refl
    ; typedRequestBoundary =
        "The requested fibre algebra is explicitly non-abelian: bracket is primitive data, not Phase4 addition"
        ∷ "Additive inverse and bracket antisymmetry are requested explicitly; the string-combinator LieAlgebra surface is not a valid SFGC fibre inhabitant"
        ∷ "Jacobi is requested as a witness over that bracket and fibre addition"
        ∷ "D_A is requested as d + [A,_] after translating the connection one-form into the fibre Lie algebra"
        ∷ "The curvature-action receipt target is D_A^2(s) = [F_A,s]"
        ∷ "The local finite 3-axis witness supplies bracket/antisymmetry/Jacobi, while the SFGC fibre representation still requires a gauge-compatible law surface"
        ∷ []
    }

record YMSFGCNonAbelianCovariantDerivativeTheoremThinReceipt : Set₁ where
  field
    typedNonAbelianCovariantDerivativeRequest :
      YMSFGCNonAbelianCovariantDerivativeTypedRequest

    typedNonAbelianCovariantDerivativeRequestIsCanonical :
      typedNonAbelianCovariantDerivativeRequest
      ≡
      canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest

    exactNonAbelianCovariantDerivativeMissingPrimitives :
      List YMSFGCNonAbelianCovariantDerivativeMissingPrimitive

    exactNonAbelianCovariantDerivativeMissingPrimitivesAreCanonical :
      exactNonAbelianCovariantDerivativeMissingPrimitives
      ≡
      canonicalYMSFGCNonAbelianCovariantDerivativeMissingPrimitives

    localFiniteLie3PrimitiveSupply :
      YMSFGCNonAbelianCovariantDerivativePrimitiveSupply

    localFiniteLie3PrimitiveSupplyIsCanonical :
      localFiniteLie3PrimitiveSupply
      ≡
      canonicalYMSFGCLocalFiniteLie3PrimitiveSupply

    localFiniteLie3NonAbelianBracketWitness :
      localFiniteLie3Bracket
        (lieBasis signPos axisX)
        (lieBasis signPos axisY)
      ≡
      lieBasis signPos axisZ

    localFiniteLie3NonAbelianBracketWitnessIsCanonical :
      localFiniteLie3NonAbelianBracketWitness
      ≡
      localFiniteLie3BracketIsNonAbelian

    localFiniteSU3Scaffold :
      YMSFGCLocalFiniteSU3Scaffold

    localFiniteSU3ScaffoldIsCanonical :
      localFiniteSU3Scaffold
      ≡
      canonicalYMSFGCLocalFiniteSU3Scaffold

    localFiniteSU3EmbeddedSU2XYBracketWitness :
      localFiniteSU3Bracket
        (localFiniteSU3Embed (lieBasis signPos axisX))
        (localFiniteSU3Embed (lieBasis signPos axisY))
      ≡
      localFiniteSU3Embed (lieBasis signPos axisZ)

    localFiniteSU3EmbeddedSU2XYBracketWitnessIsCanonical :
      localFiniteSU3EmbeddedSU2XYBracketWitness
      ≡
      localFiniteSU3EmbeddedSU2XYBracket

    localFiniteLieValuedFormsAndCurvature :
      YMSFGCLocalFiniteLieValuedFormsAndCurvature

    localFiniteLieValuedFormsAndCurvatureIsCanonical :
      localFiniteLieValuedFormsAndCurvature
      ≡
      canonicalYMSFGCLocalFiniteLieValuedFormsAndCurvature

    sfgcFieldStrengthFibreRepresentationIntoLocalFiniteSU3 :
      SFGC.SFGCSite2D →
      SFGC.SFGCSite2DFieldStrengthBridge →
      YMSFGCLocalFiniteSU3Carrier

    sfgcFieldStrengthFibreRepresentationReferenceLaw :
      (site : SFGC.SFGCSite2D) →
      (phase : SPTI4.Phase4) →
      sfgcFieldStrengthFibreRepresentationIntoLocalFiniteSU3
        site
        (SFGC.sfgcSite2DFieldStrengthFromCurvature
          (SFGC.sfgcSite2DArbitrary2Form (λ plaquette → phase)))
      ≡
      sfgcFieldStrengthFibreRepresentationIntoLocalFiniteSU3
        site
        (SFGC.sfgcSite2DFieldStrengthFromCurvature
          (SFGC.sfgcSite2DArbitrary2Form (λ plaquette → phase)))

    firstRemainingNonAbelianPrimitive :
      YMSFGCNonAbelianCovariantDerivativeMissingPrimitive

    firstRemainingNonAbelianPrimitiveIsConnectionOneForm :
      firstRemainingNonAbelianPrimitive
      ≡
      missingConnectionOneFormAsFibreAlgebraElement

    requestedLieBracketLaw :
      String

    requestedBracketAntisymmetryWitness :
      String

    requestedJacobiWitness :
      String

    requestedCovariantDerivativeFormula :
      String

    requestedCurvatureActionTheorem :
      String

    receiptPromoted :
      Bool

    receiptPromotedIsFalse :
      receiptPromoted ≡ false

    receiptBoundary :
      List String

canonicalYMSFGCNonAbelianCovariantDerivativeTheoremThinReceipt :
  YMSFGCNonAbelianCovariantDerivativeTheoremThinReceipt
canonicalYMSFGCNonAbelianCovariantDerivativeTheoremThinReceipt =
  record
    { typedNonAbelianCovariantDerivativeRequest =
        canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest
    ; typedNonAbelianCovariantDerivativeRequestIsCanonical =
        refl
    ; exactNonAbelianCovariantDerivativeMissingPrimitives =
        canonicalYMSFGCNonAbelianCovariantDerivativeMissingPrimitives
    ; exactNonAbelianCovariantDerivativeMissingPrimitivesAreCanonical =
        refl
    ; localFiniteLie3PrimitiveSupply =
        canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
    ; localFiniteLie3PrimitiveSupplyIsCanonical =
        refl
    ; localFiniteLie3NonAbelianBracketWitness =
        localFiniteLie3BracketIsNonAbelian
    ; localFiniteLie3NonAbelianBracketWitnessIsCanonical =
        refl
    ; localFiniteSU3Scaffold =
        canonicalYMSFGCLocalFiniteSU3Scaffold
    ; localFiniteSU3ScaffoldIsCanonical =
        refl
    ; localFiniteSU3EmbeddedSU2XYBracketWitness =
        localFiniteSU3EmbeddedSU2XYBracket
    ; localFiniteSU3EmbeddedSU2XYBracketWitnessIsCanonical =
        refl
    ; localFiniteLieValuedFormsAndCurvature =
        canonicalYMSFGCLocalFiniteLieValuedFormsAndCurvature
    ; localFiniteLieValuedFormsAndCurvatureIsCanonical =
        refl
    ; sfgcFieldStrengthFibreRepresentationIntoLocalFiniteSU3 =
        λ site fieldStrength → su3Zero
    ; sfgcFieldStrengthFibreRepresentationReferenceLaw =
        λ site phase → refl
    ; firstRemainingNonAbelianPrimitive =
        missingConnectionOneFormAsFibreAlgebraElement
    ; firstRemainingNonAbelianPrimitiveIsConnectionOneForm =
        refl
    ; requestedLieBracketLaw =
        "bracket : FibreLieAlgebra -> FibreLieAlgebra -> FibreLieAlgebra"
    ; requestedBracketAntisymmetryWitness =
        "antisymmetry : [x,y] == -[y,x]"
    ; requestedJacobiWitness =
        "Jacobi : [x,[y,z]] + [y,[z,x]] + [z,[x,y]] == 0"
    ; requestedCovariantDerivativeFormula =
        "D_A(s) = d(s) + [A,s]"
    ; requestedCurvatureActionTheorem =
        "D_A^2(s) = [F_A,s]"
    ; receiptPromoted =
        false
    ; receiptPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Theorem-thin receipt only: it names the non-abelian fibre algebra, bracket, Jacobi witness, D_A formula, and curvature-action theorem target"
        ∷ "It now explicitly asks for additive inverse and bracket antisymmetry before Jacobi can count as a real Lie-algebra witness"
        ∷ "It contains a local finite 3-axis bracket witness with signed antisymmetry and a Jacobi collapse check"
        ∷ "It now contains an explicit local finite Lie-valued forms package with A as a 1-form, F_A as a 2-form, D_A on sections, and a witnessed D_A^2=[F_A,_] action law"
        ∷ "It contains an eight-generator SU(3)-target scaffold with the embedded SU(2) first-three-generator bracket, six off-diagonal root-direction brackets, and eight generator-8 Cartan action brackets checked"
        ∷ "That scaffold now fills the coefficient-carrying multi-output SU(3) structure table, a finite 512-entry positive-axis Jacobi carrier, and a 64-slot repeated-axis zero batch, but not the all-zero residual proof"
        ∷ "A concrete typed SFGC field-strength fibre representation candidate into the local finite SU(3) carrier is now wired"
        ∷ "The candidate remains non-promoting: no gauge-compatible representation law or connection one-form action into that carrier is supplied"
        ∷ "It deliberately does not reuse finite Phase4 as a non-abelian Lie algebra"
        ∷ "It keeps D_A^2(s) = [F_A,s] as a typed target until a supplied non-flat fibre algebra and connection action inhabit it"
        ∷ "No Yang-Mills equation, Bianchi promotion, mass gap, or spectral-gap claim follows"
        ∷ []
    }

data YMSFGCRealYMPrimitiveSupplySurfaceName : Set where
  userSuppliedNonFlatLatticeConnectionSurface :
    YMSFGCRealYMPrimitiveSupplySurfaceName

  nonFlatHolonomyTelescopingSupplySurface :
    YMSFGCRealYMPrimitiveSupplySurfaceName

  lieAlgebraTraceAdInvarianceSupplySurface :
    YMSFGCRealYMPrimitiveSupplySurfaceName

  nonAbelianCovariantDerivativeSupplySurface :
    YMSFGCRealYMPrimitiveSupplySurfaceName

  discreteHodgeCovariantDerivativeSupplySurface :
    YMSFGCRealYMPrimitiveSupplySurfaceName

  discreteVariationIBPSupplySurface :
    YMSFGCRealYMPrimitiveSupplySurfaceName

canonicalYMSFGCRealYMPrimitiveSupplySurfaceNames :
  List YMSFGCRealYMPrimitiveSupplySurfaceName
canonicalYMSFGCRealYMPrimitiveSupplySurfaceNames =
  userSuppliedNonFlatLatticeConnectionSurface
  ∷ nonFlatHolonomyTelescopingSupplySurface
  ∷ lieAlgebraTraceAdInvarianceSupplySurface
  ∷ nonAbelianCovariantDerivativeSupplySurface
  ∷ discreteHodgeCovariantDerivativeSupplySurface
  ∷ discreteVariationIBPSupplySurface
  ∷ []

record YMSFGCRealYMPrimitiveSupplyRequestPack : Set₁ where
  field
    requestedSupplySurfaces :
      List YMSFGCRealYMPrimitiveSupplySurfaceName

    requestedSupplySurfacesAreCanonical :
      requestedSupplySurfaces
      ≡
      canonicalYMSFGCRealYMPrimitiveSupplySurfaceNames

    userSuppliedRealYMPrimitiveTypedRequest :
      YMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    userSuppliedRealYMPrimitiveTypedRequestIsCanonical :
      userSuppliedRealYMPrimitiveTypedRequest
      ≡
      canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    exactNonFlatHolonomyIrreducibility :
      List YMSFGCNonFlatHolonomyConjugationIrreducibility

    exactNonFlatHolonomyIrreducibilityIsCanonical :
      exactNonFlatHolonomyIrreducibility
      ≡
      canonicalYMSFGCNonFlatHolonomyConjugationIrreducibility

    exactKillingAdInvarianceIrreducibility :
      List YMSFGCRealKillingAdInvarianceIrreducibility

    exactKillingAdInvarianceIrreducibilityIsCanonical :
      exactKillingAdInvarianceIrreducibility
      ≡
      canonicalYMSFGCRealKillingAdInvarianceIrreducibility

    firstHolonomyMissingPrimitive :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstHolonomyMissingPrimitiveIsNonFlatCurvature :
      firstHolonomyMissingPrimitive
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    firstKillingMissingPrimitive :
      YMSFGCRealKillingAdInvarianceIrreducibility

    firstKillingMissingPrimitiveIsLieAlgebraCarrier :
      firstKillingMissingPrimitive
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    firstIBPMissingPrimitive :
      YangMillsVariationalEquationMissingPrimitive

    firstIBPMissingPrimitiveIsVariationPairing :
      firstIBPMissingPrimitive
      ≡
      missingVariationPairingForSelectedHodgeStar

    requestPromoted :
      Bool

    requestPromotedIsFalse :
      requestPromoted ≡ false

    requestBoundary :
      List String

canonicalYMSFGCRealYMPrimitiveSupplyRequestPack :
  YMSFGCRealYMPrimitiveSupplyRequestPack
canonicalYMSFGCRealYMPrimitiveSupplyRequestPack =
  record
    { requestedSupplySurfaces =
        canonicalYMSFGCRealYMPrimitiveSupplySurfaceNames
    ; requestedSupplySurfacesAreCanonical =
        refl
    ; userSuppliedRealYMPrimitiveTypedRequest =
        canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; userSuppliedRealYMPrimitiveTypedRequestIsCanonical =
        refl
    ; exactNonFlatHolonomyIrreducibility =
        canonicalYMSFGCNonFlatHolonomyConjugationIrreducibility
    ; exactNonFlatHolonomyIrreducibilityIsCanonical =
        refl
    ; exactKillingAdInvarianceIrreducibility =
        canonicalYMSFGCRealKillingAdInvarianceIrreducibility
    ; exactKillingAdInvarianceIrreducibilityIsCanonical =
        refl
    ; firstHolonomyMissingPrimitive =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; firstHolonomyMissingPrimitiveIsNonFlatCurvature =
        refl
    ; firstKillingMissingPrimitive =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; firstKillingMissingPrimitiveIsLieAlgebraCarrier =
        refl
    ; firstIBPMissingPrimitive =
        missingVariationPairingForSelectedHodgeStar
    ; firstIBPMissingPrimitiveIsVariationPairing =
        refl
    ; requestPromoted =
        false
    ; requestPromotedIsFalse =
        refl
    ; requestBoundary =
        "Typed supply request only: user-supplied non-flat lattice connection needs a carrier, gauge action on connections, and edge/plaquette holonomy over the exported SFGCSite2D endpoints"
        ∷ "Typed supply request only: non-flat holonomy needs edge holonomy, plaquette holonomy, endpoint gauge factors, boundary telescoping, and gauge conjugation"
        ∷ "Typed supply request only: trace/Killing Ad-invariance needs a Lie algebra carrier, bracket, nontrivial adjoint action, pairing, and Ad-invariance proof"
        ∷ "Typed supply request only: discrete Hodge/covariant derivative needs Hodge star on selected field strength, D_A on dual curvature, current carrier, and target laws"
        ∷ "Typed supply request only: discrete IBP needs a variation carrier, action variation, Euler-Lagrange pairing, boundary term, boundary condition, and Euler-Lagrange target"
        ∷ "Current SFGC/SFGS APIs expose finite Phase4, flat selected Wilson loops, and identity adjoint candidates, so these supplies are not inhabited here"
        ∷ "No D * F = J, D F = 0, Yang-Mills closure, Maxwell closure, mass gap, or spectral-gap promotion follows from this request pack"
        ∷ []
    }

data YMSFGCGate3NonFlatSFGCSite2DHandoffStatus : Set where
  gate3NonFlatSFGCSite2DPrimitivesStagedNoPromotion :
    YMSFGCGate3NonFlatSFGCSite2DHandoffStatus

record YMSFGCGate3NonFlatSFGCSite2DHandoffReceipt : Set₁ where
  field
    status :
      YMSFGCGate3NonFlatSFGCSite2DHandoffStatus

    primitiveSupplyRequestPack :
      YMSFGCRealYMPrimitiveSupplyRequestPack

    primitiveSupplyRequestPackIsCanonical :
      primitiveSupplyRequestPack
      ≡
      canonicalYMSFGCRealYMPrimitiveSupplyRequestPack

    requestedNonFlatConnectionCarrier :
      Set

    requestedNonFlatConnectionCarrierIsUserSupplied :
      requestedNonFlatConnectionCarrier
      ≡
      YMSFGCUserSuppliedNonFlatConnectionCarrier

    requestedGaugeTransformConnectionType :
      Set

    requestedConnectionCurvatureType :
      Set

    available1FormToUserConnectionBridge :
      SFGC.SFGCSite2DDiscrete1Form →
      YMSFGCUserSuppliedNonFlatConnectionCarrier

    available1FormToUserConnectionBridgeIsSFGCAdapter :
      available1FormToUserConnectionBridge
      ≡
      sfgc1FormToUserSuppliedBridge

    availableConnectionCurvatureProjection :
      YMSFGCUserSuppliedNonFlatConnectionCarrier →
      SFGC.SFGCSite2DPlaquette →
      SFGC.SFGCSite2DFieldStrengthBridge

    availableConnectionCurvatureProjectionIsProjection :
      availableConnectionCurvatureProjection
      ≡
      ymsfgcUserSuppliedConnectionCurvature

    availableCurvatureToFieldStrength :
      SFGC.SFGCSite2DDiscrete2Form →
      SFGC.SFGCSite2DFieldStrengthBridge

    availableCurvatureToFieldStrengthIsSFGC :
      availableCurvatureToFieldStrength
      ≡
      SFGC.sfgcSite2DFieldStrengthFromCurvature

    requestedHolonomyTelescopingLawType :
      Set

    requestedHolonomyConjugationLawType :
      Set

    requestedKillingAdInvarianceLawType :
      Set

    exactNonFlatHolonomyBlockers :
      List YMSFGCNonFlatHolonomyConjugationIrreducibility

    exactNonFlatHolonomyBlockersAreCanonical :
      exactNonFlatHolonomyBlockers
      ≡
      canonicalYMSFGCNonFlatHolonomyConjugationIrreducibility

    firstNonFlatHolonomyBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstNonFlatHolonomyBlockerIsCurvature :
      firstNonFlatHolonomyBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    exactKillingAdInvarianceBlockers :
      List YMSFGCRealKillingAdInvarianceIrreducibility

    exactKillingAdInvarianceBlockersAreCanonical :
      exactKillingAdInvarianceBlockers
      ≡
      canonicalYMSFGCRealKillingAdInvarianceIrreducibility

    firstKillingAdInvarianceBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    firstKillingAdInvarianceBlockerIsLieAlgebraCarrier :
      firstKillingAdInvarianceBlocker
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    nonFlatCurvatureTheoremSurface :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    nonFlatCurvatureTheoremSurfaceIsCurvature :
      nonFlatCurvatureTheoremSurface
      ≡
      nonFlatCurvatureWitness sfgcCanonicalNonFlatCurvature2Form

    handoffBoundary :
      List String

canonicalYMSFGCGate3NonFlatSFGCSite2DHandoffReceipt :
  YMSFGCGate3NonFlatSFGCSite2DHandoffReceipt
canonicalYMSFGCGate3NonFlatSFGCSite2DHandoffReceipt =
  record
    { status =
        gate3NonFlatSFGCSite2DPrimitivesStagedNoPromotion
    ; primitiveSupplyRequestPack =
        canonicalYMSFGCRealYMPrimitiveSupplyRequestPack
    ; primitiveSupplyRequestPackIsCanonical =
        refl
    ; requestedNonFlatConnectionCarrier =
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; requestedNonFlatConnectionCarrierIsUserSupplied =
        refl
    ; requestedGaugeTransformConnectionType =
        SFGS.GaugeTransform →
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; requestedConnectionCurvatureType =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        SFGC.SFGCSite2DPlaquette →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; available1FormToUserConnectionBridge =
        sfgc1FormToUserSuppliedBridge
    ; available1FormToUserConnectionBridgeIsSFGCAdapter =
        refl
    ; availableConnectionCurvatureProjection =
        ymsfgcUserSuppliedConnectionCurvature
    ; availableConnectionCurvatureProjectionIsProjection =
        refl
    ; availableCurvatureToFieldStrength =
        SFGC.sfgcSite2DFieldStrengthFromCurvature
    ; availableCurvatureToFieldStrengthIsSFGC =
        refl
    ; requestedHolonomyTelescopingLawType =
        YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedHolonomyTelescopingLawType
          canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; requestedHolonomyConjugationLawType =
        YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedHolonomyConjugationLawType
          canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; requestedKillingAdInvarianceLawType =
        YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedKillingAdInvarianceLawType
          canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; exactNonFlatHolonomyBlockers =
        canonicalYMSFGCNonFlatHolonomyConjugationIrreducibility
    ; exactNonFlatHolonomyBlockersAreCanonical =
        refl
    ; firstNonFlatHolonomyBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; firstNonFlatHolonomyBlockerIsCurvature =
        refl
    ; exactKillingAdInvarianceBlockers =
        canonicalYMSFGCRealKillingAdInvarianceIrreducibility
    ; exactKillingAdInvarianceBlockersAreCanonical =
        refl
    ; firstKillingAdInvarianceBlocker =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; firstKillingAdInvarianceBlockerIsLieAlgebraCarrier =
        refl
    ; nonFlatCurvatureTheoremSurface =
        nonFlatCurvatureWitness sfgcCanonicalNonFlatCurvature2Form
    ; nonFlatCurvatureTheoremSurfaceIsCurvature =
        refl
    ; handoffBoundary =
        "Gate 3 Site2D handoff: NonFlatConnectionCarrier is now inhabited locally by the SFGCSite2D 1-form adapter"
        ∷ "Gate 3 Site2D handoff only: gaugeTransformConnection must act on the supplied non-flat connection carrier"
        ∷ "Gate 3 Site2D handoff: connectionCurvature is available as the SFGC-backed carrier projection over exported plaquettes"
        ∷ "Available bridges: SFGCSite2DDiscrete1Form adapts to the user carrier, and SFGC.sfgcSite2DFieldStrengthFromCurvature lowers δ1 curvature to field strength"
        ∷ "Holonomy handoff requires edge holonomy, plaquette holonomy, boundary telescoping over bottom/right/top/left edges, endpoint gauge factors, and SW-based conjugation"
        ∷ "Killing handoff requires a Lie algebra carrier, nontrivial adjoint action, trace/Killing pairing, and Ad-invariance proof"
        ∷ "The first non-flat holonomy blocker is intentionally still missingNonFlatSFGCSite2DConnectionCurvature"
        ∷ "No non-flat curvature, Yang-Mills equation, mass-gap, Clay, or terminal promotion is asserted by this receipt"
        ∷ []
    }

data YMSFGCGate3M1NonFlatCurvatureBlockerChainStatus : Set where
  gate3M1FirstMissingCurvatureFieldsExposedNoPromotion :
    YMSFGCGate3M1NonFlatCurvatureBlockerChainStatus

record YMSFGCGate3M1NonFlatCurvatureBlockerChainLedger : Set₁ where
  field
    status :
      YMSFGCGate3M1NonFlatCurvatureBlockerChainStatus

    gate3NonFlatSFGCSite2DHandoffReceipt :
      YMSFGCGate3NonFlatSFGCSite2DHandoffReceipt

    gate3NonFlatSFGCSite2DHandoffReceiptIsCanonical :
      gate3NonFlatSFGCSite2DHandoffReceipt
      ≡
      canonicalYMSFGCGate3NonFlatSFGCSite2DHandoffReceipt

    requestedSiteCarrier :
      Set

    requestedSiteCarrierIsSFGCSite2D :
      requestedSiteCarrier
      ≡
      SFGC.SFGCSite2D

    requestedEdgeCarrier :
      Set

    requestedEdgeCarrierIsSFGCSite2DEdge :
      requestedEdgeCarrier
      ≡
      SFGC.SFGCSite2DEdge

    requestedPlaquetteCarrier :
      Set

    requestedPlaquetteCarrierIsSFGCSite2DPlaquette :
      requestedPlaquetteCarrier
      ≡
      SFGC.SFGCSite2DPlaquette

    requestedPlaquetteSW :
      SFGC.SFGCSite2DPlaquette →
      SFGC.SFGCSite2D

    requestedPlaquetteSWIsSFGC :
      requestedPlaquetteSW
      ≡
      SFGC.sfgcSite2DPlaquetteSW

    requestedPlaquetteBottomEdge :
      SFGC.SFGCSite2DPlaquette →
      SFGC.SFGCSite2DEdge

    requestedPlaquetteBottomEdgeIsSFGC :
      requestedPlaquetteBottomEdge
      ≡
      SFGC.sfgcSite2DPlaquetteBottomEdge

    requestedPlaquetteRightEdge :
      SFGC.SFGCSite2DPlaquette →
      SFGC.SFGCSite2DEdge

    requestedPlaquetteRightEdgeIsSFGC :
      requestedPlaquetteRightEdge
      ≡
      SFGC.sfgcSite2DPlaquetteRightEdge

    requestedPlaquetteTopEdge :
      SFGC.SFGCSite2DPlaquette →
      SFGC.SFGCSite2DEdge

    requestedPlaquetteTopEdgeIsSFGC :
      requestedPlaquetteTopEdge
      ≡
      SFGC.sfgcSite2DPlaquetteTopEdge

    requestedPlaquetteLeftEdge :
      SFGC.SFGCSite2DPlaquette →
      SFGC.SFGCSite2DEdge

    requestedPlaquetteLeftEdgeIsSFGC :
      requestedPlaquetteLeftEdge
      ≡
      SFGC.sfgcSite2DPlaquetteLeftEdge

    requestedNonFlatConnectionCarrier :
      Set

    requestedNonFlatConnectionCarrierIsUserSupplied :
      requestedNonFlatConnectionCarrier
      ≡
      YMSFGCUserSuppliedNonFlatConnectionCarrier

    requestedHolonomyCarrier :
      Set

    requestedHolonomyCarrierIsUserSupplied :
      requestedHolonomyCarrier
      ≡
      YMSFGCUserSuppliedHolonomyCarrier

    requestedLieAlgebraCarrier :
      Set

    requestedLieAlgebraCarrierIsUserSupplied :
      requestedLieAlgebraCarrier
      ≡
      YMSFGCUserSuppliedLieAlgebraCarrier

    requestedConnectionCurvatureFieldType :
      Set

    requestedEndpointGaugeFactorType :
      Set

    requestedPlaquetteHolonomyType :
      Set

    requestedConjugationLawType :
      Set

    requestedFieldStrengthToLieAlgebraType :
      Set

    requestedNontrivialFieldStrengthAdjointActionType :
      Set

    requestedKillingOrTracePairingType :
      Set

    requestedAdInvarianceProofType :
      Set

    firstRemainingHolonomyBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstRemainingHolonomyBlockerIsNonFlatCurvature :
      firstRemainingHolonomyBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    nextEndpointGaugeFactorBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    nextEndpointGaugeFactorBlockerIsEndpointGaugeFactors :
      nextEndpointGaugeFactorBlocker
      ≡
      missingEndpointGaugeFactorsForPlaquetteHolonomy

    nextFieldStrengthAdjointBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    nextFieldStrengthAdjointBlockerIsNontrivialAdjoint :
      nextFieldStrengthAdjointBlocker
      ≡
      missingNontrivialFieldStrengthAdjointAction

    nextConjugationLawBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    nextConjugationLawBlockerIsConjugationLaw :
      nextConjugationLawBlocker
      ≡
      missingConjugationLawForNonFlatPlaquetteHolonomy

    firstRemainingKillingBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    firstRemainingKillingBlockerIsLieAlgebraCarrier :
      firstRemainingKillingBlocker
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    nextKillingAdjointBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    nextKillingAdjointBlockerIsNontrivialAdjoint :
      nextKillingAdjointBlocker
      ≡
      missingNontrivialAdjointActionOnSelectedFieldStrength

    nextKillingPairingBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    nextKillingPairingBlockerIsPairing :
      nextKillingPairingBlocker
      ≡
      missingKillingOrTracePairingOnSelectedFieldStrength

    nextKillingAdInvarianceBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    nextKillingAdInvarianceBlockerIsAdInvariance :
      nextKillingAdInvarianceBlocker
      ≡
      missingAdInvarianceProofForThatPairing

    nonFlatCurvatureTheoremSurface :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    nonFlatCurvatureTheoremSurfaceIsCurvature :
      nonFlatCurvatureTheoremSurface
      ≡
      nonFlatCurvatureWitness sfgcCanonicalNonFlatCurvature2Form

    ledgerBoundary :
      List String

canonicalYMSFGCGate3M1NonFlatCurvatureBlockerChainLedger :
  YMSFGCGate3M1NonFlatCurvatureBlockerChainLedger
canonicalYMSFGCGate3M1NonFlatCurvatureBlockerChainLedger =
  record
    { status =
        gate3M1FirstMissingCurvatureFieldsExposedNoPromotion
    ; gate3NonFlatSFGCSite2DHandoffReceipt =
        canonicalYMSFGCGate3NonFlatSFGCSite2DHandoffReceipt
    ; gate3NonFlatSFGCSite2DHandoffReceiptIsCanonical =
        refl
    ; requestedSiteCarrier =
        SFGC.SFGCSite2D
    ; requestedSiteCarrierIsSFGCSite2D =
        refl
    ; requestedEdgeCarrier =
        SFGC.SFGCSite2DEdge
    ; requestedEdgeCarrierIsSFGCSite2DEdge =
        refl
    ; requestedPlaquetteCarrier =
        SFGC.SFGCSite2DPlaquette
    ; requestedPlaquetteCarrierIsSFGCSite2DPlaquette =
        refl
    ; requestedPlaquetteSW =
        SFGC.sfgcSite2DPlaquetteSW
    ; requestedPlaquetteSWIsSFGC =
        refl
    ; requestedPlaquetteBottomEdge =
        SFGC.sfgcSite2DPlaquetteBottomEdge
    ; requestedPlaquetteBottomEdgeIsSFGC =
        refl
    ; requestedPlaquetteRightEdge =
        SFGC.sfgcSite2DPlaquetteRightEdge
    ; requestedPlaquetteRightEdgeIsSFGC =
        refl
    ; requestedPlaquetteTopEdge =
        SFGC.sfgcSite2DPlaquetteTopEdge
    ; requestedPlaquetteTopEdgeIsSFGC =
        refl
    ; requestedPlaquetteLeftEdge =
        SFGC.sfgcSite2DPlaquetteLeftEdge
    ; requestedPlaquetteLeftEdgeIsSFGC =
        refl
    ; requestedNonFlatConnectionCarrier =
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; requestedNonFlatConnectionCarrierIsUserSupplied =
        refl
    ; requestedHolonomyCarrier =
        YMSFGCUserSuppliedHolonomyCarrier
    ; requestedHolonomyCarrierIsUserSupplied =
        refl
    ; requestedLieAlgebraCarrier =
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedLieAlgebraCarrierIsUserSupplied =
        refl
    ; requestedConnectionCurvatureFieldType =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        SFGC.SFGCSite2DPlaquette →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; requestedEndpointGaugeFactorType =
        SFGS.GaugeTransform →
        SFGC.SFGCSite2D →
        YMSFGCUserSuppliedHolonomyCarrier
    ; requestedPlaquetteHolonomyType =
        YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedPlaquetteHolonomyType
          canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; requestedConjugationLawType =
        YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedHolonomyConjugationLawType
          canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; requestedFieldStrengthToLieAlgebraType =
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DPlaquette →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedNontrivialFieldStrengthAdjointActionType =
        SFGS.GaugeTransform →
        YMSFGCUserSuppliedLieAlgebraCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requestedKillingOrTracePairingType =
        YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedKillingFormType
          canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; requestedAdInvarianceProofType =
        YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedKillingAdInvarianceLawType
          canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; firstRemainingHolonomyBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; firstRemainingHolonomyBlockerIsNonFlatCurvature =
        refl
    ; nextEndpointGaugeFactorBlocker =
        missingEndpointGaugeFactorsForPlaquetteHolonomy
    ; nextEndpointGaugeFactorBlockerIsEndpointGaugeFactors =
        refl
    ; nextFieldStrengthAdjointBlocker =
        missingNontrivialFieldStrengthAdjointAction
    ; nextFieldStrengthAdjointBlockerIsNontrivialAdjoint =
        refl
    ; nextConjugationLawBlocker =
        missingConjugationLawForNonFlatPlaquetteHolonomy
    ; nextConjugationLawBlockerIsConjugationLaw =
        refl
    ; firstRemainingKillingBlocker =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; firstRemainingKillingBlockerIsLieAlgebraCarrier =
        refl
    ; nextKillingAdjointBlocker =
        missingNontrivialAdjointActionOnSelectedFieldStrength
    ; nextKillingAdjointBlockerIsNontrivialAdjoint =
        refl
    ; nextKillingPairingBlocker =
        missingKillingOrTracePairingOnSelectedFieldStrength
    ; nextKillingPairingBlockerIsPairing =
        refl
    ; nextKillingAdInvarianceBlocker =
        missingAdInvarianceProofForThatPairing
    ; nextKillingAdInvarianceBlockerIsAdInvariance =
        refl
    ; nonFlatCurvatureTheoremSurface =
        nonFlatCurvatureWitness sfgcCanonicalNonFlatCurvature2Form
    ; nonFlatCurvatureTheoremSurfaceIsCurvature =
        refl
    ; ledgerBoundary =
        "Gate 3 m1 first remaining holonomy field is connectionCurvature : NonFlatConnection -> SFGCSite2DPlaquette -> SFGCSite2DFieldStrengthBridge"
        ∷ "SFGC endpoint geometry is exposed concretely: SW plus bottom/right/top/left plaquette edges are canonical SFGCSite2D projections"
        ∷ "Endpoint gauge factors, plaquette holonomy, and the non-flat conjugation law are staged as typed request fields after curvature"
        ∷ "The field-strength Ad action is staged through a user-supplied Lie algebra carrier, not the current trivial selected C4 action"
        ∷ "Killing/trace pairing and Ad-invariance are staged after a supplied Lie-algebra carrier for the selected finite gauge sector"
        ∷ "The exact first remaining blocker is still missingNonFlatSFGCSite2DConnectionCurvature"
        ∷ "No Route B sourced equation, Yang-Mills promotion, mass-gap, or terminal claim is asserted"
        ∷ []
    }

record SFGCPathTransportPrimitive : Set₁ where
  field
    PathOrEdge :
      Set

    pathSource :
      PathOrEdge →
      SFGC.SFGCSite2D

    pathTarget :
      PathOrEdge →
      SFGC.SFGCSite2D

    fieldStrengthTransport :
      PathOrEdge →
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    identityPath :
      SFGC.SFGCSite2D →
      PathOrEdge

    identityTransportLaw :
      (site : SFGC.SFGCSite2D) →
      (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
      fieldStrengthTransport (identityPath site) fieldStrength
      ≡
      fieldStrength

    transportGaugeCompatibilityLaw :
      SFGS.GaugeTransform →
      PathOrEdge →
      SFGC.SFGCSite2DFieldStrengthBridge →
      Set

    primitiveBoundary :
      List String

record CovariantDifferencePrimitive
  (transport : SFGCPathTransportPrimitive) : Set₁ where
  field
    CovariantDifferenceCarrier :
      Set

    zeroCovariantDifference :
      CovariantDifferenceCarrier

    covariantDifference :
      SFGC.GaugeField →
      SFGC.SFGCSite2DFieldStrengthBridge →
      CovariantDifferenceCarrier

    flatConnectionExtendsSelectedExteriorDerivative :
      (form : SFGC.SFGCSite2DDiscrete0Form) →
      Set

    covariantDifferenceGaugeCompatibilityLaw :
      SFGS.GaugeTransform →
      SFGC.GaugeField →
      SFGC.SFGCSite2DFieldStrengthBridge →
      Set

    covariantBianchiTargetLaw :
      SFGC.GaugeField →
      Set

    primitiveBoundary :
      List String

record GaugeInvariantQuadraticDensityPrimitive
  (transport : SFGCPathTransportPrimitive) : Set₁ where
  field
    DensityScalar :
      Set

    density :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DPlaquette →
      DensityScalar

    nonconstantWitness :
      Set

    gaugeInvariantDensityLaw :
      SFGS.GaugeTransform →
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DPlaquette →
      Set

    traceOrKillingPairingLaw :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DPlaquette →
      Set

    primitiveBoundary :
      List String

record DiscreteYMActionPrimitive
  (transport : SFGCPathTransportPrimitive)
  (densityPrimitive : GaugeInvariantQuadraticDensityPrimitive transport) :
  Set₁ where
  field
    ActionScalar :
      Set

    plaquetteDomain :
      Set

    plaquetteWeight :
      plaquetteDomain →
      GaugeInvariantQuadraticDensityPrimitive.DensityScalar
        densityPrimitive →
      ActionScalar

    plaquetteOf :
      plaquetteDomain →
      SFGC.SFGCSite2DPlaquette

    integrateDensity :
      SFGC.SFGCSite2DFieldStrengthBridge →
      plaquetteDomain →
      ActionScalar

    variationalPairing :
      SFGC.GaugeField →
      Set

    eulerLagrangeDStarFEqualsJTarget :
      SFGC.GaugeField →
      Set

    primitiveBoundary :
      List String

record SFGCPathTransportPrimitiveTypedRequest : Set₁ where
  field
    requestedPathOrEdgeCarrier :
      Set

    requestedPathSource :
      requestedPathOrEdgeCarrier →
      SFGC.SFGCSite2D

    requestedPathTarget :
      requestedPathOrEdgeCarrier →
      SFGC.SFGCSite2D

    requestedFieldStrengthFiber :
      SFGC.SFGCSite2D →
      Set

    requestedFieldStrengthFiberProjectionType :
      Set

    requestedParallelTransportType :
      Set

    requestedIdentityPathType :
      Set

    requestedIdentityTransportLawType :
      Set

    requestedGaugeCompatibilityLawType :
      (fieldStrengthTransport :
        requestedPathOrEdgeCarrier →
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DFieldStrengthBridge) →
      SFGS.GaugeTransform →
      (path : requestedPathOrEdgeCarrier) →
      SFGC.SFGCSite2DFieldStrengthBridge →
      Set

    typedRequestBoundary :
      List String

canonicalSFGCPathTransportPrimitiveTypedRequest :
  SFGCPathTransportPrimitiveTypedRequest
canonicalSFGCPathTransportPrimitiveTypedRequest =
  record
    { requestedPathOrEdgeCarrier =
        SFGC.SFGCSite2DEdge
    ; requestedPathSource =
        SFGC.sfgcSite2DEdgeSourceTotal
    ; requestedPathTarget =
        SFGC.sfgcSite2DEdgeTargetTotal
    ; requestedFieldStrengthFiber =
        λ site → SFGC.SFGCSite2DFieldStrengthBridge
    ; requestedFieldStrengthFiberProjectionType =
        (site : SFGC.SFGCSite2D) →
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; requestedParallelTransportType =
        (edge : SFGC.SFGCSite2DEdge) →
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; requestedIdentityPathType =
        SFGC.SFGCSite2D →
        SFGC.SFGCSite2DEdge
    ; requestedIdentityTransportLawType =
        (fieldStrengthTransport :
          SFGC.SFGCSite2DEdge →
          SFGC.SFGCSite2DFieldStrengthBridge →
          SFGC.SFGCSite2DFieldStrengthBridge) →
        (identityPath :
          SFGC.SFGCSite2D →
          SFGC.SFGCSite2DEdge) →
        (site : SFGC.SFGCSite2D) →
        (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
        fieldStrengthTransport (identityPath site) fieldStrength
          ≡
        fieldStrength
    ; requestedGaugeCompatibilityLawType =
        λ fieldStrengthTransport gauge edge fieldStrength →
          SFGC.SFGCSite2DFieldStrengthBridge.curvature2Form
            (fieldStrengthTransport edge fieldStrength)
          ≡
          SFGC.SFGCSite2DFieldStrengthBridge.curvature2Form
            fieldStrength
    ; typedRequestBoundary =
        "Concrete local carrier: SFGCSite2DEdge with exported source and target maps"
        ∷ "Implemented local primitive: identityPath : SFGCSite2D -> SFGCSite2DEdge via SFGC.sfgcSite2DIdentityEdgeAt"
        ∷ "Implemented local law: identityPathTargetLaw by SFGC.sfgcSite2DIdentityEdgeTargetLaw"
        ∷ "Implemented lower candidate: identity edges preserve the bridge and oriented edges re-probe the target plaquette"
        ∷ "Missing typed primitive: supplied field-strength fiber/link action proving this is parallel transport along SFGCSite2DEdge"
        ∷ "Missing typed primitive: gauge-compatibility law for that transport"
        ∷ []
    }

record CovariantDifferencePrimitiveTypedRequest
  (transportRequest : SFGCPathTransportPrimitiveTypedRequest) : Set₁ where
  field
    requestedCovariantDifferenceCarrier :
      Set

    requestedZeroCovariantDifferenceType :
      Set

    requestedCovariantDifferenceType :
      Set

    requestedFlatConnectionExtensionLawType :
      (flatCovariantDerivative0 :
        SFGC.SFGCSite2DDiscrete0Form →
        SFGC.SFGCSite2DDiscrete1Form) →
      SFGC.SFGCSite2DDiscrete0Form →
      Set

    requestedGaugeCompatibilityLawType :
      (covariantDifference :
        SFGC.GaugeField →
        SFGC.SFGCSite2DFieldStrengthBridge →
        requestedCovariantDifferenceCarrier) →
      SFGS.GaugeTransform →
      SFGC.GaugeField →
      SFGC.SFGCSite2DFieldStrengthBridge →
      Set

    requestedBianchiTargetLawType :
      (covariantDifference :
        SFGC.GaugeField →
        SFGC.SFGCSite2DFieldStrengthBridge →
        requestedCovariantDifferenceCarrier) →
      SFGC.GaugeField →
      Set

    typedRequestBoundary :
      List String

canonicalCovariantDifferencePrimitiveTypedRequest :
  CovariantDifferencePrimitiveTypedRequest
    canonicalSFGCPathTransportPrimitiveTypedRequest
canonicalCovariantDifferencePrimitiveTypedRequest =
  record
    { requestedCovariantDifferenceCarrier =
        SFGC.SFGCSite2DFieldStrengthBridge
    ; requestedZeroCovariantDifferenceType =
        SFGC.SFGCSite2DFieldStrengthBridge
    ; requestedCovariantDifferenceType =
        SFGC.GaugeField →
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; requestedFlatConnectionExtensionLawType =
        λ flatCovariantDerivative0 form →
          flatCovariantDerivative0 form
          ≡
          SFGC.sfgcSite2Dδ₀ form
    ; requestedGaugeCompatibilityLawType =
        λ covariantDifference gauge A fieldStrength →
          covariantDifference (SFGC.transformGauge gauge A) fieldStrength
          ≡
          covariantDifference A fieldStrength
    ; requestedBianchiTargetLawType =
        λ covariantDifference A →
          covariantDifference A
            (SFGC.sfgcSite2DFieldStrengthFromCurvature
              SFGC.sfgcSite2DZero2Form)
          ≡
          SFGC.sfgcSite2DFieldStrengthFromCurvature
            SFGC.sfgcSite2DZero2Form
    ; typedRequestBoundary =
        "Narrowed request: D_A should act on the selected SFGCSite2DFieldStrengthBridge carrier"
        ∷ "Missing typed primitive: zero covariant difference and a covariantDifference operation using path transport"
        ∷ "Missing typed primitive: flat-connection extension law relating D_A to SFGC.sfgcSite2Dδ0"
        ∷ "Missing typed primitive: gauge-compatibility and Bianchi target laws for the selected covariant difference"
        ∷ []
    }

record GaugeInvariantQuadraticDensityPrimitiveTypedRequest : Set₁ where
  field
    requestedDensityScalar :
      Set

    requestedDensityType :
      Set

    requestedNonconstantWitnessType :
      (density :
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DPlaquette →
        requestedDensityScalar) →
      Set

    requestedGaugeInvariantDensityLawType :
      (density :
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DPlaquette →
        requestedDensityScalar) →
      SFGS.GaugeTransform →
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DPlaquette →
      Set

    requestedTraceOrKillingPairingLawType :
      (density :
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DPlaquette →
        requestedDensityScalar) →
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DPlaquette →
      Set

    typedRequestBoundary :
      List String

canonicalGaugeInvariantQuadraticDensityPrimitiveTypedRequest :
  GaugeInvariantQuadraticDensityPrimitiveTypedRequest
canonicalGaugeInvariantQuadraticDensityPrimitiveTypedRequest =
  record
    { requestedDensityScalar =
        ℤ
    ; requestedDensityType =
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DPlaquette →
        ℤ
    ; requestedNonconstantWitnessType =
        λ density → ℤ
    ; requestedGaugeInvariantDensityLawType =
        λ density gauge fieldStrength plaquette →
          density fieldStrength plaquette
          ≡
          density fieldStrength plaquette
    ; requestedTraceOrKillingPairingLawType =
        λ density fieldStrength plaquette →
          density fieldStrength plaquette
          ≡
          density fieldStrength plaquette
    ; typedRequestBoundary =
        "Narrowed request: an integer-valued density on selected field-strength bridge plaquette values"
        ∷ "Available proxy phaseKernel4 is constant on diagonal inputs, so it does not satisfy this nonconstant density request"
        ∷ "Missing typed primitive: gauge-invariant trace or Killing pairing for the selected finite field-strength algebra"
        ∷ []
    }

record DiscreteYMActionPrimitiveTypedRequest
  (densityRequest : GaugeInvariantQuadraticDensityPrimitiveTypedRequest) :
  Set₁ where
  field
    requestedActionScalar :
      Set

    requestedPlaquetteDomain :
      Set

    requestedPlaquetteOfType :
      Set

    requestedPlaquetteWeightType :
      Set

    requestedIntegrateDensityType :
      Set

    requestedVariationalPairingType :
      SFGC.GaugeField →
      Set

    requestedEulerLagrangeDStarFEqualsJTargetType :
      SFGC.GaugeField →
      Set

    typedRequestBoundary :
      List String

canonicalDiscreteYMActionPrimitiveTypedRequest :
  DiscreteYMActionPrimitiveTypedRequest
    canonicalGaugeInvariantQuadraticDensityPrimitiveTypedRequest
canonicalDiscreteYMActionPrimitiveTypedRequest =
  record
    { requestedActionScalar =
        ℤ
    ; requestedPlaquetteDomain =
        SFGC.SFGCSite2DPlaquette
    ; requestedPlaquetteOfType =
        SFGC.SFGCSite2DPlaquette →
        SFGC.SFGCSite2DPlaquette
    ; requestedPlaquetteWeightType =
        SFGC.SFGCSite2DPlaquette →
        ℤ →
        ℤ
    ; requestedIntegrateDensityType =
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DPlaquette →
        ℤ
    ; requestedVariationalPairingType =
        λ A → SFGC.GaugeField
    ; requestedEulerLagrangeDStarFEqualsJTargetType =
        λ A → YangMillsVariationalEquationMissingPrimitive
    ; typedRequestBoundary =
        "Narrowed request: plaquette-domain action over SFGCSite2DPlaquette with integer action scalar"
        ∷ "Missing typed primitive: real plaquette sum/integration functional rather than single-plaquette proxy evaluation"
        ∷ "Missing typed primitive: variational pairing for GaugeField variations"
        ∷ "Missing typed primitive: Euler-Lagrange target deriving D * F = J from that action"
        ∷ []
    }

record YMSFGCPrimitiveInterfaceRequest : Set₁ where
  field
    typedPathTransportPrimitiveRequest :
      SFGCPathTransportPrimitiveTypedRequest

    typedCovariantDifferencePrimitiveRequest :
      CovariantDifferencePrimitiveTypedRequest
        typedPathTransportPrimitiveRequest

    typedGaugeInvariantQuadraticDensityPrimitiveRequest :
      GaugeInvariantQuadraticDensityPrimitiveTypedRequest

    typedDiscreteYMActionPrimitiveRequest :
      DiscreteYMActionPrimitiveTypedRequest
        typedGaugeInvariantQuadraticDensityPrimitiveRequest

    typedDiscreteHodgeCovariantDerivativePrimitiveRequest :
      DiscreteHodgeCovariantDerivativePrimitiveTypedRequest

    typedNonAbelianCovariantDerivativePrimitiveRequest :
      YMSFGCNonAbelianCovariantDerivativeTypedRequest

    nonAbelianCovariantDerivativeTheoremThinReceipt :
      YMSFGCNonAbelianCovariantDerivativeTheoremThinReceipt

    requestedPathTransportPrimitive :
      String

    requestedCovariantDifferencePrimitive :
      String

    requestedNonAbelianCovariantDerivativePrimitive :
      String

    requestedGaugeInvariantQuadraticDensityPrimitive :
      String

    requestedDiscreteYMActionPrimitive :
      String

    requestedDiscreteHodgeCovariantDerivativePrimitive :
      String

    requestBoundary :
      List String

canonicalYMSFGCPrimitiveInterfaceRequest :
  YMSFGCPrimitiveInterfaceRequest
canonicalYMSFGCPrimitiveInterfaceRequest =
  record
    { typedPathTransportPrimitiveRequest =
        canonicalSFGCPathTransportPrimitiveTypedRequest
    ; typedCovariantDifferencePrimitiveRequest =
        canonicalCovariantDifferencePrimitiveTypedRequest
    ; typedGaugeInvariantQuadraticDensityPrimitiveRequest =
        canonicalGaugeInvariantQuadraticDensityPrimitiveTypedRequest
    ; typedDiscreteYMActionPrimitiveRequest =
        canonicalDiscreteYMActionPrimitiveTypedRequest
    ; typedDiscreteHodgeCovariantDerivativePrimitiveRequest =
        canonicalDiscreteHodgeCovariantDerivativePrimitiveTypedRequest
    ; typedNonAbelianCovariantDerivativePrimitiveRequest =
        canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest
    ; nonAbelianCovariantDerivativeTheoremThinReceipt =
        canonicalYMSFGCNonAbelianCovariantDerivativeTheoremThinReceipt
    ; requestedPathTransportPrimitive =
        "SFGCPathTransportPrimitive: real PathOrEdge carrier with source/target, identity transport, field-strength transport, and gauge-compatibility law"
    ; requestedCovariantDifferencePrimitive =
        "CovariantDifferencePrimitive: D_A on SFGCSite2DFieldStrengthBridge using path transport, with flat-extension and gauge-compatibility laws"
    ; requestedNonAbelianCovariantDerivativePrimitive =
        "NonAbelianCovariantDerivativePrimitive: fibre Lie bracket, Jacobi witness, D_A = d + [A,_], and D_A^2(s) = [F_A,s]"
    ; requestedGaugeInvariantQuadraticDensityPrimitive =
        "GaugeInvariantQuadraticDensityPrimitive: nonconstant trace/Killing-style density on SFGCSite2DFieldStrengthBridge plaquette values"
    ; requestedDiscreteYMActionPrimitive =
        "DiscreteYMActionPrimitive: plaquette domain, integration/sum functional, variational pairing, and Euler-Lagrange D * F = J target"
    ; requestedDiscreteHodgeCovariantDerivativePrimitive =
        "DiscreteHodgeCovariantDerivativePrimitive: Hodge star on selected curvature, covariant derivative on dual curvature, current carrier, D * F = J target, and covariant Bianchi target"
    ; requestBoundary =
        "Typed requests now reuse concrete SFGCSite2DEdge source/target and SFGCSite2DPlaquette carriers where available"
        ∷ "The remaining absent fields are supplied field-strength fiber transport, covariant-difference laws, SFGC representation into the local finite Lie carrier, physical D_A laws, nonconstant Killing density, plaquette integration, Hodge star, dual covariant derivative, current coupling, and variation pairing"
        ∷ "These are interface records plus lower candidates only; no local SFGC/G2 API currently promotes the requested real primitive records"
        ∷ "They narrow the remaining primitives below the existing selected curvature and field-strength bridge"
        ∷ "They do not assert D * F = J, D F = 0, or any promotion flag"
        ∷ []
    }

canonicalYMSFGCNondegeneratePlaquetteAPI :
  G2NP.RequiredNondegenerateSFGCPlaquetteAPI SFGC.GaugeField
canonicalYMSFGCNondegeneratePlaquetteAPI =
  record
    { Site =
        SFGC.SFGCSite2D
    ; Direction =
        SFGC.SFGCPrimeDirection
    ; rightDirection =
        SFGC.p2Right
    ; transverseDirection =
        SFGC.p3Transverse
    ; independentDirections =
        SFGC.p2Right≠p3Transverse
    ; Edge =
        SFGC.SFGCSite2DEdge
    ; edgeAt =
        SFGC.sfgcSite2DEdgeAt
    ; edgeSource =
        SFGC.sfgcSite2DEdgeSourceTotal
    ; edgeTarget =
        SFGC.sfgcSite2DEdgeTargetTotal
    ; edgeSourceLaw =
        SFGC.sfgcSite2DEdgeAtSourceLaw
    ; shiftAction =
        SFGC.sfgcSite2DShiftAction
    ; edgeTargetLaw =
        SFGC.sfgcSite2DEdgeAtTargetLaw
    ; Plaquette =
        SFGC.SFGCSite2DPlaquette
    ; plaquetteAt =
        SFGC.sfgcSite2DPlaquetteAt
    ; southwest =
        SFGC.sfgcSite2DPlaquetteSW
    ; southeast =
        SFGC.sfgcSite2DPlaquetteSE
    ; northeast =
        SFGC.sfgcSite2DPlaquetteNE
    ; northwest =
        SFGC.sfgcSite2DPlaquetteNW
    ; bottomEdge =
        SFGC.sfgcSite2DPlaquetteBottomEdge
    ; rightEdge =
        SFGC.sfgcSite2DPlaquetteRightEdge
    ; topEdge =
        SFGC.sfgcSite2DPlaquetteTopEdge
    ; leftEdge =
        SFGC.sfgcSite2DPlaquetteLeftEdge
    ; bottomSourceLaw =
        SFGC.sfgcSite2DPlaquetteBottomSourceLaw
    ; bottomTargetLaw =
        SFGC.sfgcSite2DPlaquetteBottomTargetLaw
    ; rightSourceLaw =
        SFGC.sfgcSite2DPlaquetteRightSourceLaw
    ; rightTargetLaw =
        SFGC.sfgcSite2DPlaquetteRightTargetLaw
    ; topSourceLaw =
        SFGC.sfgcSite2DPlaquetteTopSourceLaw
    ; topTargetLaw =
        SFGC.sfgcSite2DPlaquetteTopTargetLaw
    ; leftSourceLaw =
        SFGC.sfgcSite2DPlaquetteLeftSourceLaw
    ; leftTargetLaw =
        SFGC.sfgcSite2DPlaquetteLeftTargetLaw
    ; plaquetteCommutes =
        SFGC.sfgcSite2DP2P3EndpointCommutation
    ; signedPlaquetteBoundary =
        λ plaquette →
          G2DCC.correctedSquareBoundary
            (SFGC.sfgcSite2DPlaquetteBottomEdge plaquette)
            (SFGC.sfgcSite2DPlaquetteRightEdge plaquette)
            (SFGC.sfgcSite2DPlaquetteTopEdge plaquette)
            (SFGC.sfgcSite2DPlaquetteLeftEdge plaquette)
    ; signedPlaquetteBoundaryIsCorrectedSquare =
        λ base → refl
    ; Discrete0Form =
        SFGC.SFGCSite2DDiscrete0Form
    ; Discrete1Form =
        SFGC.SFGCSite2DDiscrete1Form
    ; Discrete2Form =
        SFGC.SFGCSite2DDiscrete2Form
    ; connectionTo1Form =
        SFGC.sfgcSite2DConnectionTo1Form
    ; evaluate1 =
        SFGC.sfgcSite2DEvaluate1
    ; evaluate2 =
        SFGC.sfgcSite2DEvaluate2
    ; δ₀ =
        SFGC.sfgcSite2Dδ₀
    ; δ₁ =
        SFGC.sfgcSite2Dδ₁
    ; boundaryOfBoundaryZero =
        SFGC.sfgcSite2DP2P3BoundaryOfBoundaryZero
    ; vacuumConnection =
        SFGC.vacuumGaugeField
    ; vacuumFlatness =
        SFGC.sfgcSite2DVacuumWilsonLoopFlatness
    ; FieldStrengthCarrier =
        SFGC.SFGCSite2DFieldStrengthBridge
    ; fieldStrengthFromCurvature =
        SFGC.sfgcSite2DFieldStrengthFromCurvature
    ; schemaBoundary =
        "YM-local inhabitant: SFGCSite2D supplies independent p2/right and p3/transverse axes"
        ∷ "connectionTo1Form is SFGC.sfgcSite2DConnectionTo1Form over SFGC.GaugeField"
        ∷ "δ1 of the connection is Wilson-loop curvature on the nondegenerate p2/p3 plaquette"
        ∷ "boundaryOfBoundaryZero and vacuum flatness are inherited from the SFGC 2D sidecar"
        ∷ "This supplies a curvature carrier only; it is not a Yang-Mills equation or closure proof"
        ∷ []
    }

canonicalYMSFGCDiscreteCurvatureCarrier :
  G2DCC.DiscreteCurvatureCarrier SFGC.GaugeField
canonicalYMSFGCDiscreteCurvatureCarrier =
  G2NP.discreteCurvatureCarrierFromRequiredNondegenerateSFGCPlaquetteAPI
    canonicalYMSFGCNondegeneratePlaquetteAPI

record YMSFGCSelectedExteriorDerivativeSquaredZeroWitness : Set where
  field
    selectedDiscreteExteriorDerivative0 :
      SFGC.SFGCSite2DDiscrete0Form →
      SFGC.SFGCSite2DDiscrete1Form

    selectedDiscreteExteriorDerivative0IsSFGC :
      selectedDiscreteExteriorDerivative0
      ≡
      SFGC.sfgcSite2Dδ₀

    selectedDiscreteExteriorDerivative1 :
      SFGC.SFGCSite2DDiscrete1Form →
      SFGC.SFGCSite2DDiscrete2Form

    selectedDiscreteExteriorDerivative1IsSFGC :
      selectedDiscreteExteriorDerivative1
      ≡
      SFGC.sfgcSite2Dδ₁

    selectedExteriorDerivativeSquaredZeroOnPlaquetteEvaluation :
      (f : SFGC.SFGCSite2DDiscrete0Form) →
      (base : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEvaluate2
        (selectedDiscreteExteriorDerivative1
          (selectedDiscreteExteriorDerivative0 f))
        (SFGC.sfgcSite2DPlaquetteAt base)
      ≡
      SFGC.sfgcSite2DEvaluate2
        SFGC.sfgcSite2DZero2Form
        (SFGC.sfgcSite2DPlaquetteAt base)

    witnessBoundary :
      List String

canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness :
  YMSFGCSelectedExteriorDerivativeSquaredZeroWitness
canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness =
  record
    { selectedDiscreteExteriorDerivative0 =
        SFGC.sfgcSite2Dδ₀
    ; selectedDiscreteExteriorDerivative0IsSFGC =
        refl
    ; selectedDiscreteExteriorDerivative1 =
        SFGC.sfgcSite2Dδ₁
    ; selectedDiscreteExteriorDerivative1IsSFGC =
        refl
    ; selectedExteriorDerivativeSquaredZeroOnPlaquetteEvaluation =
        SFGC.sfgcSite2DP2P3BoundaryOfBoundaryZero
    ; witnessBoundary =
        "Wired honestly: SFGC.sfgcSite2DP2P3BoundaryOfBoundaryZero proves selected δ1(δ0 f) vanishes on the p2/p3 plaquette evaluation"
        ∷ "This is exterior nilpotency for the selected SFGCSite2D cochain surface, not a covariant Yang-Mills Bianchi proof"
        ∷ "The remaining Bianchi work is transport from this exterior law to the selected covariant derivative and field-strength carrier"
        ∷ []
    }

sfgcFlatPlaquetteStokesSupportFromSelectedExteriorWitness :
  (f : SFGC.SFGCSite2DDiscrete0Form) →
  (base : SFGC.SFGCSite2D) →
  SFGC.sfgcSite2DEvaluate2
    (SFGC.sfgcSite2Dδ₁
      (SFGC.sfgcSite2Dδ₀ f))
    (SFGC.sfgcSite2DPlaquetteAt base)
  ≡
  SFGC.sfgcSite2DEvaluate2
    SFGC.sfgcSite2DZero2Form
    (SFGC.sfgcSite2DPlaquetteAt base)
sfgcFlatPlaquetteStokesSupportFromSelectedExteriorWitness =
  YMSFGCSelectedExteriorDerivativeSquaredZeroWitness.selectedExteriorDerivativeSquaredZeroOnPlaquetteEvaluation
    canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness

sfgcFlatPlaquetteJacobiSupportRepresentative458 :
  localFiniteSU3PositiveAxisJacobiResidual
    su3Axis4
    su3Axis5
    su3Axis8
  ≡
  su3Zero
sfgcFlatPlaquetteJacobiSupportRepresentative458 =
  localFiniteSU3Representative458JacobiResidualIsZero

sfgcSelectedCurvature2Form :
  SFGC.GaugeField →
  SFGC.SFGCSite2DDiscrete2Form
sfgcSelectedCurvature2Form A =
  SFGC.sfgcSite2Dδ₁ (SFGC.sfgcSite2DConnectionTo1Form A)

sfgcSelectedFieldStrengthBridge :
  SFGC.GaugeField →
  SFGC.SFGCSite2DFieldStrengthBridge
sfgcSelectedFieldStrengthBridge A =
  SFGC.sfgcSite2DFieldStrengthFromCurvature
    (sfgcSelectedCurvature2Form A)

phase4SquareBoundaryCancel :
  (bottom right : SPTI4.Phase4) →
  SFGS.phaseAdd4
    (SFGS.phaseAdd4
      (SFGS.phaseAdd4 bottom right)
      (SFGS.phaseInv4 bottom))
    (SFGS.phaseInv4 right)
  ≡
  SPTI4.φ0
phase4SquareBoundaryCancel SPTI4.φ0 SPTI4.φ0 = refl
phase4SquareBoundaryCancel SPTI4.φ0 SPTI4.φ1 = refl
phase4SquareBoundaryCancel SPTI4.φ0 SPTI4.φ2 = refl
phase4SquareBoundaryCancel SPTI4.φ0 SPTI4.φ3 = refl
phase4SquareBoundaryCancel SPTI4.φ1 SPTI4.φ0 = refl
phase4SquareBoundaryCancel SPTI4.φ1 SPTI4.φ1 = refl
phase4SquareBoundaryCancel SPTI4.φ1 SPTI4.φ2 = refl
phase4SquareBoundaryCancel SPTI4.φ1 SPTI4.φ3 = refl
phase4SquareBoundaryCancel SPTI4.φ2 SPTI4.φ0 = refl
phase4SquareBoundaryCancel SPTI4.φ2 SPTI4.φ1 = refl
phase4SquareBoundaryCancel SPTI4.φ2 SPTI4.φ2 = refl
phase4SquareBoundaryCancel SPTI4.φ2 SPTI4.φ3 = refl
phase4SquareBoundaryCancel SPTI4.φ3 SPTI4.φ0 = refl
phase4SquareBoundaryCancel SPTI4.φ3 SPTI4.φ1 = refl
phase4SquareBoundaryCancel SPTI4.φ3 SPTI4.φ2 = refl
phase4SquareBoundaryCancel SPTI4.φ3 SPTI4.φ3 = refl

sfgcSelectedWilsonLoopPhaseZero :
  (A : SFGC.GaugeField) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    (sfgcSelectedFieldStrengthBridge A)
    plaquette
  ≡
  SPTI4.φ0
sfgcSelectedWilsonLoopPhaseZero
  A
  (SFGC.sfgcSite2DPlaquetteAt (SFGC.sfgcSite2D p2 p3)) =
  phase4SquareBoundaryCancel (A p2) (A p3)

sfgcSelectedFieldStrengthAdjointTransportCandidate :
  SFGS.GaugeTransform →
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2DFieldStrengthBridge
sfgcSelectedFieldStrengthAdjointTransportCandidate gauge fieldStrength =
  fieldStrength

sfgcSelectedFieldStrengthAdjointTransportCandidatePlaquetteLaw :
  (gauge : SFGS.GaugeTransform) →
  (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    (sfgcSelectedFieldStrengthAdjointTransportCandidate gauge fieldStrength)
    plaquette
    ≡
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    fieldStrength
    plaquette
sfgcSelectedFieldStrengthAdjointTransportCandidatePlaquetteLaw
  gauge fieldStrength plaquette =
  refl

sfgcSelectedFlatConnectionExteriorExtensionCandidate :
  SFGC.SFGCSite2DDiscrete0Form →
  SFGC.SFGCSite2DDiscrete1Form
sfgcSelectedFlatConnectionExteriorExtensionCandidate =
  SFGC.sfgcSite2Dδ₀

sfgcSelectedFlatConnectionExteriorExtensionCandidateLaw :
  (form : SFGC.SFGCSite2DDiscrete0Form) →
  sfgcSelectedFlatConnectionExteriorExtensionCandidate form
    ≡
  SFGC.sfgcSite2Dδ₀ form
sfgcSelectedFlatConnectionExteriorExtensionCandidateLaw form =
  refl

sfgcPhase4QuadraticKernelProxy :
  SPTI4.Phase4 →
  ℤ
sfgcPhase4QuadraticKernelProxy phase =
  SPTI4.phaseKernel4 phase phase

sfgcPhase4QuadraticKernelProxyIsSamePhaseKernel :
  (phase : SPTI4.Phase4) →
  sfgcPhase4QuadraticKernelProxy phase
    ≡
  + 1
sfgcPhase4QuadraticKernelProxyIsSamePhaseKernel =
  SPTI4.samePhaseConstructiveKernel

sfgcSelectedCurvatureQuadraticDensityProxy :
  SFGC.SFGCSite2DDiscrete2Form →
  SFGC.SFGCSite2DPlaquette →
  ℤ
sfgcSelectedCurvatureQuadraticDensityProxy curvature plaquette =
  sfgcPhase4QuadraticKernelProxy
    (SFGC.sfgcSite2DEvaluate2 curvature plaquette)

sfgcSelectedCurvatureQuadraticDensityProxyIsPhaseKernel :
  (curvature : SFGC.SFGCSite2DDiscrete2Form) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  sfgcSelectedCurvatureQuadraticDensityProxy curvature plaquette
    ≡
  SPTI4.phaseKernel4
    (SFGC.sfgcSite2DEvaluate2 curvature plaquette)
    (SFGC.sfgcSite2DEvaluate2 curvature plaquette)
sfgcSelectedCurvatureQuadraticDensityProxyIsPhaseKernel
  curvature plaquette =
  refl

sfgcIdentityEdgeCandidate :
  SFGC.SFGCSite2D →
  SFGC.SFGCSite2DEdge
sfgcIdentityEdgeCandidate =
  SFGC.sfgcSite2DIdentityEdgeAt

sfgcIdentityPathTargetLaw :
  (site : SFGC.SFGCSite2D) →
  SFGC.sfgcSite2DEdgeTargetTotal (sfgcIdentityEdgeCandidate site)
    ≡
  site
sfgcIdentityPathTargetLaw =
  SFGC.sfgcSite2DIdentityEdgeTargetLaw

sfgcIdentityFieldStrengthTransportCandidate :
  SFGC.SFGCSite2DEdge →
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2DFieldStrengthBridge
sfgcIdentityFieldStrengthTransportCandidate edge fieldStrength =
  fieldStrength

sfgcFieldStrengthProbePhaseAtSite :
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2D →
  SPTI4.Phase4
sfgcFieldStrengthProbePhaseAtSite fieldStrength site =
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    fieldStrength
    (SFGC.sfgcSite2DPlaquetteAt site)

sfgcFieldStrengthProbeBridgeAtSite :
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2D →
  SFGC.SFGCSite2DFieldStrengthBridge
sfgcFieldStrengthProbeBridgeAtSite fieldStrength site =
  SFGC.sfgcSite2DFieldStrengthFromCurvature
    (SFGC.sfgcSite2DArbitrary2Form
      (λ plaquette →
        sfgcFieldStrengthProbePhaseAtSite fieldStrength site))

sfgcEdgeFieldStrengthTransportCandidate :
  SFGC.SFGCSite2DEdge →
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2DFieldStrengthBridge
sfgcEdgeFieldStrengthTransportCandidate
  (SFGC.sfgcSite2DIdentityEdge site)
  fieldStrength =
  fieldStrength
sfgcEdgeFieldStrengthTransportCandidate
  (SFGC.sfgcSite2DOrientedEdge dir site edge)
  fieldStrength =
  sfgcFieldStrengthProbeBridgeAtSite
    fieldStrength
    (SFGC.sfgcSite2DEdgeTarget edge)

sfgcEdgeFieldStrengthTransportIdentityLaw :
  (site : SFGC.SFGCSite2D) →
  (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
  sfgcEdgeFieldStrengthTransportCandidate
    (sfgcIdentityEdgeCandidate site)
    fieldStrength
    ≡
  fieldStrength
sfgcEdgeFieldStrengthTransportIdentityLaw site fieldStrength =
  refl

sfgcEdgeFieldStrengthTransportTargetProbeLaw :
  (dir : SFGC.SFGCPrimeDirection) →
  (site : SFGC.SFGCSite2D) →
  (edge : SFGC.SFGCSite2DShiftEdge dir site) →
  (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    (sfgcEdgeFieldStrengthTransportCandidate
      (SFGC.sfgcSite2DOrientedEdge dir site edge)
      fieldStrength)
    plaquette
    ≡
  sfgcFieldStrengthProbePhaseAtSite
    fieldStrength
    (SFGC.sfgcSite2DEdgeTarget edge)
sfgcEdgeFieldStrengthTransportTargetProbeLaw
  dir site edge fieldStrength plaquette =
  refl

record SFGCSuppliedLinkFibreFieldStrengthTransportInterface : Set₁ where
  field
    LinkOrEdge :
      Set

    linkSource :
      LinkOrEdge →
      SFGC.SFGCSite2D

    linkTarget :
      LinkOrEdge →
      SFGC.SFGCSite2D

    FieldStrengthFibre :
      SFGC.SFGCSite2D →
      Set

    lowerToBridge :
      {site : SFGC.SFGCSite2D} →
      FieldStrengthFibre site →
      SFGC.SFGCSite2DFieldStrengthBridge

    bridgeToFibre :
      (site : SFGC.SFGCSite2D) →
      SFGC.SFGCSite2DFieldStrengthBridge →
      FieldStrengthFibre site

    linkFibreTransport :
      (link : LinkOrEdge) →
      FieldStrengthFibre (linkSource link) →
      FieldStrengthFibre (linkTarget link)

    identityLink :
      SFGC.SFGCSite2D →
      LinkOrEdge

    identityLinkSourceLaw :
      (site : SFGC.SFGCSite2D) →
      linkSource (identityLink site)
      ≡
      site

    identityLinkTargetLaw :
      (site : SFGC.SFGCSite2D) →
      linkTarget (identityLink site)
      ≡
      site

    identityLinkTransportLaw :
      (site : SFGC.SFGCSite2D) →
      (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
      lowerToBridge
        (linkFibreTransport
          (identityLink site)
          (bridgeToFibre (linkSource (identityLink site)) fieldStrength))
      ≡
      fieldStrength

    transportGaugeCompatibilityLaw :
      SFGS.GaugeTransform →
      LinkOrEdge →
      SFGC.SFGCSite2DFieldStrengthBridge →
      Set

    suppliedInterfaceBoundary :
      List String

compileSuppliedLinkFibreFieldStrengthTransport :
  SFGCSuppliedLinkFibreFieldStrengthTransportInterface →
  SFGCPathTransportPrimitive
compileSuppliedLinkFibreFieldStrengthTransport supplied =
  record
    { PathOrEdge =
        SFGCSuppliedLinkFibreFieldStrengthTransportInterface.LinkOrEdge
          supplied
    ; pathSource =
        SFGCSuppliedLinkFibreFieldStrengthTransportInterface.linkSource
          supplied
    ; pathTarget =
        SFGCSuppliedLinkFibreFieldStrengthTransportInterface.linkTarget
          supplied
    ; fieldStrengthTransport =
        λ link fieldStrength →
          SFGCSuppliedLinkFibreFieldStrengthTransportInterface.lowerToBridge
            supplied
            (SFGCSuppliedLinkFibreFieldStrengthTransportInterface.linkFibreTransport
              supplied
              link
              (SFGCSuppliedLinkFibreFieldStrengthTransportInterface.bridgeToFibre
                supplied
                (SFGCSuppliedLinkFibreFieldStrengthTransportInterface.linkSource
                  supplied link)
                fieldStrength))
    ; identityPath =
        SFGCSuppliedLinkFibreFieldStrengthTransportInterface.identityLink
          supplied
    ; identityTransportLaw =
        SFGCSuppliedLinkFibreFieldStrengthTransportInterface.identityLinkTransportLaw
          supplied
    ; transportGaugeCompatibilityLaw =
        SFGCSuppliedLinkFibreFieldStrengthTransportInterface.transportGaugeCompatibilityLaw
          supplied
    ; primitiveBoundary =
        SFGCSuppliedLinkFibreFieldStrengthTransportInterface.suppliedInterfaceBoundary
          supplied
    }

canonicalYMSFGCSuppliedEdgeProbeFieldStrengthTransportInterface :
  SFGCSuppliedLinkFibreFieldStrengthTransportInterface
canonicalYMSFGCSuppliedEdgeProbeFieldStrengthTransportInterface =
  record
    { LinkOrEdge =
        SFGC.SFGCSite2DEdge
    ; linkSource =
        SFGC.sfgcSite2DEdgeSourceTotal
    ; linkTarget =
        SFGC.sfgcSite2DEdgeTargetTotal
    ; FieldStrengthFibre =
        λ site → SFGC.SFGCSite2DFieldStrengthBridge
    ; lowerToBridge =
        λ {site} fieldStrength → fieldStrength
    ; bridgeToFibre =
        λ site fieldStrength → fieldStrength
    ; linkFibreTransport =
        sfgcEdgeFieldStrengthTransportCandidate
    ; identityLink =
        sfgcIdentityEdgeCandidate
    ; identityLinkSourceLaw =
        SFGC.sfgcSite2DIdentityEdgeSourceLaw
    ; identityLinkTargetLaw =
        sfgcIdentityPathTargetLaw
    ; identityLinkTransportLaw =
        sfgcEdgeFieldStrengthTransportIdentityLaw
    ; transportGaugeCompatibilityLaw =
        λ gauge edge fieldStrength →
          SFGC.SFGCSite2DFieldStrengthBridge.curvature2Form
            (sfgcEdgeFieldStrengthTransportCandidate edge fieldStrength)
          ≡
          SFGC.SFGCSite2DFieldStrengthBridge.curvature2Form fieldStrength
    ; suppliedInterfaceBoundary =
        "Supplied lower interface: LinkOrEdge is SFGCSite2DEdge and every fibre is the selected SFGCSite2DFieldStrengthBridge carrier"
        ∷ "The compiler lowers fibre transport into SFGCPathTransportPrimitive.fieldStrengthTransport"
        ∷ "The current supplied transport is still the edge-target probe: identity edges return the bridge, oriented edges re-probe the target plaquette"
        ∷ "Gauge compatibility is retained as a law surface because the local gauge API has no field-strength fibre action or covariance proof"
        ∷ "This interface/compiler is non-promoting and does not construct a Yang-Mills covariant derivative"
        ∷ []
    }

sfgcReferenceTransportEdgeFromPhase :
  SPTI4.Phase4 →
  SFGC.SFGCSite2DEdge
sfgcReferenceTransportEdgeFromPhase SPTI4.φ0 =
  SFGC.sfgcSite2DIdentityEdgeAt
    (SFGC.sfgcSite2D SPTI.shiftStartPoint SPTI.shiftStartPoint)
sfgcReferenceTransportEdgeFromPhase SPTI4.φ1 =
  SFGC.sfgcSite2DEdgeAt
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftStartPoint SPTI.shiftStartPoint)
sfgcReferenceTransportEdgeFromPhase SPTI4.φ2 =
  SFGC.sfgcSite2DEdgeAt
    SFGC.p3Transverse
    (SFGC.sfgcSite2D SPTI.shiftStartPoint SPTI.shiftStartPoint)
sfgcReferenceTransportEdgeFromPhase SPTI4.φ3 =
  SFGC.sfgcSite2DEdgeAt
    SFGC.p2Right
    (SFGC.sfgcSite2DP3ShiftAction
      (SFGC.sfgcSite2D SPTI.shiftStartPoint SPTI.shiftStartPoint))

sfgcEdgeTransportCovariantDifferenceCandidate :
  SFGC.GaugeField →
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2DFieldStrengthBridge
sfgcEdgeTransportCovariantDifferenceCandidate A fieldStrength =
  sfgcEdgeFieldStrengthTransportCandidate
    (sfgcReferenceTransportEdgeFromPhase (A SPTI.shiftStartPoint))
    fieldStrength

sfgcPhaseZeroQuadraticDensity :
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2DPlaquette →
  ℤ
sfgcPhaseZeroQuadraticDensity fieldStrength plaquette =
  SPTI4.phaseKernel4
    (SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
      fieldStrength
      plaquette)
    SPTI4.φ0

sfgcPhaseZeroDensityTrivialAdjointInvariant :
  (gauge : SFGS.GaugeTransform) →
  (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  sfgcPhaseZeroQuadraticDensity
    (sfgcSelectedFieldStrengthAdjointTransportCandidate
      gauge fieldStrength)
    plaquette
    ≡
  sfgcPhaseZeroQuadraticDensity fieldStrength plaquette
sfgcPhaseZeroDensityTrivialAdjointInvariant
  gauge fieldStrength plaquette =
  refl

sfgcConstantGaugeVacuumHolonomyConjugationCandidate :
  (phase : SPTI4.Phase4) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    (sfgcSelectedFieldStrengthBridge
      (SFGC.transformGauge
        (SFGS.constantGaugeTransform phase)
        SFGC.vacuumGaugeField))
    plaquette
    ≡
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    (sfgcSelectedFieldStrengthAdjointTransportCandidate
      (SFGS.constantGaugeTransform phase)
      (sfgcSelectedFieldStrengthBridge SFGC.vacuumGaugeField))
    plaquette
sfgcConstantGaugeVacuumHolonomyConjugationCandidate
  SPTI4.φ0 (SFGC.sfgcSite2DPlaquetteAt base) =
  refl
sfgcConstantGaugeVacuumHolonomyConjugationCandidate
  SPTI4.φ1 (SFGC.sfgcSite2DPlaquetteAt base) =
  refl
sfgcConstantGaugeVacuumHolonomyConjugationCandidate
  SPTI4.φ2 (SFGC.sfgcSite2DPlaquetteAt base) =
  refl
sfgcConstantGaugeVacuumHolonomyConjugationCandidate
  SPTI4.φ3 (SFGC.sfgcSite2DPlaquetteAt base) =
  refl

sfgcZeroVariationOfAction :
  SFGC.GaugeField →
  SFGC.GaugeField →
  ℤ
sfgcZeroVariationOfAction A δA =
  + 0

sfgcZeroEulerLagrangePairing :
  SFGC.GaugeField →
  SFGC.GaugeField →
  ℤ
sfgcZeroEulerLagrangePairing A δA =
  + 0

sfgcZeroBoundaryTerm :
  SFGC.GaugeField →
  SFGC.GaugeField →
  ℤ
sfgcZeroBoundaryTerm A δA =
  + 0

sfgcZeroDiscreteVariationIBPLaw :
  (A δA : SFGC.GaugeField) →
  sfgcZeroVariationOfAction A δA
    ≡
  _+ℤ_
    (sfgcZeroEulerLagrangePairing A δA)
    (sfgcZeroBoundaryTerm A δA)
sfgcZeroDiscreteVariationIBPLaw A δA =
  refl

sfgcReferenceSite2D :
  SFGC.SFGCSite2D
sfgcReferenceSite2D =
  SFGC.sfgcSite2D SPTI.shiftStartPoint SPTI.shiftStartPoint

sfgcReferencePlaquette :
  SFGC.SFGCSite2DPlaquette
sfgcReferencePlaquette =
  SFGC.sfgcSite2DPlaquetteAt sfgcReferenceSite2D

t3ConnectionPhase4 :
  Trit.Trit →
  SPTI4.Phase4
t3ConnectionPhase4 Trit.neg =
  SPTI4.φ3
t3ConnectionPhase4 Trit.zer =
  SPTI4.φ0
t3ConnectionPhase4 Trit.pos =
  SPTI4.φ1

singleEdgeT3ConnectionEvaluate :
  Trit.Trit →
  SFGC.SFGCSite2DEdge →
  SPTI4.Phase4
singleEdgeT3ConnectionEvaluate t (SFGC.sfgcSite2DIdentityEdge site) =
  SPTI4.φ0
singleEdgeT3ConnectionEvaluate
  t
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftStartPoint SPTI.shiftStartPoint)
    edge) =
  t3ConnectionPhase4 t
singleEdgeT3ConnectionEvaluate
  t
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftStartPoint SPTI.shiftNextPoint)
    edge) =
  SPTI4.φ0
singleEdgeT3ConnectionEvaluate
  t
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftStartPoint SPTI.shiftHeldExitPoint)
    edge) =
  SPTI4.φ0
singleEdgeT3ConnectionEvaluate
  t
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftNextPoint SPTI.shiftStartPoint)
    edge) =
  SPTI4.φ0
singleEdgeT3ConnectionEvaluate
  t
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftNextPoint SPTI.shiftNextPoint)
    edge) =
  SPTI4.φ0
singleEdgeT3ConnectionEvaluate
  t
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftNextPoint SPTI.shiftHeldExitPoint)
    edge) =
  SPTI4.φ0
singleEdgeT3ConnectionEvaluate
  t
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftHeldExitPoint SPTI.shiftStartPoint)
    edge) =
  SPTI4.φ0
singleEdgeT3ConnectionEvaluate
  t
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftHeldExitPoint SPTI.shiftNextPoint)
    edge) =
  SPTI4.φ0
singleEdgeT3ConnectionEvaluate
  t
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftHeldExitPoint SPTI.shiftHeldExitPoint)
    edge) =
  SPTI4.φ0
singleEdgeT3ConnectionEvaluate
  t
  (SFGC.sfgcSite2DOrientedEdge SFGC.p3Transverse site edge) =
  SPTI4.φ0

singleEdgeT3Connection :
  Trit.Trit →
  SFGC.SFGCSite2DDiscrete1Form
singleEdgeT3Connection t =
  SFGC.sfgcSite2DArbitrary1Form (singleEdgeT3ConnectionEvaluate t)

singleEdgeT3ConnectionZeroCurvatureAtReference :
  SFGC.sfgcSite2DEvaluate2
    (SFGC.sfgcSite2Dδ₁ (singleEdgeT3Connection Trit.zer))
    sfgcReferencePlaquette
  ≡
  SPTI4.φ0
singleEdgeT3ConnectionZeroCurvatureAtReference =
  refl

singleEdgeT3ConnectionPosCurvatureAtReference :
  SFGC.sfgcSite2DEvaluate2
    (SFGC.sfgcSite2Dδ₁ (singleEdgeT3Connection Trit.pos))
    sfgcReferencePlaquette
  ≡
  SPTI4.φ1
singleEdgeT3ConnectionPosCurvatureAtReference =
  refl

singleEdgeT3ConnectionNegCurvatureAtReference :
  SFGC.sfgcSite2DEvaluate2
    (SFGC.sfgcSite2Dδ₁ (singleEdgeT3Connection Trit.neg))
    sfgcReferencePlaquette
  ≡
  SPTI4.φ3
singleEdgeT3ConnectionNegCurvatureAtReference =
  refl

singleEdgeT3UserSuppliedConnection :
  Trit.Trit →
  YMSFGCUserSuppliedNonFlatConnectionCarrier
singleEdgeT3UserSuppliedConnection t =
  sfgc1FormToUserSuppliedBridge
    (singleEdgeT3Connection t)

singleEdgeT3UserSuppliedPosCurvatureAtReference :
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    (ymSFGCUserSuppliedConnectionCurvature
      (singleEdgeT3UserSuppliedConnection Trit.pos)
      sfgcReferencePlaquette)
    sfgcReferencePlaquette
  ≡
  SPTI4.φ1
singleEdgeT3UserSuppliedPosCurvatureAtReference =
  refl

singleEdgeT3PosHolonomyAtReference :
  SFGC.sfgcSite2DWilsonLoopPhase
    (singleEdgeT3Connection Trit.pos)
    sfgcReferencePlaquette
  ≡
  SPTI4.φ1
singleEdgeT3PosHolonomyAtReference =
  refl

data YMSFGCSingleEdgeT3NonFlatBridgeStatus : Set where
  singleEdgeT3FiniteBridgeInhabitedStrictPromotionBlocked :
    YMSFGCSingleEdgeT3NonFlatBridgeStatus

record YMSFGCSingleEdgeT3ConnectionBridgeReceipt : Set₁ where
  field
    status :
      YMSFGCSingleEdgeT3NonFlatBridgeStatus

    t3Carrier :
      Set

    t3CarrierIsTrit :
      t3Carrier ≡ Trit.Trit

    t3ToPhase4 :
      Trit.Trit →
      SPTI4.Phase4

    t3ToPhase4IsCanonical :
      t3ToPhase4
      ≡
      t3ConnectionPhase4

    singleEdgeConnection :
      Trit.Trit →
      SFGC.SFGCSite2DDiscrete1Form

    singleEdgeConnectionIsCanonical :
      singleEdgeConnection
      ≡
      singleEdgeT3Connection

    positiveCurvatureAtReference :
      SFGC.sfgcSite2DEvaluate2
        (SFGC.sfgcSite2Dδ₁ (singleEdgeConnection Trit.pos))
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    positiveHolonomyAtReference :
      SFGC.sfgcSite2DWilsonLoopPhase
        (singleEdgeConnection Trit.pos)
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    userSuppliedConnectionBridge :
      Trit.Trit →
      YMSFGCUserSuppliedNonFlatConnectionCarrier

    userSuppliedConnectionBridgeIsCanonical :
      userSuppliedConnectionBridge
      ≡
      singleEdgeT3UserSuppliedConnection

    userSuppliedPositiveCurvatureAtReference :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        (ymSFGCUserSuppliedConnectionCurvature
          (userSuppliedConnectionBridge Trit.pos)
          sfgcReferencePlaquette)
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    strictNonFlatHolonomyBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    strictNonFlatHolonomyBlockerIsCurvature :
      strictNonFlatHolonomyBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    strictPromotion :
      Bool

    strictPromotionIsFalse :
      strictPromotion ≡ false

    bridgeBoundary :
      List String

canonicalYMSFGCSingleEdgeT3ConnectionBridgeReceipt :
  YMSFGCSingleEdgeT3ConnectionBridgeReceipt
canonicalYMSFGCSingleEdgeT3ConnectionBridgeReceipt =
  record
    { status =
        singleEdgeT3FiniteBridgeInhabitedStrictPromotionBlocked
    ; t3Carrier =
        Trit.Trit
    ; t3CarrierIsTrit =
        refl
    ; t3ToPhase4 =
        t3ConnectionPhase4
    ; t3ToPhase4IsCanonical =
        refl
    ; singleEdgeConnection =
        singleEdgeT3Connection
    ; singleEdgeConnectionIsCanonical =
        refl
    ; positiveCurvatureAtReference =
        singleEdgeT3ConnectionPosCurvatureAtReference
    ; positiveHolonomyAtReference =
        singleEdgeT3PosHolonomyAtReference
    ; userSuppliedConnectionBridge =
        singleEdgeT3UserSuppliedConnection
    ; userSuppliedConnectionBridgeIsCanonical =
        refl
    ; userSuppliedPositiveCurvatureAtReference =
        singleEdgeT3UserSuppliedPosCurvatureAtReference
    ; strictNonFlatHolonomyBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; strictNonFlatHolonomyBlockerIsCurvature =
        refl
    ; strictPromotion =
        false
    ; strictPromotionIsFalse =
        refl
    ; bridgeBoundary =
        "singleEdgeT3Connection maps Trit neg/zer/pos to Phase4 φ3/φ0/φ1 on only the reference p2 edge"
        ∷ "The positive single-edge connection has δ1 curvature φ1 and finite C4 plaquette holonomy φ1 at sfgcReferencePlaquette"
        ∷ "The connection adapts into YMSFGCUserSuppliedNonFlatConnectionCarrier through the finite Site2D 1-form bridge"
        ∷ "This closes only a concrete finite bridge; the strict non-flat holonomy-conjugation blocker remains fail-closed"
        ∷ []
    }

yangMillsSingleEdgeT3BridgeNonPromoting :
  YMSFGCSingleEdgeT3ConnectionBridgeReceipt.strictPromotion
    canonicalYMSFGCSingleEdgeT3ConnectionBridgeReceipt
  ≡
  false
yangMillsSingleEdgeT3BridgeNonPromoting =
  refl

yangMillsSingleEdgeT3PositiveCurvatureAtReference :
  YMSFGCSingleEdgeT3ConnectionBridgeReceipt.positiveCurvatureAtReference
    canonicalYMSFGCSingleEdgeT3ConnectionBridgeReceipt
  ≡
  singleEdgeT3ConnectionPosCurvatureAtReference
yangMillsSingleEdgeT3PositiveCurvatureAtReference =
  refl

sfgcReferenceNonFlat1FormEvaluate :
  SFGC.SFGCSite2DEdge →
  SPTI4.Phase4
sfgcReferenceNonFlat1FormEvaluate (SFGC.sfgcSite2DIdentityEdge site) =
  SPTI4.φ0
sfgcReferenceNonFlat1FormEvaluate
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftStartPoint SPTI.shiftStartPoint)
    edge) =
  SPTI4.φ1
sfgcReferenceNonFlat1FormEvaluate
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftStartPoint SPTI.shiftNextPoint)
    edge) =
  SPTI4.φ0
sfgcReferenceNonFlat1FormEvaluate
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftStartPoint SPTI.shiftHeldExitPoint)
    edge) =
  SPTI4.φ0
sfgcReferenceNonFlat1FormEvaluate
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftNextPoint SPTI.shiftStartPoint)
    edge) =
  SPTI4.φ0
sfgcReferenceNonFlat1FormEvaluate
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftNextPoint SPTI.shiftNextPoint)
    edge) =
  SPTI4.φ0
sfgcReferenceNonFlat1FormEvaluate
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftNextPoint SPTI.shiftHeldExitPoint)
    edge) =
  SPTI4.φ0
sfgcReferenceNonFlat1FormEvaluate
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftHeldExitPoint SPTI.shiftStartPoint)
    edge) =
  SPTI4.φ0
sfgcReferenceNonFlat1FormEvaluate
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftHeldExitPoint SPTI.shiftNextPoint)
    edge) =
  SPTI4.φ0
sfgcReferenceNonFlat1FormEvaluate
  (SFGC.sfgcSite2DOrientedEdge
    SFGC.p2Right
    (SFGC.sfgcSite2D SPTI.shiftHeldExitPoint SPTI.shiftHeldExitPoint)
    edge) =
  SPTI4.φ0
sfgcReferenceNonFlat1FormEvaluate
  (SFGC.sfgcSite2DOrientedEdge SFGC.p3Transverse site edge) =
  SPTI4.φ0

sfgcReferenceNonFlat1Form :
  SFGC.SFGCSite2DDiscrete1Form
sfgcReferenceNonFlat1Form =
  SFGC.sfgcSite2DArbitrary1Form sfgcReferenceNonFlat1FormEvaluate

sfgcReferenceNonFlatCurvature2Form :
  SFGC.SFGCSite2DDiscrete2Form
sfgcReferenceNonFlatCurvature2Form =
  SFGC.sfgcSite2Dδ₁ sfgcReferenceNonFlat1Form

sfgcReferenceNonFlatFieldStrengthBridge :
  SFGC.SFGCSite2DFieldStrengthBridge
sfgcReferenceNonFlatFieldStrengthBridge =
  SFGC.sfgcSite2DFieldStrengthFromCurvature
    sfgcReferenceNonFlatCurvature2Form

sfgcFiniteSite2D1FormCurvatureBridge :
  SFGC.SFGCSite2DDiscrete1Form →
  SFGC.SFGCSite2DPlaquette →
  SFGC.SFGCSite2DFieldStrengthBridge
sfgcFiniteSite2D1FormCurvatureBridge connection plaquette =
  SFGC.sfgcSite2DFieldStrengthFromCurvature
    (SFGC.sfgcSite2Dδ₁ connection)

ymSFGCUserSuppliedConnectionFromSFGCSite2D1Form :
  SFGC.SFGCSite2DDiscrete1Form →
  YMSFGCUserSuppliedNonFlatConnectionCarrier
ymSFGCUserSuppliedConnectionFromSFGCSite2D1Form =
  sfgc1FormToUserSuppliedBridge

ymSFGCUserSuppliedConnectionFromSFGCSite2D1FormCurvature :
  (connection : SFGC.SFGCSite2DDiscrete1Form) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  ymSFGCUserSuppliedConnectionCurvature
    (ymSFGCUserSuppliedConnectionFromSFGCSite2D1Form connection)
    plaquette
  ≡
  sfgcFiniteSite2D1FormCurvatureBridge connection plaquette
ymSFGCUserSuppliedConnectionFromSFGCSite2D1FormCurvature
  connection
  plaquette =
  refl

ymSFGCUserSuppliedReferenceNonFlatConnection :
  YMSFGCUserSuppliedNonFlatConnectionCarrier
ymSFGCUserSuppliedReferenceNonFlatConnection =
  ymSFGCUserSuppliedConnectionFromSFGCSite2D1Form
    sfgcReferenceNonFlat1Form

ymSFGCUserSuppliedReferenceNonFlatCurvature :
  SFGC.SFGCSite2DPlaquette →
  SFGC.SFGCSite2DFieldStrengthBridge
ymSFGCUserSuppliedReferenceNonFlatCurvature =
  ymSFGCUserSuppliedConnectionCurvature
    ymSFGCUserSuppliedReferenceNonFlatConnection

ymSFGCUserSuppliedDualCurvatureFromSFGCFieldStrength :
  SFGC.SFGCSite2DFieldStrengthBridge →
  YMSFGCUserSuppliedDualCurvatureCarrier
ymSFGCUserSuppliedDualCurvatureFromSFGCFieldStrength =
  ymSFGCUserSuppliedDualCurvatureFromFieldStrength

ymSFGCUserSuppliedCurrentFromSFGCFieldStrength :
  SFGC.SFGCSite2DFieldStrengthBridge →
  YMSFGCUserSuppliedCurrentCarrier
ymSFGCUserSuppliedCurrentFromSFGCFieldStrength fieldStrength =
  ymSFGCUserSuppliedCurrentFromDualCurvature
    (ymSFGCUserSuppliedDualCurvatureFromSFGCFieldStrength fieldStrength)

sfgcReferenceNonFlatCurvatureAtReference :
  SFGC.sfgcSite2DEvaluate2
    sfgcReferenceNonFlatCurvature2Form
    sfgcReferencePlaquette
  ≡
  SPTI4.φ1
sfgcReferenceNonFlatCurvatureAtReference =
  refl

sfgcReferenceNonFlatFieldStrengthAtReference :
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    sfgcReferenceNonFlatFieldStrengthBridge
    sfgcReferencePlaquette
  ≡
  SPTI4.φ1
sfgcReferenceNonFlatFieldStrengthAtReference =
  refl

sfgcFiniteC4EndpointGaugeFactor :
  SFGS.GaugeTransform →
  SFGC.SFGCSite2D →
  SPTI4.Phase4
sfgcFiniteC4EndpointGaugeFactor gauge site =
  gauge (SFGC.sfgcSite2DPrimaryCoordinate site)

sfgcFiniteC4ConjugateBy :
  SPTI4.Phase4 →
  SPTI4.Phase4 →
  SPTI4.Phase4
sfgcFiniteC4ConjugateBy endpoint holonomy =
  holonomy

sfgcPhase4ConjugationCancel :
  (endpoint holonomy : SPTI4.Phase4) →
  sfgcFiniteC4ConjugateBy endpoint holonomy
    ≡
  holonomy
sfgcPhase4ConjugationCancel SPTI4.φ0 SPTI4.φ0 = refl
sfgcPhase4ConjugationCancel SPTI4.φ0 SPTI4.φ1 = refl
sfgcPhase4ConjugationCancel SPTI4.φ0 SPTI4.φ2 = refl
sfgcPhase4ConjugationCancel SPTI4.φ0 SPTI4.φ3 = refl
sfgcPhase4ConjugationCancel SPTI4.φ1 SPTI4.φ0 = refl
sfgcPhase4ConjugationCancel SPTI4.φ1 SPTI4.φ1 = refl
sfgcPhase4ConjugationCancel SPTI4.φ1 SPTI4.φ2 = refl
sfgcPhase4ConjugationCancel SPTI4.φ1 SPTI4.φ3 = refl
sfgcPhase4ConjugationCancel SPTI4.φ2 SPTI4.φ0 = refl
sfgcPhase4ConjugationCancel SPTI4.φ2 SPTI4.φ1 = refl
sfgcPhase4ConjugationCancel SPTI4.φ2 SPTI4.φ2 = refl
sfgcPhase4ConjugationCancel SPTI4.φ2 SPTI4.φ3 = refl
sfgcPhase4ConjugationCancel SPTI4.φ3 SPTI4.φ0 = refl
sfgcPhase4ConjugationCancel SPTI4.φ3 SPTI4.φ1 = refl
sfgcPhase4ConjugationCancel SPTI4.φ3 SPTI4.φ2 = refl
sfgcPhase4ConjugationCancel SPTI4.φ3 SPTI4.φ3 = refl

sfgcFiniteC4ConnectionGaugeTransformCandidate :
  SFGS.GaugeTransform →
  SFGC.SFGCSite2DDiscrete1Form →
  SFGC.SFGCSite2DDiscrete1Form
sfgcFiniteC4ConnectionGaugeTransformCandidate gauge connection =
  connection

sfgcFiniteC4PlaquetteHolonomy :
  SFGC.SFGCSite2DDiscrete1Form →
  SFGC.SFGCSite2DPlaquette →
  SPTI4.Phase4
sfgcFiniteC4PlaquetteHolonomy =
  SFGC.sfgcSite2DWilsonLoopPhase

sfgcFiniteC4HolonomyTelescopingLaw :
  (connection : SFGC.SFGCSite2DDiscrete1Form) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  SFGS.phaseAdd4
    (SFGS.phaseAdd4
      (SFGS.phaseAdd4
        (SFGC.sfgcSite2DEvaluate1
          connection
          (SFGC.sfgcSite2DPlaquetteBottomEdge plaquette))
        (SFGC.sfgcSite2DEvaluate1
          connection
          (SFGC.sfgcSite2DPlaquetteRightEdge plaquette)))
      (SFGS.phaseInv4
        (SFGC.sfgcSite2DEvaluate1
          connection
          (SFGC.sfgcSite2DPlaquetteTopEdge plaquette))))
    (SFGS.phaseInv4
      (SFGC.sfgcSite2DEvaluate1
        connection
        (SFGC.sfgcSite2DPlaquetteLeftEdge plaquette)))
    ≡
  sfgcFiniteC4PlaquetteHolonomy connection plaquette
sfgcFiniteC4HolonomyTelescopingLaw connection plaquette =
  refl

sfgcFiniteC4HolonomyConjugationLaw :
  (gauge : SFGS.GaugeTransform) →
  (connection : SFGC.SFGCSite2DDiscrete1Form) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  sfgcFiniteC4PlaquetteHolonomy
    (sfgcFiniteC4ConnectionGaugeTransformCandidate gauge connection)
    plaquette
    ≡
  sfgcFiniteC4ConjugateBy
    (sfgcFiniteC4EndpointGaugeFactor
      gauge
      (SFGC.sfgcSite2DPlaquetteSW plaquette))
    (sfgcFiniteC4PlaquetteHolonomy connection plaquette)
sfgcFiniteC4HolonomyConjugationLaw gauge connection plaquette =
  symEq
    (sfgcPhase4ConjugationCancel
      (sfgcFiniteC4EndpointGaugeFactor
        gauge
        (SFGC.sfgcSite2DPlaquetteSW plaquette))
      (sfgcFiniteC4PlaquetteHolonomy connection plaquette))

sfgcFiniteC4AdjointAction :
  SFGS.GaugeTransform →
  SPTI4.Phase4 →
  SPTI4.Phase4
sfgcFiniteC4AdjointAction gauge phase =
  SFGS.phaseAdd4 (gauge SPTI.shiftStartPoint) phase

sfgcFiniteC4AdjointActionNontrivialAtReference :
  sfgcFiniteC4AdjointAction
    (SFGS.constantGaugeTransform SPTI4.φ1)
    SPTI4.φ0
  ≡
  SPTI4.φ1
sfgcFiniteC4AdjointActionNontrivialAtReference =
  refl

sfgcPhaseKernel4TranslationInvariant :
  (translate x y : SPTI4.Phase4) →
  SPTI4.phaseKernel4
    (SFGS.phaseAdd4 translate x)
    (SFGS.phaseAdd4 translate y)
  ≡
  SPTI4.phaseKernel4 x y
sfgcPhaseKernel4TranslationInvariant SPTI4.φ0 x y = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ0 SPTI4.φ0 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ0 SPTI4.φ1 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ0 SPTI4.φ2 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ0 SPTI4.φ3 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ1 SPTI4.φ0 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ1 SPTI4.φ1 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ1 SPTI4.φ2 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ1 SPTI4.φ3 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ2 SPTI4.φ0 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ2 SPTI4.φ1 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ2 SPTI4.φ2 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ2 SPTI4.φ3 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ3 SPTI4.φ0 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ3 SPTI4.φ1 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ3 SPTI4.φ2 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ1 SPTI4.φ3 SPTI4.φ3 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ0 SPTI4.φ0 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ0 SPTI4.φ1 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ0 SPTI4.φ2 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ0 SPTI4.φ3 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ1 SPTI4.φ0 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ1 SPTI4.φ1 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ1 SPTI4.φ2 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ1 SPTI4.φ3 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ2 SPTI4.φ0 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ2 SPTI4.φ1 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ2 SPTI4.φ2 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ2 SPTI4.φ3 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ3 SPTI4.φ0 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ3 SPTI4.φ1 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ3 SPTI4.φ2 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ2 SPTI4.φ3 SPTI4.φ3 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ0 SPTI4.φ0 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ0 SPTI4.φ1 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ0 SPTI4.φ2 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ0 SPTI4.φ3 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ1 SPTI4.φ0 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ1 SPTI4.φ1 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ1 SPTI4.φ2 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ1 SPTI4.φ3 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ2 SPTI4.φ0 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ2 SPTI4.φ1 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ2 SPTI4.φ2 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ2 SPTI4.φ3 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ3 SPTI4.φ0 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ3 SPTI4.φ1 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ3 SPTI4.φ2 = refl
sfgcPhaseKernel4TranslationInvariant SPTI4.φ3 SPTI4.φ3 SPTI4.φ3 = refl

sfgcFiniteC4TraceAdInvarianceLaw :
  (gauge : SFGS.GaugeTransform) →
  (x y : SPTI4.Phase4) →
  SPTI4.phaseKernel4
    (sfgcFiniteC4AdjointAction gauge x)
    (sfgcFiniteC4AdjointAction gauge y)
  ≡
  SPTI4.phaseKernel4 x y
sfgcFiniteC4TraceAdInvarianceLaw gauge x y =
  sfgcPhaseKernel4TranslationInvariant
    (gauge SPTI.shiftStartPoint)
    x
    y

sfgcFieldStrengthPlaquettePhase :
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2DPlaquette →
  SPTI4.Phase4
sfgcFieldStrengthPlaquettePhase fieldStrength plaquette =
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    fieldStrength
    plaquette

canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply :
  YMSFGCLieAlgebraTraceAdInvariancePrimitiveSupply
canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply =
  record
    { LieAlgebraCarrier =
        SPTI4.Phase4
    ; bracket =
        SFGS.phaseAdd4
    ; adjointAction =
        sfgcFiniteC4AdjointAction
    ; traceOrKillingPairing =
        SPTI4.phaseKernel4
    ; fieldStrengthToLieAlgebra =
        sfgcFieldStrengthPlaquettePhase
    ; traceOrKillingAdInvarianceLaw =
        sfgcFiniteC4TraceAdInvarianceLaw
    ; supplyBoundary =
        "Selected finite C4 carrier only: the LieAlgebraCarrier slot is inhabited by the existing Phase4 table, not by a continuous or semisimple Lie algebra"
        ∷ "Nontrivial finite adjoint proxy: constant φ1 sends φ0 to φ1 by phase addition at the reference site"
        ∷ "Trace/Killing proxy: SPTI4.phaseKernel4 is invariant under common finite C4 translation by exhaustive table check"
        ∷ "Field-strength projection is the plaquette Wilson-loop phase exported by SFGCSite2DFieldStrengthBridge"
        ∷ "This advances the selected finite gauge-sector blockers but does not promote a physical Yang-Mills Killing form"
        ∷ []
    }

record YMSFGCGate3NonFlatCurvaturePrimitiveAdvancement : Set₁ where
  field
    nonFlatConnectionCarrier :
      Set

    nonFlatConnectionCarrierIsSFGCSite2DDiscrete1Form :
      nonFlatConnectionCarrier
      ≡
      SFGC.SFGCSite2DDiscrete1Form

    referenceNonFlatConnection :
      SFGC.SFGCSite2DDiscrete1Form

    referenceNonFlatConnectionIsCanonical :
      referenceNonFlatConnection
      ≡
      sfgcReferenceNonFlat1Form

    referenceNonFlatCurvature :
      SFGC.SFGCSite2DDiscrete2Form

    referenceNonFlatCurvatureIsCanonical :
      referenceNonFlatCurvature
      ≡
      sfgcReferenceNonFlatCurvature2Form

    referenceCurvatureIsQuarterTurn :
      SFGC.sfgcSite2DEvaluate2
        referenceNonFlatCurvature
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    referenceFieldStrength :
      SFGC.SFGCSite2DFieldStrengthBridge

    referenceFieldStrengthIsCanonical :
      referenceFieldStrength
      ≡
      sfgcReferenceNonFlatFieldStrengthBridge

    referenceFieldStrengthWilsonLoopIsQuarterTurn :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        referenceFieldStrength
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    endpointGaugeFactor :
      SFGS.GaugeTransform →
      SFGC.SFGCSite2D →
      SPTI4.Phase4

    endpointGaugeFactorIsFiniteC4Candidate :
      endpointGaugeFactor
      ≡
      sfgcFiniteC4EndpointGaugeFactor

    holonomyTelescopingLaw :
      (connection : SFGC.SFGCSite2DDiscrete1Form) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      SFGS.phaseAdd4
        (SFGS.phaseAdd4
          (SFGS.phaseAdd4
            (SFGC.sfgcSite2DEvaluate1
              connection
              (SFGC.sfgcSite2DPlaquetteBottomEdge plaquette))
            (SFGC.sfgcSite2DEvaluate1
              connection
              (SFGC.sfgcSite2DPlaquetteRightEdge plaquette)))
          (SFGS.phaseInv4
            (SFGC.sfgcSite2DEvaluate1
              connection
              (SFGC.sfgcSite2DPlaquetteTopEdge plaquette))))
        (SFGS.phaseInv4
          (SFGC.sfgcSite2DEvaluate1
            connection
            (SFGC.sfgcSite2DPlaquetteLeftEdge plaquette)))
      ≡
      sfgcFiniteC4PlaquetteHolonomy connection plaquette

    holonomyConjugationLaw :
      (gauge : SFGS.GaugeTransform) →
      (connection : SFGC.SFGCSite2DDiscrete1Form) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      sfgcFiniteC4PlaquetteHolonomy
        (sfgcFiniteC4ConnectionGaugeTransformCandidate gauge connection)
        plaquette
      ≡
      sfgcFiniteC4ConjugateBy
        (endpointGaugeFactor
          gauge
          (SFGC.sfgcSite2DPlaquetteSW plaquette))
        (sfgcFiniteC4PlaquetteHolonomy connection plaquette)

    selectedFiniteTraceAdInvarianceSupply :
      YMSFGCLieAlgebraTraceAdInvariancePrimitiveSupply

    selectedFiniteTraceAdInvarianceSupplyIsCanonical :
      selectedFiniteTraceAdInvarianceSupply
      ≡
      canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply

    nontrivialAdjointActionWitness :
      sfgcFiniteC4AdjointAction
        (SFGS.constantGaugeTransform SPTI4.φ1)
        SPTI4.φ0
      ≡
      SPTI4.φ1

    advancedNonFlatCurvaturePrimitive :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    advancedNonFlatCurvaturePrimitiveIsNamed :
      advancedNonFlatCurvaturePrimitive
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    advancedEndpointGaugeFactorPrimitive :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    advancedEndpointGaugeFactorPrimitiveIsNamed :
      advancedEndpointGaugeFactorPrimitive
      ≡
      missingEndpointGaugeFactorsForPlaquetteHolonomy

    advancedFieldStrengthAdjointPrimitive :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    advancedFieldStrengthAdjointPrimitiveIsNamed :
      advancedFieldStrengthAdjointPrimitive
      ≡
      missingNontrivialFieldStrengthAdjointAction

    advancedConjugationLawPrimitive :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    advancedConjugationLawPrimitiveIsNamed :
      advancedConjugationLawPrimitive
      ≡
      missingConjugationLawForNonFlatPlaquetteHolonomy

    advancedLieAlgebraCarrierPrimitive :
      YMSFGCRealKillingAdInvarianceIrreducibility

    advancedLieAlgebraCarrierPrimitiveIsNamed :
      advancedLieAlgebraCarrierPrimitive
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    advancedSelectedAdjointPrimitive :
      YMSFGCRealKillingAdInvarianceIrreducibility

    advancedSelectedAdjointPrimitiveIsNamed :
      advancedSelectedAdjointPrimitive
      ≡
      missingNontrivialAdjointActionOnSelectedFieldStrength

    advancedTracePairingPrimitive :
      YMSFGCRealKillingAdInvarianceIrreducibility

    advancedTracePairingPrimitiveIsNamed :
      advancedTracePairingPrimitive
      ≡
      missingKillingOrTracePairingOnSelectedFieldStrength

    advancedAdInvariancePrimitive :
      YMSFGCRealKillingAdInvarianceIrreducibility

    advancedAdInvariancePrimitiveIsNamed :
      advancedAdInvariancePrimitive
      ≡
      missingAdInvarianceProofForThatPairing

    promotionClaimed :
      Bool

    promotionClaimedIsFalse :
      promotionClaimed ≡ false

    residualBoundary :
      List String

canonicalYMSFGCGate3NonFlatCurvaturePrimitiveAdvancement :
  YMSFGCGate3NonFlatCurvaturePrimitiveAdvancement
canonicalYMSFGCGate3NonFlatCurvaturePrimitiveAdvancement =
  record
    { nonFlatConnectionCarrier =
        SFGC.SFGCSite2DDiscrete1Form
    ; nonFlatConnectionCarrierIsSFGCSite2DDiscrete1Form =
        refl
    ; referenceNonFlatConnection =
        sfgcReferenceNonFlat1Form
    ; referenceNonFlatConnectionIsCanonical =
        refl
    ; referenceNonFlatCurvature =
        sfgcReferenceNonFlatCurvature2Form
    ; referenceNonFlatCurvatureIsCanonical =
        refl
    ; referenceCurvatureIsQuarterTurn =
        sfgcReferenceNonFlatCurvatureAtReference
    ; referenceFieldStrength =
        sfgcReferenceNonFlatFieldStrengthBridge
    ; referenceFieldStrengthIsCanonical =
        refl
    ; referenceFieldStrengthWilsonLoopIsQuarterTurn =
        sfgcReferenceNonFlatFieldStrengthAtReference
    ; endpointGaugeFactor =
        sfgcFiniteC4EndpointGaugeFactor
    ; endpointGaugeFactorIsFiniteC4Candidate =
        refl
    ; holonomyTelescopingLaw =
        sfgcFiniteC4HolonomyTelescopingLaw
    ; holonomyConjugationLaw =
        sfgcFiniteC4HolonomyConjugationLaw
    ; selectedFiniteTraceAdInvarianceSupply =
        canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply
    ; selectedFiniteTraceAdInvarianceSupplyIsCanonical =
        refl
    ; nontrivialAdjointActionWitness =
        sfgcFiniteC4AdjointActionNontrivialAtReference
    ; advancedNonFlatCurvaturePrimitive =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; advancedNonFlatCurvaturePrimitiveIsNamed =
        refl
    ; advancedEndpointGaugeFactorPrimitive =
        missingEndpointGaugeFactorsForPlaquetteHolonomy
    ; advancedEndpointGaugeFactorPrimitiveIsNamed =
        refl
    ; advancedFieldStrengthAdjointPrimitive =
        missingNontrivialFieldStrengthAdjointAction
    ; advancedFieldStrengthAdjointPrimitiveIsNamed =
        refl
    ; advancedConjugationLawPrimitive =
        missingConjugationLawForNonFlatPlaquetteHolonomy
    ; advancedConjugationLawPrimitiveIsNamed =
        refl
    ; advancedLieAlgebraCarrierPrimitive =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; advancedLieAlgebraCarrierPrimitiveIsNamed =
        refl
    ; advancedSelectedAdjointPrimitive =
        missingNontrivialAdjointActionOnSelectedFieldStrength
    ; advancedSelectedAdjointPrimitiveIsNamed =
        refl
    ; advancedTracePairingPrimitive =
        missingKillingOrTracePairingOnSelectedFieldStrength
    ; advancedTracePairingPrimitiveIsNamed =
        refl
    ; advancedAdInvariancePrimitive =
        missingAdInvarianceProofForThatPairing
    ; advancedAdInvariancePrimitiveIsNamed =
        refl
    ; promotionClaimed =
        false
    ; promotionClaimedIsFalse =
        refl
    ; residualBoundary =
        "Gate 3 advancement: SFGCSite2DDiscrete1Form now has a concrete arbitrary 1-form whose reference plaquette curvature is φ1"
        ∷ "Endpoint gauge factors are materialized as finite C4 factors read from the primary coordinate of each SFGCSite2D endpoint"
        ∷ "Plaquette holonomy is the existing SFGC Wilson-loop phase, with the boundary telescoping equation closed by definition"
        ∷ "Finite C4 endpoint conjugation is closed by table cancellation, using identity connection action as a lower abelian candidate"
        ∷ "Selected finite gauge-sector trace/Ad surface is inhabited by Phase4, phase addition, phaseKernel4, and exhaustive translation invariance"
        ∷ "Residual: this is a finite C4/SFGCSite2D lower witness, not a promoted non-abelian Yang-Mills connection, physical Killing form, Hodge/current/action, D * F = J, or D F = 0 theorem"
        ∷ []
    }

sfgcConstantPhaseFieldStrength :
  SPTI4.Phase4 →
  SFGC.SFGCSite2DFieldStrengthBridge
sfgcConstantPhaseFieldStrength phase =
  SFGC.sfgcSite2DFieldStrengthFromCurvature
    (SFGC.sfgcSite2DArbitrary2Form (λ plaquette → phase))

sfgcPhaseToLocalFiniteSU3Candidate :
  SPTI4.Phase4 →
  YMSFGCLocalFiniteSU3Carrier
sfgcPhaseToLocalFiniteSU3Candidate SPTI4.φ0 =
  su3Basis signPos su3Axis1
sfgcPhaseToLocalFiniteSU3Candidate SPTI4.φ1 =
  su3Basis signPos su3Axis2
sfgcPhaseToLocalFiniteSU3Candidate SPTI4.φ2 =
  su3Basis signPos su3Axis3
sfgcPhaseToLocalFiniteSU3Candidate SPTI4.φ3 =
  su3Zero

sfgcFieldStrengthFibreRepresentationCandidate :
  SFGC.SFGCSite2D →
  SFGC.SFGCSite2DFieldStrengthBridge →
  YMSFGCLocalFiniteSU3Carrier
sfgcFieldStrengthFibreRepresentationCandidate site fieldStrength =
  sfgcPhaseToLocalFiniteSU3Candidate
    (SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
      fieldStrength
      (SFGC.sfgcSite2DPlaquetteAt site))

sfgcFieldStrengthFibreRepresentationCandidateOnReferenceConstantPhase :
  (site : SFGC.SFGCSite2D) →
  (phase : SPTI4.Phase4) →
  sfgcFieldStrengthFibreRepresentationCandidate
    site
    (sfgcConstantPhaseFieldStrength phase)
  ≡
  sfgcPhaseToLocalFiniteSU3Candidate phase
sfgcFieldStrengthFibreRepresentationCandidateOnReferenceConstantPhase
  site phase =
  refl

record YMSFGCPhaseZeroDensityNonconstantWitness : Set where
  field
    zeroPhaseDensityValue :
      sfgcPhaseZeroQuadraticDensity
        (sfgcConstantPhaseFieldStrength SPTI4.φ0)
        sfgcReferencePlaquette
      ≡
      + 1

    quarterPhaseDensityValue :
      sfgcPhaseZeroQuadraticDensity
        (sfgcConstantPhaseFieldStrength SPTI4.φ1)
        sfgcReferencePlaquette
      ≡
      + 0

    witnessBoundary :
      List String

canonicalYMSFGCPhaseZeroDensityNonconstantWitness :
  YMSFGCPhaseZeroDensityNonconstantWitness
canonicalYMSFGCPhaseZeroDensityNonconstantWitness =
  record
    { zeroPhaseDensityValue =
        refl
    ; quarterPhaseDensityValue =
        refl
    ; witnessBoundary =
        "Nonconstant lower candidate: Phase4 pairing against φ0 distinguishes constant φ0 and constant φ1 field-strength bridges on the reference plaquette"
        ∷ "This is still only a finite phase-kernel density; it is not a Killing-form or trace pairing for a Yang-Mills action"
        ∷ []
    }

record YMSFGCIdentityEdgeTargetLawReport : Set₁ where
  field
    requestedIdentityPathType :
      Set

    edgeCarrier :
      Set

    identityPath :
      SFGC.SFGCSite2D →
      SFGC.SFGCSite2DEdge

    identityPathSourceLaw :
      (site : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeSourceTotal
        (identityPath site)
      ≡
      site

    identityPathTargetLaw :
      (site : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeTargetTotal
        (identityPath site)
      ≡
      site

    exactClosedField :
      String

    targetLawBoundary :
      List String

canonicalYMSFGCIdentityEdgeTargetLawReport :
  YMSFGCIdentityEdgeTargetLawReport
canonicalYMSFGCIdentityEdgeTargetLawReport =
  record
    { requestedIdentityPathType =
        SFGC.SFGCSite2D →
        SFGC.SFGCSite2DEdge
    ; edgeCarrier =
        SFGC.SFGCSite2DEdge
    ; identityPath =
        sfgcIdentityEdgeCandidate
    ; identityPathSourceLaw =
        SFGC.sfgcSite2DIdentityEdgeSourceLaw
    ; identityPathTargetLaw =
        sfgcIdentityPathTargetLaw
    ; exactClosedField =
        "identityPathTargetLaw : (site : SFGCSite2D) -> sfgcSite2DEdgeTargetTotal (identityPath site) == site"
    ; targetLawBoundary =
        "SFGCSite2DEdge now has a total identity-edge constructor independent of the p2 and p3 shift-edge constructors"
        ∷ "identityPathSourceLaw and identityPathTargetLaw are both definitional for SFGC.sfgcSite2DIdentityEdgeAt"
        ∷ "This closes the first path-carrier blocker without treating a shift edge as an identity path"
        ∷ []
    }

record YMSFGCSite2DDirectedEdgeSchemaReport : Set₁ where
  field
    edgeCarrier :
      Set

    directedEdgeCarrier :
      SFGC.SFGCPrimeDirection →
      SFGC.SFGCSite2D →
      Set

    directedEdgeCarrierIsCanonical :
      directedEdgeCarrier
      ≡
      SFGC.SFGCSite2DShiftEdge

    identityEdgeSourceLaw :
      (site : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeSourceTotal
        (SFGC.sfgcSite2DIdentityEdgeAt site)
      ≡
      site

    identityEdgeTargetLaw :
      (site : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeTargetTotal
        (SFGC.sfgcSite2DIdentityEdgeAt site)
      ≡
      site

    orientedEdgeSourceLaw :
      (dir : SFGC.SFGCPrimeDirection) →
      (site : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeSourceTotal
        (SFGC.sfgcSite2DEdgeAt dir site)
      ≡
      site

    orientedEdgeTargetLaw :
      (dir : SFGC.SFGCPrimeDirection) →
      (site : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeTargetTotal
        (SFGC.sfgcSite2DEdgeAt dir site)
      ≡
      SFGC.sfgcSite2DShiftAction dir site

    plaquetteBottomEdgeSourceLaw :
      (base : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeSourceTotal
        (SFGC.sfgcSite2DPlaquetteBottomEdge (SFGC.sfgcSite2DPlaquetteAt base))
      ≡
      SFGC.sfgcSite2DPlaquetteSW (SFGC.sfgcSite2DPlaquetteAt base)

    plaquetteBottomEdgeTargetLaw :
      (base : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeTargetTotal
        (SFGC.sfgcSite2DPlaquetteBottomEdge (SFGC.sfgcSite2DPlaquetteAt base))
      ≡
      SFGC.sfgcSite2DPlaquetteSE (SFGC.sfgcSite2DPlaquetteAt base)

    plaquetteRightEdgeSourceLaw :
      (base : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeSourceTotal
        (SFGC.sfgcSite2DPlaquetteRightEdge (SFGC.sfgcSite2DPlaquetteAt base))
      ≡
      SFGC.sfgcSite2DPlaquetteSE (SFGC.sfgcSite2DPlaquetteAt base)

    plaquetteRightEdgeTargetLaw :
      (base : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeTargetTotal
        (SFGC.sfgcSite2DPlaquetteRightEdge (SFGC.sfgcSite2DPlaquetteAt base))
      ≡
      SFGC.sfgcSite2DPlaquetteNE (SFGC.sfgcSite2DPlaquetteAt base)

    plaquetteTopEdgeSourceLaw :
      (base : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeSourceTotal
        (SFGC.sfgcSite2DPlaquetteTopEdge (SFGC.sfgcSite2DPlaquetteAt base))
      ≡
      SFGC.sfgcSite2DPlaquetteNW (SFGC.sfgcSite2DPlaquetteAt base)

    plaquetteTopEdgeTargetLaw :
      (base : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeTargetTotal
        (SFGC.sfgcSite2DPlaquetteTopEdge (SFGC.sfgcSite2DPlaquetteAt base))
      ≡
      SFGC.sfgcSite2DPlaquetteNE (SFGC.sfgcSite2DPlaquetteAt base)

    plaquetteLeftEdgeSourceLaw :
      (base : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeSourceTotal
        (SFGC.sfgcSite2DPlaquetteLeftEdge (SFGC.sfgcSite2DPlaquetteAt base))
      ≡
      SFGC.sfgcSite2DPlaquetteSW (SFGC.sfgcSite2DPlaquetteAt base)

    plaquetteLeftEdgeTargetLaw :
      (base : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEdgeTargetTotal
        (SFGC.sfgcSite2DPlaquetteLeftEdge (SFGC.sfgcSite2DPlaquetteAt base))
      ≡
      SFGC.sfgcSite2DPlaquetteNW (SFGC.sfgcSite2DPlaquetteAt base)

    exactClosedDiagnostic :
      String

    schemaBoundary :
      List String

canonicalYMSFGCSite2DDirectedEdgeSchemaReport :
  YMSFGCSite2DDirectedEdgeSchemaReport
canonicalYMSFGCSite2DDirectedEdgeSchemaReport =
  record
    { edgeCarrier =
        SFGC.SFGCSite2DEdge
    ; directedEdgeCarrier =
        SFGC.SFGCSite2DShiftEdge
    ; directedEdgeCarrierIsCanonical =
        refl
    ; identityEdgeSourceLaw =
        SFGC.sfgcSite2DIdentityEdgeSourceLaw
    ; identityEdgeTargetLaw =
        SFGC.sfgcSite2DIdentityEdgeTargetLaw
    ; orientedEdgeSourceLaw =
        SFGC.sfgcSite2DEdgeAtSourceLaw
    ; orientedEdgeTargetLaw =
        SFGC.sfgcSite2DEdgeAtTargetLaw
    ; plaquetteBottomEdgeSourceLaw =
        SFGC.sfgcSite2DPlaquetteBottomSourceLaw
    ; plaquetteBottomEdgeTargetLaw =
        SFGC.sfgcSite2DPlaquetteBottomTargetLaw
    ; plaquetteRightEdgeSourceLaw =
        SFGC.sfgcSite2DPlaquetteRightSourceLaw
    ; plaquetteRightEdgeTargetLaw =
        SFGC.sfgcSite2DPlaquetteRightTargetLaw
    ; plaquetteTopEdgeSourceLaw =
        SFGC.sfgcSite2DPlaquetteTopSourceLaw
    ; plaquetteTopEdgeTargetLaw =
        SFGC.sfgcSite2DPlaquetteTopTargetLaw
    ; plaquetteLeftEdgeSourceLaw =
        SFGC.sfgcSite2DPlaquetteLeftSourceLaw
    ; plaquetteLeftEdgeTargetLaw =
        SFGC.sfgcSite2DPlaquetteLeftTargetLaw
    ; exactClosedDiagnostic =
        "directedEdgeSchema : identity/oriented edge source-target laws and plaquette boundary edge laws are all closed on SFGCSite2D"
    ; schemaBoundary =
        "First diagnostic closed: inspected the SFGC shift-edge to directed-edge schema before additional plaquette arithmetic work"
        ∷ "Identity, p2-oriented, and p3-oriented edge source/target laws are now carried together in one typed report"
        ∷ "Plaquette boundary orientation is explicit: bottom/right/top/left edges each close source and target endpoint laws"
        ∷ "This is a schema-level closure only; it does not inhabit non-flat transport covariance or Yang-Mills equation laws"
        ∷ []
    }

canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate :
  SFGCPathTransportPrimitive
canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate =
  compileSuppliedLinkFibreFieldStrengthTransport
    canonicalYMSFGCSuppliedEdgeProbeFieldStrengthTransportInterface

record YMSFGCSuppliedLinkFibreTransportCompilerReceipt : Set₁ where
  field
    suppliedLinkFibreTransportInterface :
      SFGCSuppliedLinkFibreFieldStrengthTransportInterface

    suppliedLinkFibreTransportInterfaceIsCanonical :
      suppliedLinkFibreTransportInterface
      ≡
      canonicalYMSFGCSuppliedEdgeProbeFieldStrengthTransportInterface

    compiledPathTransportPrimitive :
      SFGCPathTransportPrimitive

    compiledPathTransportPrimitiveIsCanonicalCandidate :
      compiledPathTransportPrimitive
      ≡
      canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate

    compilerPromoted :
      Bool

    compilerPromotedIsFalse :
      compilerPromoted ≡ false

    compilerBoundary :
      List String

canonicalYMSFGCSuppliedLinkFibreTransportCompilerReceipt :
  YMSFGCSuppliedLinkFibreTransportCompilerReceipt
canonicalYMSFGCSuppliedLinkFibreTransportCompilerReceipt =
  record
    { suppliedLinkFibreTransportInterface =
        canonicalYMSFGCSuppliedEdgeProbeFieldStrengthTransportInterface
    ; suppliedLinkFibreTransportInterfaceIsCanonical =
        refl
    ; compiledPathTransportPrimitive =
        compileSuppliedLinkFibreFieldStrengthTransport
          canonicalYMSFGCSuppliedEdgeProbeFieldStrengthTransportInterface
    ; compiledPathTransportPrimitiveIsCanonicalCandidate =
        refl
    ; compilerPromoted =
        false
    ; compilerPromotedIsFalse =
        refl
    ; compilerBoundary =
        "Compiler added: a supplied link/fibre field-strength transport interface now lowers to SFGCPathTransportPrimitive"
        ∷ "Canonical supplied interface uses SFGCSite2DEdge and constant selected field-strength fibres"
        ∷ "The compiled primitive is exactly the existing edge-sensitive lower candidate"
        ∷ "No real gauge-compatibility proof is constructed; the law remains a requested compatibility surface"
        ∷ "Yang-Mills promotion remains false"
        ∷ []
    }

canonicalYMSFGCDegenerateCovariantDifferencePrimitiveCandidate :
  CovariantDifferencePrimitive
    canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate
canonicalYMSFGCDegenerateCovariantDifferencePrimitiveCandidate =
  record
    { CovariantDifferenceCarrier =
        SFGC.SFGCSite2DFieldStrengthBridge
    ; zeroCovariantDifference =
        SFGC.sfgcSite2DFieldStrengthFromCurvature
          SFGC.sfgcSite2DZero2Form
    ; covariantDifference =
        sfgcEdgeTransportCovariantDifferenceCandidate
    ; flatConnectionExtendsSelectedExteriorDerivative =
        λ form →
          sfgcSelectedFlatConnectionExteriorExtensionCandidate form
          ≡
          SFGC.sfgcSite2Dδ₀ form
    ; covariantDifferenceGaugeCompatibilityLaw =
        λ gauge A fieldStrength →
          sfgcEdgeTransportCovariantDifferenceCandidate
            (SFGC.transformGauge gauge A)
            fieldStrength
          ≡
          sfgcEdgeTransportCovariantDifferenceCandidate A fieldStrength
    ; covariantBianchiTargetLaw =
        λ A →
          sfgcEdgeTransportCovariantDifferenceCandidate A
            (SFGC.sfgcSite2DFieldStrengthFromCurvature
              SFGC.sfgcSite2DZero2Form)
          ≡
          SFGC.sfgcSite2DFieldStrengthFromCurvature
            SFGC.sfgcSite2DZero2Form
    ; primitiveBoundary =
        "Non-promoting candidate: covariantDifference uses A at shiftStartPoint to select a reference SFGCSite2DEdge, then applies the edge-sensitive field-strength transport to the input bridge"
        ∷ "It inhabits the requested carrier shape and no longer ignores A, but it is not a derived Yang-Mills covariant derivative"
        ∷ "Blocked from promotion by missing link/fiber parallel transport, covariant-difference laws, and gauge-compatibility proofs"
        ∷ []
    }

canonicalYMSFGCPhaseZeroQuadraticDensityPrimitiveCandidate :
  GaugeInvariantQuadraticDensityPrimitive
    canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate
canonicalYMSFGCPhaseZeroQuadraticDensityPrimitiveCandidate =
  record
    { DensityScalar =
        ℤ
    ; density =
        sfgcPhaseZeroQuadraticDensity
    ; nonconstantWitness =
        YMSFGCPhaseZeroDensityNonconstantWitness
    ; gaugeInvariantDensityLaw =
        λ gauge fieldStrength plaquette →
          sfgcPhaseZeroQuadraticDensity fieldStrength plaquette
          ≡
          sfgcPhaseZeroQuadraticDensity fieldStrength plaquette
    ; traceOrKillingPairingLaw =
        λ fieldStrength plaquette →
          sfgcPhaseZeroQuadraticDensity fieldStrength plaquette
          ≡
          sfgcPhaseZeroQuadraticDensity fieldStrength plaquette
    ; primitiveBoundary =
        "Lower candidate: density pairs the selected Wilson-loop phase with φ0 using SPTI4.phaseKernel4"
        ∷ "Nonconstant witness distinguishes φ0 and φ1 constant field-strength bridge values"
        ∷ "Blocked from promotion: gauge invariance and trace/Killing pairing remain law surfaces, not real Yang-Mills proofs"
        ∷ []
    }

sfgcDegenerateCovariantDifferencePrimitiveFlatConnectionExtendsSelectedExteriorDerivative :
  (form : SFGC.SFGCSite2DDiscrete0Form) →
  CovariantDifferencePrimitive.flatConnectionExtendsSelectedExteriorDerivative
    canonicalYMSFGCDegenerateCovariantDifferencePrimitiveCandidate
    form
sfgcDegenerateCovariantDifferencePrimitiveFlatConnectionExtendsSelectedExteriorDerivative form =
  sfgcSelectedFlatConnectionExteriorExtensionCandidateLaw form

canonicalYMSFGCSinglePlaquetteYMActionPrimitiveCandidate :
  DiscreteYMActionPrimitive
    canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate
    canonicalYMSFGCPhaseZeroQuadraticDensityPrimitiveCandidate
canonicalYMSFGCSinglePlaquetteYMActionPrimitiveCandidate =
  record
    { ActionScalar =
        ℤ
    ; plaquetteDomain =
        SFGC.SFGCSite2DPlaquette
    ; plaquetteWeight =
        λ plaquette densityValue → densityValue
    ; plaquetteOf =
        λ plaquette → plaquette
    ; integrateDensity =
        λ fieldStrength plaquette →
          sfgcPhaseZeroQuadraticDensity fieldStrength plaquette
    ; variationalPairing =
        λ A → SFGC.GaugeField
    ; eulerLagrangeDStarFEqualsJTarget =
        λ A → YangMillsVariationalEquationMissingPrimitive
    ; primitiveBoundary =
        "Degenerate non-promoting candidate: integrateDensity evaluates one plaquette-domain point, with identity weight"
        ∷ "This is not a plaquette sum over a lattice domain and carries no variational Euler-Lagrange proof"
        ∷ "Blocked from promotion by missing integration, variation pairing, Hodge star, source coupling, and D * F = J derivation"
        ∷ []
    }

record YMSFGCDiscreteVariationIBPLowerCandidate : Set where
  field
    variationOfAction :
      SFGC.GaugeField →
      SFGC.GaugeField →
      ℤ

    variationOfActionIsZero :
      variationOfAction
      ≡
      sfgcZeroVariationOfAction

    eulerLagrangePairing :
      SFGC.GaugeField →
      SFGC.GaugeField →
      ℤ

    eulerLagrangePairingIsZero :
      eulerLagrangePairing
      ≡
      sfgcZeroEulerLagrangePairing

    boundaryTerm :
      SFGC.GaugeField →
      SFGC.GaugeField →
      ℤ

    boundaryTermIsZero :
      boundaryTerm
      ≡
      sfgcZeroBoundaryTerm

    zeroIBPLaw :
      (A δA : SFGC.GaugeField) →
      variationOfAction A δA
        ≡
      _+ℤ_
        (eulerLagrangePairing A δA)
        (boundaryTerm A δA)

    candidateBoundary :
      List String

canonicalYMSFGCDiscreteVariationIBPLowerCandidate :
  YMSFGCDiscreteVariationIBPLowerCandidate
canonicalYMSFGCDiscreteVariationIBPLowerCandidate =
  record
    { variationOfAction =
        sfgcZeroVariationOfAction
    ; variationOfActionIsZero =
        refl
    ; eulerLagrangePairing =
        sfgcZeroEulerLagrangePairing
    ; eulerLagrangePairingIsZero =
        refl
    ; boundaryTerm =
        sfgcZeroBoundaryTerm
    ; boundaryTermIsZero =
        refl
    ; zeroIBPLaw =
        sfgcZeroDiscreteVariationIBPLaw
    ; candidateBoundary =
        "Degenerate lower candidate: zero variation splits as zero Euler-Lagrange pairing plus zero boundary term"
        ∷ "This discharges only the algebraic shape of the discrete IBP equation for the zero proxy"
        ∷ "It is not a variation of the single-plaquette action and does not derive D * F = J"
        ∷ []
    }

YMSFGCFullHolonomyConjugationLawType :
  Set
YMSFGCFullHolonomyConjugationLawType =
  (gauge : SFGS.GaugeTransform) →
  (A : SFGC.GaugeField) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    (sfgcSelectedFieldStrengthBridge
      (SFGC.transformGauge gauge A))
    plaquette
    ≡
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    (sfgcSelectedFieldStrengthAdjointTransportCandidate
      gauge
      (sfgcSelectedFieldStrengthBridge A))
    plaquette

YMSFGCFullKillingAdInvarianceLawType :
  Set
YMSFGCFullKillingAdInvarianceLawType =
  (density :
    SFGC.SFGCSite2DFieldStrengthBridge →
    SFGC.SFGCSite2DPlaquette →
    ℤ) →
  (gauge : SFGS.GaugeTransform) →
  (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  density
    (sfgcSelectedFieldStrengthAdjointTransportCandidate
      gauge fieldStrength)
    plaquette
    ≡
  density fieldStrength plaquette

YMSFGCFullDiscreteVariationIBPLawType :
  Set
YMSFGCFullDiscreteVariationIBPLawType =
  (variationOfAction :
    SFGC.GaugeField →
    SFGC.GaugeField →
    ℤ) →
  (eulerLagrangePairing :
    SFGC.GaugeField →
    SFGC.GaugeField →
    ℤ) →
  (boundaryTerm :
    SFGC.GaugeField →
    SFGC.GaugeField →
    ℤ) →
  (A δA : SFGC.GaugeField) →
  variationOfAction A δA
    ≡
  _+ℤ_
    (eulerLagrangePairing A δA)
    (boundaryTerm A δA)

sfgcSelectedEndpointGaugeFactor :
  SFGS.GaugeTransform →
  SFGC.SFGCSite2D →
  SPTI4.Phase4
sfgcSelectedEndpointGaugeFactor gauge site =
  gauge (SFGC.sfgcSite2DPrimaryCoordinate site)

sfgcPhase4ConjugateBy :
  SPTI4.Phase4 →
  SPTI4.Phase4 →
  SPTI4.Phase4
sfgcPhase4ConjugateBy endpoint holonomy =
  holonomy

sfgcPhase4ConjugateZero :
  (endpoint : SPTI4.Phase4) →
  sfgcPhase4ConjugateBy endpoint SPTI4.φ0
  ≡
  SPTI4.φ0
sfgcPhase4ConjugateZero SPTI4.φ0 = refl
sfgcPhase4ConjugateZero SPTI4.φ1 = refl
sfgcPhase4ConjugateZero SPTI4.φ2 = refl
sfgcPhase4ConjugateZero SPTI4.φ3 = refl

sfgcSelectedEndpointConjugatedWilsonLoopZero :
  (gauge : SFGS.GaugeTransform) →
  (A : SFGC.GaugeField) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  sfgcPhase4ConjugateBy
    (sfgcSelectedEndpointGaugeFactor
      gauge
      (SFGC.sfgcSite2DPlaquetteSW plaquette))
    (SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
      (sfgcSelectedFieldStrengthBridge A)
      plaquette)
  ≡
  SPTI4.φ0
sfgcSelectedEndpointConjugatedWilsonLoopZero gauge A plaquette =
  trans
    (cong
      (sfgcPhase4ConjugateBy
        (sfgcSelectedEndpointGaugeFactor
          gauge
          (SFGC.sfgcSite2DPlaquetteSW plaquette)))
      (sfgcSelectedWilsonLoopPhaseZero A plaquette))
    (sfgcPhase4ConjugateZero
      (sfgcSelectedEndpointGaugeFactor
        gauge
        (SFGC.sfgcSite2DPlaquetteSW plaquette)))

sfgcSelectedEndpointPlaquetteConjugationLaw :
  (gauge : SFGS.GaugeTransform) →
  (A : SFGC.GaugeField) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    (sfgcSelectedFieldStrengthBridge
      (SFGC.transformGauge gauge A))
    plaquette
  ≡
  sfgcPhase4ConjugateBy
    (sfgcSelectedEndpointGaugeFactor
      gauge
      (SFGC.sfgcSite2DPlaquetteSW plaquette))
    (SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
      (sfgcSelectedFieldStrengthBridge A)
      plaquette)
sfgcSelectedEndpointPlaquetteConjugationLaw gauge A plaquette =
  trans
    (sfgcSelectedWilsonLoopPhaseZero
      (SFGC.transformGauge gauge A)
      plaquette)
    (symEq
      (sfgcSelectedEndpointConjugatedWilsonLoopZero
        gauge A plaquette))

sfgcEndpointPhaseAdjointAction :
  SFGS.GaugeTransform →
  SFGC.SFGCSite2D →
  YMSFGCLocalFiniteLie3Carrier →
  YMSFGCLocalFiniteLie3Carrier
sfgcEndpointPhaseAdjointAction gauge site =
  localFiniteLie3PhaseAdjointAction
    (sfgcSelectedEndpointGaugeFactor gauge site)

sfgcEndpointPhaseAdjointTraceAdInvariance :
  (gauge : SFGS.GaugeTransform) →
  (site : SFGC.SFGCSite2D) →
  (x y : YMSFGCLocalFiniteLie3Carrier) →
  localFiniteLie3TracePairing
    (sfgcEndpointPhaseAdjointAction gauge site x)
    (sfgcEndpointPhaseAdjointAction gauge site y)
  ≡
  localFiniteLie3TracePairing x y
sfgcEndpointPhaseAdjointTraceAdInvariance gauge site =
  localFiniteLie3PhaseAdjointTraceAdInvariance
    (sfgcSelectedEndpointGaugeFactor gauge site)

sfgcSelectedEndpointGaugeFactorAtEdgeSource :
  SFGS.GaugeTransform →
  SFGC.SFGCSite2DEdge →
  SPTI4.Phase4
sfgcSelectedEndpointGaugeFactorAtEdgeSource gauge edge =
  sfgcSelectedEndpointGaugeFactor
    gauge
    (SFGC.sfgcSite2DEdgeSourceTotal edge)

sfgcSelectedEndpointGaugeFactorAtEdgeTarget :
  SFGS.GaugeTransform →
  SFGC.SFGCSite2DEdge →
  SPTI4.Phase4
sfgcSelectedEndpointGaugeFactorAtEdgeTarget gauge edge =
  sfgcSelectedEndpointGaugeFactor
    gauge
    (SFGC.sfgcSite2DEdgeTargetTotal edge)

sfgcSelectedBottomSourceEndpointGaugeFactorIsSW :
  (gauge : SFGS.GaugeTransform) →
  (base : SFGC.SFGCSite2D) →
  sfgcSelectedEndpointGaugeFactorAtEdgeSource
    gauge
    (SFGC.sfgcSite2DPlaquetteBottomEdge
      (SFGC.sfgcSite2DPlaquetteAt base))
  ≡
  sfgcSelectedEndpointGaugeFactor
    gauge
    (SFGC.sfgcSite2DPlaquetteSW
      (SFGC.sfgcSite2DPlaquetteAt base))
sfgcSelectedBottomSourceEndpointGaugeFactorIsSW gauge base =
  cong
    (sfgcSelectedEndpointGaugeFactor gauge)
    (SFGC.sfgcSite2DPlaquetteBottomSourceLaw base)

sfgcSelectedLeftSourceEndpointGaugeFactorIsSW :
  (gauge : SFGS.GaugeTransform) →
  (base : SFGC.SFGCSite2D) →
  sfgcSelectedEndpointGaugeFactorAtEdgeSource
    gauge
    (SFGC.sfgcSite2DPlaquetteLeftEdge
      (SFGC.sfgcSite2DPlaquetteAt base))
  ≡
  sfgcSelectedEndpointGaugeFactor
    gauge
    (SFGC.sfgcSite2DPlaquetteSW
      (SFGC.sfgcSite2DPlaquetteAt base))
sfgcSelectedLeftSourceEndpointGaugeFactorIsSW gauge base =
  cong
    (sfgcSelectedEndpointGaugeFactor gauge)
    (SFGC.sfgcSite2DPlaquetteLeftSourceLaw base)

record YMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt : Set₁ where
  field
    endpointGaugeFactor :
      SFGS.GaugeTransform →
      SFGC.SFGCSite2D →
      SPTI4.Phase4

    endpointGaugeFactorIsSelectedPrimaryCoordinate :
      endpointGaugeFactor
      ≡
      sfgcSelectedEndpointGaugeFactor

    edgeSourceEndpointGaugeFactor :
      SFGS.GaugeTransform →
      SFGC.SFGCSite2DEdge →
      SPTI4.Phase4

    edgeSourceEndpointGaugeFactorIsSelected :
      edgeSourceEndpointGaugeFactor
      ≡
      sfgcSelectedEndpointGaugeFactorAtEdgeSource

    edgeTargetEndpointGaugeFactor :
      SFGS.GaugeTransform →
      SFGC.SFGCSite2DEdge →
      SPTI4.Phase4

    edgeTargetEndpointGaugeFactorIsSelected :
      edgeTargetEndpointGaugeFactor
      ≡
      sfgcSelectedEndpointGaugeFactorAtEdgeTarget

    bottomSourceEndpointGaugeFactorIsSW :
      (gauge : SFGS.GaugeTransform) →
      (base : SFGC.SFGCSite2D) →
      sfgcSelectedEndpointGaugeFactorAtEdgeSource
        gauge
        (SFGC.sfgcSite2DPlaquetteBottomEdge
          (SFGC.sfgcSite2DPlaquetteAt base))
      ≡
      sfgcSelectedEndpointGaugeFactor
        gauge
        (SFGC.sfgcSite2DPlaquetteSW
          (SFGC.sfgcSite2DPlaquetteAt base))

    bottomSourceEndpointGaugeFactorIsSWCanonical :
      Bool

    leftSourceEndpointGaugeFactorIsSW :
      (gauge : SFGS.GaugeTransform) →
      (base : SFGC.SFGCSite2D) →
      sfgcSelectedEndpointGaugeFactorAtEdgeSource
        gauge
        (SFGC.sfgcSite2DPlaquetteLeftEdge
          (SFGC.sfgcSite2DPlaquetteAt base))
      ≡
      sfgcSelectedEndpointGaugeFactor
        gauge
        (SFGC.sfgcSite2DPlaquetteSW
          (SFGC.sfgcSite2DPlaquetteAt base))

    leftSourceEndpointGaugeFactorIsSWCanonical :
      Bool

    receiptPromoted :
      Bool

    receiptPromotedIsFalse :
      receiptPromoted ≡ false

    receiptBoundary :
      List String

canonicalYMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt :
  YMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt
canonicalYMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt =
  record
    { endpointGaugeFactor =
        sfgcSelectedEndpointGaugeFactor
    ; endpointGaugeFactorIsSelectedPrimaryCoordinate =
        refl
    ; edgeSourceEndpointGaugeFactor =
        sfgcSelectedEndpointGaugeFactorAtEdgeSource
    ; edgeSourceEndpointGaugeFactorIsSelected =
        refl
    ; edgeTargetEndpointGaugeFactor =
        sfgcSelectedEndpointGaugeFactorAtEdgeTarget
    ; edgeTargetEndpointGaugeFactorIsSelected =
        refl
    ; bottomSourceEndpointGaugeFactorIsSW =
        sfgcSelectedBottomSourceEndpointGaugeFactorIsSW
    ; bottomSourceEndpointGaugeFactorIsSWCanonical =
        true
    ; leftSourceEndpointGaugeFactorIsSW =
        sfgcSelectedLeftSourceEndpointGaugeFactorIsSW
    ; leftSourceEndpointGaugeFactorIsSWCanonical =
        true
    ; receiptPromoted =
        false
    ; receiptPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Exposes concrete Phase4 endpoint gauge factors at every SFGCSite2DEdge source and target"
        ∷ "The plaquette SW endpoint is now tied to the bottom-edge source and left-edge source by SFGC source laws"
        ∷ "This is still the selected flat Phase4 endpoint surface, not a user-supplied real non-flat holonomy carrier"
        ∷ "Non-flat curvature and non-flat plaquette holonomy conjugation remain unconstructed"
        ∷ []
    }

sfgcPhaseToLocalFiniteLie3 :
  SPTI4.Phase4 →
  YMSFGCLocalFiniteLie3Carrier
sfgcPhaseToLocalFiniteLie3 SPTI4.φ0 = lieZero
sfgcPhaseToLocalFiniteLie3 SPTI4.φ1 = lieBasis signPos axisX
sfgcPhaseToLocalFiniteLie3 SPTI4.φ2 = lieBasis signPos axisY
sfgcPhaseToLocalFiniteLie3 SPTI4.φ3 = lieBasis signPos axisZ

sfgcSelectedConstantPhi1GaugeField :
  SFGC.GaugeField
sfgcSelectedConstantPhi1GaugeField _ =
  SPTI4.φ1

sfgcSelectedConnectionOneFormAsLocalFiniteLie3 :
  SFGC.GaugeField →
  YMSFGCLocalFiniteLie3Carrier
sfgcSelectedConnectionOneFormAsLocalFiniteLie3 A =
  sfgcPhaseToLocalFiniteLie3 (A SPTI.shiftStartPoint)

sfgcSelectedConnectionOneFormAsLocalFiniteSU3 :
  SFGC.GaugeField →
  YMSFGCLocalFiniteSU3Carrier
sfgcSelectedConnectionOneFormAsLocalFiniteSU3 A =
  localFiniteSU3Embed
    (sfgcSelectedConnectionOneFormAsLocalFiniteLie3 A)

sfgcSelectedConnectionOneFormAsLocalFiniteLie3Nonzero :
  sfgcSelectedConnectionOneFormAsLocalFiniteLie3
    sfgcSelectedConstantPhi1GaugeField
  ≡
  lieBasis signPos axisX
sfgcSelectedConnectionOneFormAsLocalFiniteLie3Nonzero =
  refl

sfgcSelectedConnectionOneFormAsLocalFiniteSU3Nonzero :
  sfgcSelectedConnectionOneFormAsLocalFiniteSU3
    sfgcSelectedConstantPhi1GaugeField
  ≡
  localFiniteSU3Embed (lieBasis signPos axisX)
sfgcSelectedConnectionOneFormAsLocalFiniteSU3Nonzero =
  refl

record YMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt : Set₁ where
  field
    localFibreLieAlgebraCarrier :
      Set

    localFibreLieAlgebraCarrierIsFiniteLie3 :
      localFibreLieAlgebraCarrier
      ≡
      YMSFGCLocalFiniteLie3Carrier

    connectionOneFormAsFibreAlgebra :
      SFGC.GaugeField →
      YMSFGCLocalFiniteLie3Carrier

    connectionOneFormAsFibreAlgebraIsSelectedPhaseMap :
      connectionOneFormAsFibreAlgebra
      ≡
      sfgcSelectedConnectionOneFormAsLocalFiniteLie3

    connectionOneFormAsLocalSU3Fibre :
      SFGC.GaugeField →
      YMSFGCLocalFiniteSU3Carrier

    connectionOneFormAsLocalSU3FibreIsEmbedded :
      connectionOneFormAsLocalSU3Fibre
      ≡
      sfgcSelectedConnectionOneFormAsLocalFiniteSU3

    nonzeroConnectionProbe :
      sfgcSelectedConnectionOneFormAsLocalFiniteLie3
        sfgcSelectedConstantPhi1GaugeField
      ≡
      lieBasis signPos axisX

    nonzeroConnectionProbeIsCanonical :
      Bool

    nonzeroSU3ConnectionProbe :
      sfgcSelectedConnectionOneFormAsLocalFiniteSU3
        sfgcSelectedConstantPhi1GaugeField
      ≡
      localFiniteSU3Embed (lieBasis signPos axisX)

    nonzeroSU3ConnectionProbeIsCanonical :
      Bool

    receiptPromoted :
      Bool

    receiptPromotedIsFalse :
      receiptPromoted ≡ false

    receiptBoundary :
      List String

canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt :
  YMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt
canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt =
  record
    { localFibreLieAlgebraCarrier =
        YMSFGCLocalFiniteLie3Carrier
    ; localFibreLieAlgebraCarrierIsFiniteLie3 =
        refl
    ; connectionOneFormAsFibreAlgebra =
        sfgcSelectedConnectionOneFormAsLocalFiniteLie3
    ; connectionOneFormAsFibreAlgebraIsSelectedPhaseMap =
        refl
    ; connectionOneFormAsLocalSU3Fibre =
        sfgcSelectedConnectionOneFormAsLocalFiniteSU3
    ; connectionOneFormAsLocalSU3FibreIsEmbedded =
        refl
    ; nonzeroConnectionProbe =
        sfgcSelectedConnectionOneFormAsLocalFiniteLie3Nonzero
    ; nonzeroConnectionProbeIsCanonical =
        true
    ; nonzeroSU3ConnectionProbe =
        sfgcSelectedConnectionOneFormAsLocalFiniteSU3Nonzero
    ; nonzeroSU3ConnectionProbeIsCanonical =
        true
    ; receiptPromoted =
        false
    ; receiptPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Local receipt: maps the selected SFGC GaugeField start-point Phase4 value into the local finite Lie3 fibre algebra"
        ∷ "The same local connection one-form is embedded into the finite SU3 scaffold via localFiniteSU3Embed"
        ∷ "The constant phi1 probe is nonzero, so this is not the previous all-zero connection-one-form probe"
        ∷ "The user-supplied non-flat connection carrier is inhabited separately by the SFGC 1-form adapter; this local finite Lie3 map still does not supply the requested real connectionOneFormAsFibreAlgebra law"
        ∷ "D_A = d + [A,_] and D_A^2 = [F_A,_] remain non-promoting until the strict non-flat holonomy, transport, and supplied fibre laws are inhabited"
        ∷ []
    }

sfgcArbitraryGaugeHolonomyConjugation :
  YMSFGCFullHolonomyConjugationLawType
sfgcArbitraryGaugeHolonomyConjugation gauge A plaquette =
  trans
    (sfgcSelectedWilsonLoopPhaseZero
      (SFGC.transformGauge gauge A)
      plaquette)
    (symEq
      (sfgcSelectedWilsonLoopPhaseZero A plaquette))

sfgcTrivialC4AdjointArbitraryDensityInvariant :
  YMSFGCFullKillingAdInvarianceLawType
sfgcTrivialC4AdjointArbitraryDensityInvariant
  density gauge fieldStrength plaquette =
  refl

record YMSFGCRealKillingAdInvarianceIrreducibilityLedger : Set₁ where
  field
    selectedGaugePhaseCarrier :
      Set

    selectedGaugePhaseCarrierIsPhase4 :
      selectedGaugePhaseCarrier ≡ SPTI4.Phase4

    selectedAdjointAction :
      SFGS.GaugeTransform →
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    selectedAdjointActionIsTrivialC4 :
      selectedAdjointAction
      ≡
      sfgcSelectedFieldStrengthAdjointTransportCandidate

    arbitraryDensityInvariantUnderSelectedAdjoint :
      YMSFGCFullKillingAdInvarianceLawType

    exactIrreducibility :
      List YMSFGCRealKillingAdInvarianceIrreducibility

    exactIrreducibilityIsCanonical :
      exactIrreducibility
      ≡
      canonicalYMSFGCRealKillingAdInvarianceIrreducibility

    realKillingAdInvarianceConstructed :
      Bool

    realKillingAdInvarianceConstructedIsFalse :
      realKillingAdInvarianceConstructed ≡ false

    ledgerBoundary :
      List String

canonicalYMSFGCRealKillingAdInvarianceIrreducibilityLedger :
  YMSFGCRealKillingAdInvarianceIrreducibilityLedger
canonicalYMSFGCRealKillingAdInvarianceIrreducibilityLedger =
  record
    { selectedGaugePhaseCarrier =
        SPTI4.Phase4
    ; selectedGaugePhaseCarrierIsPhase4 =
        refl
    ; selectedAdjointAction =
        sfgcSelectedFieldStrengthAdjointTransportCandidate
    ; selectedAdjointActionIsTrivialC4 =
        refl
    ; arbitraryDensityInvariantUnderSelectedAdjoint =
        sfgcTrivialC4AdjointArbitraryDensityInvariant
    ; exactIrreducibility =
        canonicalYMSFGCRealKillingAdInvarianceIrreducibility
    ; exactIrreducibilityIsCanonical =
        refl
    ; realKillingAdInvarianceConstructed =
        false
    ; realKillingAdInvarianceConstructedIsFalse =
        refl
    ; ledgerBoundary =
        "The selected finite C4 adjoint action is identity on SFGCSite2DFieldStrengthBridge, so arbitrary-density invariance is definitional"
        ∷ "That definitional invariant is not a Killing-form theorem: no Lie algebra carrier is exposed for the selected gauge sector"
        ∷ "No nontrivial Ad action, Killing/trace pairing, or Ad-invariance proof is exported by SFGC or SFGS"
        ∷ "Therefore a real Killing Ad-invariance law cannot be constructed from the current fields"
        ∷ []
    }

record YMSFGCNonFlatHolonomyConjugationIrreducibilityLedger : Set₁ where
  field
    arbitraryGaugeHolonomyConjugationClosedForSelectedFlatSurface :
      YMSFGCFullHolonomyConjugationLawType

    selectedWilsonLoopPhaseZero :
      (A : SFGC.GaugeField) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        (sfgcSelectedFieldStrengthBridge A)
        plaquette
      ≡
      SPTI4.φ0

    exactNonFlatIrreducibility :
      List YMSFGCNonFlatHolonomyConjugationIrreducibility

    exactNonFlatIrreducibilityIsCanonical :
      exactNonFlatIrreducibility
      ≡
      canonicalYMSFGCNonFlatHolonomyConjugationIrreducibility

    nonFlatHolonomyConjugationConstructed :
      Bool

    nonFlatHolonomyConjugationConstructedIsFalse :
      nonFlatHolonomyConjugationConstructed ≡ false

    ledgerBoundary :
      List String

canonicalYMSFGCNonFlatHolonomyConjugationIrreducibilityLedger :
  YMSFGCNonFlatHolonomyConjugationIrreducibilityLedger
canonicalYMSFGCNonFlatHolonomyConjugationIrreducibilityLedger =
  record
    { arbitraryGaugeHolonomyConjugationClosedForSelectedFlatSurface =
        sfgcArbitraryGaugeHolonomyConjugation
    ; selectedWilsonLoopPhaseZero =
        sfgcSelectedWilsonLoopPhaseZero
    ; exactNonFlatIrreducibility =
        canonicalYMSFGCNonFlatHolonomyConjugationIrreducibility
    ; exactNonFlatIrreducibilityIsCanonical =
        refl
    ; nonFlatHolonomyConjugationConstructed =
        false
    ; nonFlatHolonomyConjugationConstructedIsFalse =
        refl
    ; ledgerBoundary =
        "Arbitrary-gauge holonomy conjugation is closed for the currently selected SFGC surface because every selected plaquette Wilson-loop phase reduces to φ0"
        ∷ "This is an honest arbitrary-gauge law for the current definitions, but it is a flat finite-C4 cancellation law"
        ∷ "A non-flat Yang-Mills holonomy-conjugation theorem still needs non-flat plaquette curvature, endpoint gauge factors, and nontrivial field-strength Ad action"
        ∷ "No non-flat Yang-Mills holonomy promotion follows from the selected flat cancellation"
        ∷ []
    }

data YMSFGCArbitraryGaugeFinalLawAttemptStatus : Set where
  arbitraryHolonomyClosedKillingIrreducibleBeyondTrivialC4 :
    YMSFGCArbitraryGaugeFinalLawAttemptStatus

record YMSFGCArbitraryGaugeHolonomyKillingAttempt : Set₁ where
  field
    status :
      YMSFGCArbitraryGaugeFinalLawAttemptStatus

    arbitraryGaugeHolonomyConjugation :
      YMSFGCFullHolonomyConjugationLawType

    nonFlatHolonomyConjugationIrreducibilityLedger :
      YMSFGCNonFlatHolonomyConjugationIrreducibilityLedger

    nonFlatHolonomyConjugationIrreducibilityLedgerIsCanonical :
      nonFlatHolonomyConjugationIrreducibilityLedger
      ≡
      canonicalYMSFGCNonFlatHolonomyConjugationIrreducibilityLedger

    trivialC4AdjointDensityInvariance :
      YMSFGCFullKillingAdInvarianceLawType

    realKillingAdInvarianceIrreducibilityLedger :
      YMSFGCRealKillingAdInvarianceIrreducibilityLedger

    realKillingAdInvarianceIrreducibilityLedgerIsCanonical :
      realKillingAdInvarianceIrreducibilityLedger
      ≡
      canonicalYMSFGCRealKillingAdInvarianceIrreducibilityLedger

    holonomyLawClosed :
      Bool

    holonomyLawClosedIsTrue :
      holonomyLawClosed ≡ true

    realKillingLawClosed :
      Bool

    realKillingLawClosedIsFalse :
      realKillingLawClosed ≡ false

    attemptBoundary :
      List String

canonicalYMSFGCArbitraryGaugeHolonomyKillingAttempt :
  YMSFGCArbitraryGaugeHolonomyKillingAttempt
canonicalYMSFGCArbitraryGaugeHolonomyKillingAttempt =
  record
    { status =
        arbitraryHolonomyClosedKillingIrreducibleBeyondTrivialC4
    ; arbitraryGaugeHolonomyConjugation =
        sfgcArbitraryGaugeHolonomyConjugation
    ; nonFlatHolonomyConjugationIrreducibilityLedger =
        canonicalYMSFGCNonFlatHolonomyConjugationIrreducibilityLedger
    ; nonFlatHolonomyConjugationIrreducibilityLedgerIsCanonical =
        refl
    ; trivialC4AdjointDensityInvariance =
        sfgcTrivialC4AdjointArbitraryDensityInvariant
    ; realKillingAdInvarianceIrreducibilityLedger =
        canonicalYMSFGCRealKillingAdInvarianceIrreducibilityLedger
    ; realKillingAdInvarianceIrreducibilityLedgerIsCanonical =
        refl
    ; holonomyLawClosed =
        true
    ; holonomyLawClosedIsTrue =
        refl
    ; realKillingLawClosed =
        false
    ; realKillingLawClosedIsFalse =
        refl
    ; attemptBoundary =
        "Closed: arbitrary gauge transform and arbitrary selected SFGC GaugeField have equal selected plaquette holonomy after transform, because both sides reduce to φ0"
        ∷ "Not promoted: the closed holonomy law is a flat finite-C4 cancellation over the selected SFGCSite2D connectionTo1Form"
        ∷ "Only trivial-C4 density invariance is available for Ad: the selected adjoint action is identity"
        ∷ "A real Killing Ad-invariance theorem remains irreducible from current SFGC/SFGS fields"
        ∷ []
    }

record YMSFGCFinalPrimitiveLowerLawCandidate : Set₁ where
  field
    constantGaugeVacuumHolonomyConjugation :
      (phase : SPTI4.Phase4) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        (sfgcSelectedFieldStrengthBridge
          (SFGC.transformGauge
            (SFGS.constantGaugeTransform phase)
            SFGC.vacuumGaugeField))
        plaquette
        ≡
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        (sfgcSelectedFieldStrengthAdjointTransportCandidate
          (SFGS.constantGaugeTransform phase)
          (sfgcSelectedFieldStrengthBridge SFGC.vacuumGaugeField))
        plaquette

    phaseZeroDensityTrivialAdjointInvariant :
      (gauge : SFGS.GaugeTransform) →
      (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      sfgcPhaseZeroQuadraticDensity
        (sfgcSelectedFieldStrengthAdjointTransportCandidate
          gauge fieldStrength)
        plaquette
        ≡
      sfgcPhaseZeroQuadraticDensity fieldStrength plaquette

    zeroVariationIBPCandidate :
      YMSFGCDiscreteVariationIBPLowerCandidate

    zeroVariationIBPCandidateIsCanonical :
      zeroVariationIBPCandidate
      ≡
      canonicalYMSFGCDiscreteVariationIBPLowerCandidate

    arbitraryGaugeHolonomyKillingAttempt :
      YMSFGCArbitraryGaugeHolonomyKillingAttempt

    arbitraryGaugeHolonomyKillingAttemptIsCanonical :
      arbitraryGaugeHolonomyKillingAttempt
      ≡
      canonicalYMSFGCArbitraryGaugeHolonomyKillingAttempt

    remainingHolonomyConjugationLaw :
      Set

    remainingHolonomyConjugationLawIsFull :
      remainingHolonomyConjugationLaw
      ≡
      YMSFGCFullHolonomyConjugationLawType

    remainingKillingAdInvarianceLaw :
      Set

    remainingKillingAdInvarianceLawIsFull :
      remainingKillingAdInvarianceLaw
      ≡
      YMSFGCFullKillingAdInvarianceLawType

    remainingDiscreteVariationIBPLaw :
      Set

    remainingDiscreteVariationIBPLawIsFull :
      remainingDiscreteVariationIBPLaw
      ≡
      YMSFGCFullDiscreteVariationIBPLawType

    finalPrimitiveMathBlockers :
      List YMSFGCFinalPrimitiveMathBlocker

    finalPrimitiveMathBlockersAreCanonical :
      finalPrimitiveMathBlockers
      ≡
      canonicalYMSFGCFinalPrimitiveMathBlockers

    lowerLawCandidatePromoted :
      Bool

    lowerLawCandidatePromotedIsFalse :
      lowerLawCandidatePromoted ≡ false

    lowerLawBoundary :
      List String

canonicalYMSFGCFinalPrimitiveLowerLawCandidate :
  YMSFGCFinalPrimitiveLowerLawCandidate
canonicalYMSFGCFinalPrimitiveLowerLawCandidate =
  record
    { constantGaugeVacuumHolonomyConjugation =
        sfgcConstantGaugeVacuumHolonomyConjugationCandidate
    ; phaseZeroDensityTrivialAdjointInvariant =
        sfgcPhaseZeroDensityTrivialAdjointInvariant
    ; zeroVariationIBPCandidate =
        canonicalYMSFGCDiscreteVariationIBPLowerCandidate
    ; zeroVariationIBPCandidateIsCanonical =
        refl
    ; arbitraryGaugeHolonomyKillingAttempt =
        canonicalYMSFGCArbitraryGaugeHolonomyKillingAttempt
    ; arbitraryGaugeHolonomyKillingAttemptIsCanonical =
        refl
    ; remainingHolonomyConjugationLaw =
        YMSFGCFullHolonomyConjugationLawType
    ; remainingHolonomyConjugationLawIsFull =
        refl
    ; remainingKillingAdInvarianceLaw =
        YMSFGCFullKillingAdInvarianceLawType
    ; remainingKillingAdInvarianceLawIsFull =
        refl
    ; remainingDiscreteVariationIBPLaw =
        YMSFGCFullDiscreteVariationIBPLawType
    ; remainingDiscreteVariationIBPLawIsFull =
        refl
    ; finalPrimitiveMathBlockers =
        canonicalYMSFGCFinalPrimitiveMathBlockers
    ; finalPrimitiveMathBlockersAreCanonical =
        refl
    ; lowerLawCandidatePromoted =
        false
    ; lowerLawCandidatePromotedIsFalse =
        refl
    ; lowerLawBoundary =
        "Discharged lower holonomy case: constant gauge transforms preserve vacuum plaquette field strength under the trivial finite adjoint candidate"
        ∷ "Discharged selected arbitrary holonomy case: every selected SFGCSite2D GaugeField plaquette Wilson-loop phase reduces to φ0 before and after arbitrary SFGS gauge transform"
        ∷ "Discharged lower density case: phase-zero density is invariant under the trivial finite adjoint candidate by refl"
        ∷ "Discharged lower IBP shape: zero variation equals zero Euler-Lagrange pairing plus zero boundary term"
        ∷ "Remaining holonomy blocker is the non-flat arbitrary-gauge, arbitrary-connection conjugation law"
        ∷ "Remaining density blocker is a real Killing/trace Ad-invariance law, not only identity adjoint invariance"
        ∷ "Remaining variational blocker is a real action variation and discrete IBP law for the selected action surface"
        ∷ "These lower laws do not promote Yang-Mills, Maxwell, D * F = J, or D F = 0"
        ∷ []
    }

record YMSFGCExactCanonicalMissingPrimitiveSummary : Set₁ where
  field
    pathTransportPrimitiveCandidate :
      SFGCPathTransportPrimitive

    pathTransportPrimitiveCandidateIsCanonical :
      pathTransportPrimitiveCandidate
      ≡
      canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate

    covariantDifferencePrimitiveCandidate :
      CovariantDifferencePrimitive
        canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate

    covariantDifferencePrimitiveCandidateIsCanonical :
      covariantDifferencePrimitiveCandidate
      ≡
      canonicalYMSFGCDegenerateCovariantDifferencePrimitiveCandidate

    gaugeInvariantQuadraticDensityPrimitiveCandidate :
      GaugeInvariantQuadraticDensityPrimitive
        canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate

    gaugeInvariantQuadraticDensityPrimitiveCandidateIsCanonical :
      gaugeInvariantQuadraticDensityPrimitiveCandidate
      ≡
      canonicalYMSFGCPhaseZeroQuadraticDensityPrimitiveCandidate

    arbitrarySelectedHolonomyCancellation :
      YMSFGCFullHolonomyConjugationLawType

    arbitrarySelectedHolonomyCancellationIsCanonical :
      arbitrarySelectedHolonomyCancellation
      ≡
      sfgcArbitraryGaugeHolonomyConjugation

    trivialAdResidualCancellation :
      YMSFGCFullKillingAdInvarianceLawType

    trivialAdResidualCancellationIsCanonical :
      trivialAdResidualCancellation
      ≡
      sfgcTrivialC4AdjointArbitraryDensityInvariant

    zeroDiscreteIBPExactLaw :
      (A δA : SFGC.GaugeField) →
      sfgcZeroVariationOfAction A δA
        ≡
      _+ℤ_
        (sfgcZeroEulerLagrangePairing A δA)
        (sfgcZeroBoundaryTerm A δA)

    zeroDiscreteIBPExactLawIsCanonical :
      zeroDiscreteIBPExactLaw
      ≡
      sfgcZeroDiscreteVariationIBPLaw

    firstStrictTransportMissingPrimitive :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    firstStrictTransportMissingPrimitiveIsFieldStrengthAction :
      firstStrictTransportMissingPrimitive
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    firstStrictNonFlatHolonomyMissingPrimitive :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictNonFlatHolonomyMissingPrimitiveIsCurvature :
      firstStrictNonFlatHolonomyMissingPrimitive
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    firstStrictKillingMissingPrimitive :
      YMSFGCRealKillingAdInvarianceIrreducibility

    firstStrictKillingMissingPrimitiveIsLieAlgebraCarrier :
      firstStrictKillingMissingPrimitive
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    firstStrictIBPMissingPrimitive :
      YangMillsVariationalEquationMissingPrimitive

    firstStrictIBPMissingPrimitiveIsVariationPairing :
      firstStrictIBPMissingPrimitive
      ≡
      missingVariationPairingForSelectedHodgeStar

    summaryPromoted :
      Bool

    summaryPromotedIsFalse :
      summaryPromoted ≡ false

    summaryBoundary :
      List String

canonicalYMSFGCExactCanonicalMissingPrimitiveSummary :
  YMSFGCExactCanonicalMissingPrimitiveSummary
canonicalYMSFGCExactCanonicalMissingPrimitiveSummary =
  record
    { pathTransportPrimitiveCandidate =
        canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate
    ; pathTransportPrimitiveCandidateIsCanonical =
        refl
    ; covariantDifferencePrimitiveCandidate =
        canonicalYMSFGCDegenerateCovariantDifferencePrimitiveCandidate
    ; covariantDifferencePrimitiveCandidateIsCanonical =
        refl
    ; gaugeInvariantQuadraticDensityPrimitiveCandidate =
        canonicalYMSFGCPhaseZeroQuadraticDensityPrimitiveCandidate
    ; gaugeInvariantQuadraticDensityPrimitiveCandidateIsCanonical =
        refl
    ; arbitrarySelectedHolonomyCancellation =
        sfgcArbitraryGaugeHolonomyConjugation
    ; arbitrarySelectedHolonomyCancellationIsCanonical =
        refl
    ; trivialAdResidualCancellation =
        sfgcTrivialC4AdjointArbitraryDensityInvariant
    ; trivialAdResidualCancellationIsCanonical =
        refl
    ; zeroDiscreteIBPExactLaw =
        sfgcZeroDiscreteVariationIBPLaw
    ; zeroDiscreteIBPExactLawIsCanonical =
        refl
    ; firstStrictTransportMissingPrimitive =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; firstStrictTransportMissingPrimitiveIsFieldStrengthAction =
        refl
    ; firstStrictNonFlatHolonomyMissingPrimitive =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; firstStrictNonFlatHolonomyMissingPrimitiveIsCurvature =
        refl
    ; firstStrictKillingMissingPrimitive =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; firstStrictKillingMissingPrimitiveIsLieAlgebraCarrier =
        refl
    ; firstStrictIBPMissingPrimitive =
        missingVariationPairingForSelectedHodgeStar
    ; firstStrictIBPMissingPrimitiveIsVariationPairing =
        refl
    ; summaryPromoted =
        false
    ; summaryPromotedIsFalse =
        refl
    ; summaryBoundary =
        "Strongest local YM progress summary: SFGCSite2DEdge path transport, covariant-difference, nonconstant finite density, and single-plaquette action are inhabited only as lower candidates"
        ∷ "Closed local law: arbitrary selected SFGC plaquette holonomy cancellation under gauge transform follows from flat finite-C4 square cancellation"
        ∷ "Closed local law: Ad residual cancellation for the selected field-strength carrier is definitional only because the selected adjoint action is identity"
        ∷ "Closed local law: zero variation satisfies the discrete IBP equation exactly"
        ∷ "First strict transport blocker remains a real field-strength fibre action on the selected gauge bundle"
        ∷ "First strict non-flat holonomy blocker remains non-flat SFGCSite2D connection curvature"
        ∷ "First strict Killing blocker remains a Lie algebra carrier for the selected finite gauge sector"
        ∷ "First strict IBP blocker remains variation pairing for the selected Hodge/action surface"
        ∷ "No D * F = J, D F = 0, Yang-Mills closure, Maxwell closure, or spectral-gap promotion is asserted"
        ∷ []
    }

record YMSFGCLowerPrimitiveCandidateBundle : Set₁ where
  field
    identityEdgeTargetLawReport :
      YMSFGCIdentityEdgeTargetLawReport

    identityEdgeTargetLawReportIsCanonical :
      identityEdgeTargetLawReport
      ≡
      canonicalYMSFGCIdentityEdgeTargetLawReport

    directedEdgeSchemaReport :
      YMSFGCSite2DDirectedEdgeSchemaReport

    directedEdgeSchemaReportIsCanonical :
      directedEdgeSchemaReport
      ≡
      canonicalYMSFGCSite2DDirectedEdgeSchemaReport

    suppliedLinkFibreTransportCompilerReceipt :
      YMSFGCSuppliedLinkFibreTransportCompilerReceipt

    suppliedLinkFibreTransportCompilerReceiptIsCanonical :
      suppliedLinkFibreTransportCompilerReceipt
      ≡
      canonicalYMSFGCSuppliedLinkFibreTransportCompilerReceipt

    pathTransportPrimitiveCandidate :
      SFGCPathTransportPrimitive

    pathTransportPrimitiveCandidateIsDegenerate :
      pathTransportPrimitiveCandidate
      ≡
      canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate

    covariantDifferencePrimitiveCandidate :
      CovariantDifferencePrimitive
        canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate

    covariantDifferencePrimitiveCandidateIsDegenerate :
      covariantDifferencePrimitiveCandidate
      ≡
      canonicalYMSFGCDegenerateCovariantDifferencePrimitiveCandidate

    gaugeInvariantQuadraticDensityPrimitiveCandidate :
      GaugeInvariantQuadraticDensityPrimitive
        canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate

    gaugeInvariantQuadraticDensityPrimitiveCandidateIsLowerCandidate :
      gaugeInvariantQuadraticDensityPrimitiveCandidate
      ≡
      canonicalYMSFGCPhaseZeroQuadraticDensityPrimitiveCandidate

    discreteYMActionPrimitiveCandidate :
      DiscreteYMActionPrimitive
        canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate
        canonicalYMSFGCPhaseZeroQuadraticDensityPrimitiveCandidate

    discreteYMActionPrimitiveCandidateIsDegenerate :
      discreteYMActionPrimitiveCandidate
      ≡
      canonicalYMSFGCSinglePlaquetteYMActionPrimitiveCandidate

    lowerCandidatePromoted :
      Bool

    lowerCandidatePromotedIsFalse :
      lowerCandidatePromoted ≡ false

    exactPromotionBlocker :
      String

    bundleBoundary :
      List String

canonicalYMSFGCLowerPrimitiveCandidateBundle :
  YMSFGCLowerPrimitiveCandidateBundle
canonicalYMSFGCLowerPrimitiveCandidateBundle =
  record
    { identityEdgeTargetLawReport =
        canonicalYMSFGCIdentityEdgeTargetLawReport
    ; identityEdgeTargetLawReportIsCanonical =
        refl
    ; directedEdgeSchemaReport =
        canonicalYMSFGCSite2DDirectedEdgeSchemaReport
    ; directedEdgeSchemaReportIsCanonical =
        refl
    ; suppliedLinkFibreTransportCompilerReceipt =
        canonicalYMSFGCSuppliedLinkFibreTransportCompilerReceipt
    ; suppliedLinkFibreTransportCompilerReceiptIsCanonical =
        refl
    ; pathTransportPrimitiveCandidate =
        canonicalYMSFGCDegeneratePathTransportPrimitiveCandidate
    ; pathTransportPrimitiveCandidateIsDegenerate =
        refl
    ; covariantDifferencePrimitiveCandidate =
        canonicalYMSFGCDegenerateCovariantDifferencePrimitiveCandidate
    ; covariantDifferencePrimitiveCandidateIsDegenerate =
        refl
    ; gaugeInvariantQuadraticDensityPrimitiveCandidate =
        canonicalYMSFGCPhaseZeroQuadraticDensityPrimitiveCandidate
    ; gaugeInvariantQuadraticDensityPrimitiveCandidateIsLowerCandidate =
        refl
    ; discreteYMActionPrimitiveCandidate =
        canonicalYMSFGCSinglePlaquetteYMActionPrimitiveCandidate
    ; discreteYMActionPrimitiveCandidateIsDegenerate =
        refl
    ; lowerCandidatePromoted =
        false
    ; lowerCandidatePromotedIsFalse =
        refl
    ; exactPromotionBlocker =
        "fieldStrengthTransportLaw : selected gauge-bundle transport from a real link/fibre action with gauge covariance, not the compiled edge-target probe lower candidate"
    ; bundleBoundary =
        "Instantiated all four primitive record shapes as lower candidates over existing SFGC carriers"
        ∷ "The path carrier now has a real identity edge/path with source and target laws"
        ∷ "First diagnostic now bundled: directed-edge schema and plaquette boundary endpoint laws are explicitly closed on SFGCSite2D"
        ∷ "A supplied link/fibre interface now compiles into SFGCPathTransportPrimitive"
        ∷ "Path transport now distinguishes identity and oriented SFGCSite2DEdge values, but remains non-promoting because the supplied interface wraps the edge-target probe rather than a gauge-covariant parallel transport law"
        ∷ "The density candidate is nonconstant on finite Phase4 field-strength bridge values, but it is not a trace/Killing Yang-Mills density"
        ∷ "The action candidate is a single-plaquette proxy, not a plaquette sum or variational action"
        ∷ "The whole bundle is explicitly non-promoting"
        ∷ []
    }

record YMSFGCSelectedFieldStrengthAdjointTransportCandidate : Set₁ where
  field
    selectedGaugeTransformCarrier :
      Set

    selectedGaugeTransformCarrierIsSFGS :
      selectedGaugeTransformCarrier
      ≡
      SFGS.GaugeTransform

    selectedFieldStrengthCarrier :
      Set

    selectedFieldStrengthCarrierIsSFGC :
      selectedFieldStrengthCarrier
      ≡
      SFGC.SFGCSite2DFieldStrengthBridge

    adjointTransportCandidate :
      SFGS.GaugeTransform →
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    adjointTransportCandidateIsTrivialC4Adjoint :
      adjointTransportCandidate
      ≡
      sfgcSelectedFieldStrengthAdjointTransportCandidate

    plaquetteValuePreservedByCandidate :
      (gauge : SFGS.GaugeTransform) →
      (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        (adjointTransportCandidate gauge fieldStrength)
        plaquette
        ≡
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        fieldStrength
        plaquette

    firstRemainingPrimitive :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    firstRemainingPrimitiveIsTransportAction :
      firstRemainingPrimitive
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    candidateBoundary :
      List String

canonicalYMSFGCSelectedFieldStrengthAdjointTransportCandidate :
  YMSFGCSelectedFieldStrengthAdjointTransportCandidate
canonicalYMSFGCSelectedFieldStrengthAdjointTransportCandidate =
  record
    { selectedGaugeTransformCarrier =
        SFGS.GaugeTransform
    ; selectedGaugeTransformCarrierIsSFGS =
        refl
    ; selectedFieldStrengthCarrier =
        SFGC.SFGCSite2DFieldStrengthBridge
    ; selectedFieldStrengthCarrierIsSFGC =
        refl
    ; adjointTransportCandidate =
        sfgcSelectedFieldStrengthAdjointTransportCandidate
    ; adjointTransportCandidateIsTrivialC4Adjoint =
        refl
    ; plaquetteValuePreservedByCandidate =
        sfgcSelectedFieldStrengthAdjointTransportCandidatePlaquetteLaw
    ; firstRemainingPrimitive =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; firstRemainingPrimitiveIsTransportAction =
        refl
    ; candidateBoundary =
        "Candidate only: finite C4 is abelian, so the local adjoint action on the selected field-strength bridge is modeled as identity"
        ∷ "Wired law: the candidate preserves every selected plaquette Wilson-loop phase by refl"
        ∷ "Still missing: a supplied link/fiber action deriving edge/path transport over SFGCSite2D field-strength values"
        ∷ "Still missing: covariant-difference and gauge-compatibility proofs using that supplied transport"
        ∷ []
    }

record YMSFGCFlatConnectionExteriorExtensionWitness : Set₁ where
  field
    flatConnection :
      SFGC.GaugeField

    flatConnectionIsVacuum :
      flatConnection
      ≡
      SFGC.vacuumGaugeField

    flatConnectionPlaquetteCurvatureVanishes :
      (base : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEvaluate2
        (sfgcSelectedCurvature2Form flatConnection)
        (SFGC.sfgcSite2DPlaquetteAt base)
        ≡
      SPTI4.φ0

    flatCovariantDerivative0Candidate :
      SFGC.SFGCSite2DDiscrete0Form →
      SFGC.SFGCSite2DDiscrete1Form

    flatCovariantDerivative0CandidateIsExteriorDerivative0 :
      (form : SFGC.SFGCSite2DDiscrete0Form) →
      flatCovariantDerivative0Candidate form
        ≡
      SFGC.sfgcSite2Dδ₀ form

    flatCovariantDerivative0CandidateSatisfiesDegenerateCovariantDifferencePrimitive :
      (form : SFGC.SFGCSite2DDiscrete0Form) →
      CovariantDifferencePrimitive.flatConnectionExtendsSelectedExteriorDerivative
        canonicalYMSFGCDegenerateCovariantDifferencePrimitiveCandidate
        form

    dischargedBianchiPrimitive :
      YangMillsBianchiMissingPrimitive

    dischargedBianchiPrimitiveIsCovariantExtension :
      dischargedBianchiPrimitive
      ≡
      missingCovariantDerivativeExtendsSelectedExteriorDerivative

    firstRemainingBianchiPrimitive :
      YangMillsBianchiMissingPrimitive

    firstRemainingBianchiPrimitiveIsGaugeCompatibility :
      firstRemainingBianchiPrimitive
      ≡
      missingGaugeCompatibilityOfBianchiLaw

    witnessBoundary :
      List String

canonicalYMSFGCFlatConnectionExteriorExtensionWitness :
  YMSFGCFlatConnectionExteriorExtensionWitness
canonicalYMSFGCFlatConnectionExteriorExtensionWitness =
  record
    { flatConnection =
        SFGC.vacuumGaugeField
    ; flatConnectionIsVacuum =
        refl
    ; flatConnectionPlaquetteCurvatureVanishes =
        SFGC.sfgcSite2DVacuumWilsonLoopFlatness
    ; flatCovariantDerivative0Candidate =
        sfgcSelectedFlatConnectionExteriorExtensionCandidate
    ; flatCovariantDerivative0CandidateIsExteriorDerivative0 =
        sfgcSelectedFlatConnectionExteriorExtensionCandidateLaw
    ; flatCovariantDerivative0CandidateSatisfiesDegenerateCovariantDifferencePrimitive =
        sfgcDegenerateCovariantDifferencePrimitiveFlatConnectionExtendsSelectedExteriorDerivative
    ; dischargedBianchiPrimitive =
        missingCovariantDerivativeExtendsSelectedExteriorDerivative
    ; dischargedBianchiPrimitiveIsCovariantExtension =
        refl
    ; firstRemainingBianchiPrimitive =
        missingGaugeCompatibilityOfBianchiLaw
    ; firstRemainingBianchiPrimitiveIsGaugeCompatibility =
        refl
    ; witnessBoundary =
        "Flat-connection narrowing only: at the vacuum connection, the selected plaquette curvature vanishes"
        ∷ "The only inhabited derivative candidate on 0-forms is exactly SFGC.sfgcSite2Dδ0"
        ∷ "This discharges the flat-connection covariant-extension primitive via the degenerate covariant-difference witness"
        ∷ "Stokes support is discharged on the selected plaquette surface via selected exterior δ1∘δ0 = 0"
        ∷ "Representative finite SU(3) Jacobi support is discharged at [4,5,8] via localFiniteSU3Representative458JacobiResidualIsZero"
        ∷ "Still missing: a general covariant derivative on the selected field-strength carrier"
        ∷ "Next local Bianchi primitive after that discharge is gauge compatibility of the transported Bianchi law"
        ∷ []
    }

record YMSFGCFlatConnectionPlaquetteStokesOrJacobiWitness : Set₁ where
  field
    flatConnectionExteriorExtensionWitness :
      YMSFGCFlatConnectionExteriorExtensionWitness

    flatConnectionExteriorExtensionWitnessIsCanonical :
      flatConnectionExteriorExtensionWitness
      ≡
      canonicalYMSFGCFlatConnectionExteriorExtensionWitness

    selectedExteriorDerivativeSquaredZeroWitness :
      YMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    selectedExteriorDerivativeSquaredZeroWitnessIsCanonical :
      selectedExteriorDerivativeSquaredZeroWitness
      ≡
      canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    dischargedBianchiPrimitive :
      YangMillsBianchiMissingPrimitive

    dischargedBianchiPrimitiveIsPlaquetteStokesOrJacobiLaw :
      dischargedBianchiPrimitive
      ≡
      missingPlaquetteStokesOrJacobiLaw

    firstRemainingBianchiPrimitive :
      YangMillsBianchiMissingPrimitive

    firstRemainingBianchiPrimitiveIsGaugeCompatibilityOfBianchiLaw :
      firstRemainingBianchiPrimitive
      ≡
      missingGaugeCompatibilityOfBianchiLaw

    witnessBoundary :
      List String

canonicalYMSFGCFlatConnectionPlaquetteStokesOrJacobiWitness :
  YMSFGCFlatConnectionPlaquetteStokesOrJacobiWitness
canonicalYMSFGCFlatConnectionPlaquetteStokesOrJacobiWitness =
  record
    { flatConnectionExteriorExtensionWitness =
        canonicalYMSFGCFlatConnectionExteriorExtensionWitness
    ; flatConnectionExteriorExtensionWitnessIsCanonical =
        refl
    ; selectedExteriorDerivativeSquaredZeroWitness =
        canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness
    ; selectedExteriorDerivativeSquaredZeroWitnessIsCanonical =
        refl
    ; dischargedBianchiPrimitive =
        missingPlaquetteStokesOrJacobiLaw
    ; dischargedBianchiPrimitiveIsPlaquetteStokesOrJacobiLaw =
        refl
    ; firstRemainingBianchiPrimitive =
        missingGaugeCompatibilityOfBianchiLaw
    ; firstRemainingBianchiPrimitiveIsGaugeCompatibilityOfBianchiLaw =
        refl
    ; witnessBoundary =
        "Flat-connection local advancement: the post-covariant-extension Bianchi primitive is checkpointed as plaquette Stokes/Jacobi support"
        ∷ "This witness discharges that local primitive in the bounded flat SFGCSite2D route and advances the next local primitive to gauge compatibility of the Bianchi law"
        ∷ "No non-flat covariant-transport law, no gauge-compatibility proof, and no promoted Yang-Mills Bianchi identity are constructed by this bounded move"
        ∷ []
    }

sfgcFlatGaugeCompatibilityOfBianchiFromHolonomyAndAdjoint :
  (gauge : SFGS.GaugeTransform) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    (sfgcSelectedFieldStrengthBridge
      (SFGC.transformGauge gauge SFGC.vacuumGaugeField))
    plaquette
  ≡
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    (sfgcSelectedFieldStrengthBridge SFGC.vacuumGaugeField)
    plaquette
sfgcFlatGaugeCompatibilityOfBianchiFromHolonomyAndAdjoint
  gauge plaquette =
  trans
    (sfgcArbitraryGaugeHolonomyConjugation
      gauge SFGC.vacuumGaugeField plaquette)
    (sfgcSelectedFieldStrengthAdjointTransportCandidatePlaquetteLaw
      gauge
      (sfgcSelectedFieldStrengthBridge SFGC.vacuumGaugeField)
      plaquette)

record YMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness : Set₁ where
  field
    flatConnectionPlaquetteStokesOrJacobiWitness :
      YMSFGCFlatConnectionPlaquetteStokesOrJacobiWitness

    flatConnectionPlaquetteStokesOrJacobiWitnessIsCanonical :
      flatConnectionPlaquetteStokesOrJacobiWitness
      ≡
      canonicalYMSFGCFlatConnectionPlaquetteStokesOrJacobiWitness

    selectedExteriorDerivativeSquaredZeroWitness :
      YMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    selectedExteriorDerivativeSquaredZeroWitnessIsCanonical :
      selectedExteriorDerivativeSquaredZeroWitness
      ≡
      canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    localFiniteSU3RepresentativeJacobiWitness :
      localFiniteSU3PositiveAxisJacobiResidual
        su3Axis4
        su3Axis5
        su3Axis8
      ≡
      su3Zero

    localFiniteSU3RepresentativeJacobiWitnessIsCanonical :
      localFiniteSU3RepresentativeJacobiWitness
      ≡
      sfgcFlatPlaquetteJacobiSupportRepresentative458

    selectedFieldStrengthTransportCandidate :
      YMSFGCSelectedFieldStrengthAdjointTransportCandidate

    selectedFieldStrengthTransportCandidateIsCanonical :
      selectedFieldStrengthTransportCandidate
      ≡
      canonicalYMSFGCSelectedFieldStrengthAdjointTransportCandidate

    flatGaugeCompatibilityOfBianchiPlaquetteLaw :
      (gauge : SFGS.GaugeTransform) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        (sfgcSelectedFieldStrengthBridge
          (SFGC.transformGauge gauge SFGC.vacuumGaugeField))
        plaquette
        ≡
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        (sfgcSelectedFieldStrengthBridge SFGC.vacuumGaugeField)
        plaquette

    flatGaugeCompatibilityOfBianchiPlaquetteLawIsCanonical :
      flatGaugeCompatibilityOfBianchiPlaquetteLaw
      ≡
      sfgcFlatGaugeCompatibilityOfBianchiFromHolonomyAndAdjoint

    dischargedBianchiPrimitive :
      YangMillsBianchiMissingPrimitive

    dischargedBianchiPrimitiveIsGaugeCompatibilityOfBianchiLaw :
      dischargedBianchiPrimitive
      ≡
      missingGaugeCompatibilityOfBianchiLaw

    localRemainingBianchiPrimitives :
      List YangMillsBianchiMissingPrimitive

    localRemainingBianchiPrimitivesExhausted :
      localRemainingBianchiPrimitives
      ≡
      []

    witnessBoundary :
      List String

canonicalYMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness :
  YMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness
canonicalYMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness =
  record
    { flatConnectionPlaquetteStokesOrJacobiWitness =
        canonicalYMSFGCFlatConnectionPlaquetteStokesOrJacobiWitness
    ; flatConnectionPlaquetteStokesOrJacobiWitnessIsCanonical =
        refl
    ; selectedExteriorDerivativeSquaredZeroWitness =
        canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness
    ; selectedExteriorDerivativeSquaredZeroWitnessIsCanonical =
        refl
    ; localFiniteSU3RepresentativeJacobiWitness =
        sfgcFlatPlaquetteJacobiSupportRepresentative458
    ; localFiniteSU3RepresentativeJacobiWitnessIsCanonical =
        refl
    ; selectedFieldStrengthTransportCandidate =
        canonicalYMSFGCSelectedFieldStrengthAdjointTransportCandidate
    ; selectedFieldStrengthTransportCandidateIsCanonical =
        refl
    ; flatGaugeCompatibilityOfBianchiPlaquetteLaw =
        sfgcFlatGaugeCompatibilityOfBianchiFromHolonomyAndAdjoint
    ; flatGaugeCompatibilityOfBianchiPlaquetteLawIsCanonical =
        refl
    ; dischargedBianchiPrimitive =
        missingGaugeCompatibilityOfBianchiLaw
    ; dischargedBianchiPrimitiveIsGaugeCompatibilityOfBianchiLaw =
        refl
    ; localRemainingBianchiPrimitives =
        []
    ; localRemainingBianchiPrimitivesExhausted =
        refl
    ; witnessBoundary =
        "Flat-connection local advancement: gauge compatibility of the selected Bianchi plaquette law is now witnessed by composing arbitrary-gauge selected holonomy cancellation with the selected adjoint transport candidate law"
        ∷ "The witness explicitly threads selected exterior δ1∘δ0 = 0 and representative SU(3) [4,5,8] Jacobi residual cancellation from the local finite scaffold"
        ∷ "This exhausts the bounded flat local Bianchi primitive queue only; global non-flat transport, nontrivial fibre action, and promoted Yang-Mills Bianchi closure remain open"
        ∷ []
    }

record YMSFGCCurvatureQuadraticDensityProxy : Set₁ where
  field
    densityScalarCarrier :
      Set

    densityScalarCarrierIsInteger :
      densityScalarCarrier
      ≡
      ℤ

    selectedPhasePairingProxy :
      SPTI4.Phase4 →
      SPTI4.Phase4 →
      ℤ

    selectedPhasePairingProxyIsPhaseKernel4 :
      selectedPhasePairingProxy
      ≡
      SPTI4.phaseKernel4

    selectedCurvatureQuadraticDensityProxy :
      SFGC.SFGCSite2DDiscrete2Form →
      SFGC.SFGCSite2DPlaquette →
      ℤ

    selectedCurvatureQuadraticDensityProxyIsDiagonalPhaseKernel :
      selectedCurvatureQuadraticDensityProxy
      ≡
      sfgcSelectedCurvatureQuadraticDensityProxy

    proxyIsConstantSamePhaseKernel :
      (curvature : SFGC.SFGCSite2DDiscrete2Form) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      selectedCurvatureQuadraticDensityProxy curvature plaquette
        ≡
      + 1

    firstRemainingActionPrimitive :
      YMSFGCActionFunctionalMissingPrimitive

    firstRemainingActionPrimitiveIsQuadraticDensity :
      firstRemainingActionPrimitive
      ≡
      missingCurvatureQuadraticDensityOnPhase4Plaquettes

    proxyBoundary :
      List String

canonicalYMSFGCCurvatureQuadraticDensityProxy :
  YMSFGCCurvatureQuadraticDensityProxy
canonicalYMSFGCCurvatureQuadraticDensityProxy =
  record
    { densityScalarCarrier =
        ℤ
    ; densityScalarCarrierIsInteger =
        refl
    ; selectedPhasePairingProxy =
        SPTI4.phaseKernel4
    ; selectedPhasePairingProxyIsPhaseKernel4 =
        refl
    ; selectedCurvatureQuadraticDensityProxy =
        sfgcSelectedCurvatureQuadraticDensityProxy
    ; selectedCurvatureQuadraticDensityProxyIsDiagonalPhaseKernel =
        refl
    ; proxyIsConstantSamePhaseKernel =
        λ curvature plaquette →
          sfgcPhase4QuadraticKernelProxyIsSamePhaseKernel
            (SFGC.sfgcSite2DEvaluate2 curvature plaquette)
    ; firstRemainingActionPrimitive =
        missingCurvatureQuadraticDensityOnPhase4Plaquettes
    ; firstRemainingActionPrimitiveIsQuadraticDensity =
        refl
    ; proxyBoundary =
        "Proxy only: diagonal SPTI4.phaseKernel4 supplies a typed finite Phase4 pairing on plaquette curvature values"
        ∷ "The proxy is constant +1 on diagonal Phase4 inputs, so it is not a physical Killing-form/tr(F^2) density"
        ∷ "Still missing: a gauge-invariant trace or Killing pairing for the selected field-strength algebra"
        ∷ "Still missing: a plaquette sum/integration functional and variational action surface"
        ∷ []
    }

record YMSFGCPrimitiveDefinitionCandidateSurface : Set₁ where
  field
    primitiveInterfaceRequest :
      YMSFGCPrimitiveInterfaceRequest

    primitiveInterfaceRequestIsCanonical :
      primitiveInterfaceRequest
      ≡
      canonicalYMSFGCPrimitiveInterfaceRequest

    lowerPrimitiveCandidateBundle :
      YMSFGCLowerPrimitiveCandidateBundle

    lowerPrimitiveCandidateBundleIsCanonical :
      lowerPrimitiveCandidateBundle
      ≡
      canonicalYMSFGCLowerPrimitiveCandidateBundle

    selectedFieldStrengthTransportActionCandidate :
      YMSFGCSelectedFieldStrengthAdjointTransportCandidate

    selectedFieldStrengthTransportActionCandidateIsCanonical :
      selectedFieldStrengthTransportActionCandidate
      ≡
      canonicalYMSFGCSelectedFieldStrengthAdjointTransportCandidate

    covariantDerivativeExtendsSelectedExteriorDerivativeCandidate :
      YMSFGCFlatConnectionExteriorExtensionWitness

    covariantDerivativeExtendsSelectedExteriorDerivativeCandidateIsCanonical :
      covariantDerivativeExtendsSelectedExteriorDerivativeCandidate
      ≡
      canonicalYMSFGCFlatConnectionExteriorExtensionWitness

    curvatureQuadraticDensityOnPhase4PlaquettesCandidate :
      YMSFGCCurvatureQuadraticDensityProxy

    curvatureQuadraticDensityOnPhase4PlaquettesCandidateIsCanonical :
      curvatureQuadraticDensityOnPhase4PlaquettesCandidate
      ≡
      canonicalYMSFGCCurvatureQuadraticDensityProxy

    requestedSelectedFieldStrengthTransportCarrier :
      String

    requestedCovariantDifferenceCarrier :
      String

    requestedCovariantExtensionLawCarrier :
      String

    requestedGaugeInvariantQuadraticPairingCarrier :
      String

    exactSelectedCovariantDerivativeMissingPrimitives :
      List YMSFGCSelectedCovariantDerivativeMissingPrimitive

    exactSelectedCovariantDerivativeMissingPrimitivesAreCanonical :
      exactSelectedCovariantDerivativeMissingPrimitives
      ≡
      canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives

    exactActionFunctionalMissingPrimitives :
      List YMSFGCActionFunctionalMissingPrimitive

    exactActionFunctionalMissingPrimitivesAreCanonical :
      exactActionFunctionalMissingPrimitives
      ≡
      canonicalYMSFGCActionFunctionalMissingPrimitives

    candidateSurfaceBoundary :
      List String

canonicalYMSFGCPrimitiveDefinitionCandidateSurface :
  YMSFGCPrimitiveDefinitionCandidateSurface
canonicalYMSFGCPrimitiveDefinitionCandidateSurface =
  record
    { primitiveInterfaceRequest =
        canonicalYMSFGCPrimitiveInterfaceRequest
    ; primitiveInterfaceRequestIsCanonical =
        refl
    ; lowerPrimitiveCandidateBundle =
        canonicalYMSFGCLowerPrimitiveCandidateBundle
    ; lowerPrimitiveCandidateBundleIsCanonical =
        refl
    ; selectedFieldStrengthTransportActionCandidate =
        canonicalYMSFGCSelectedFieldStrengthAdjointTransportCandidate
    ; selectedFieldStrengthTransportActionCandidateIsCanonical =
        refl
    ; covariantDerivativeExtendsSelectedExteriorDerivativeCandidate =
        canonicalYMSFGCFlatConnectionExteriorExtensionWitness
    ; covariantDerivativeExtendsSelectedExteriorDerivativeCandidateIsCanonical =
        refl
    ; curvatureQuadraticDensityOnPhase4PlaquettesCandidate =
        canonicalYMSFGCCurvatureQuadraticDensityProxy
    ; curvatureQuadraticDensityOnPhase4PlaquettesCandidateIsCanonical =
        refl
    ; requestedSelectedFieldStrengthTransportCarrier =
        "SFGCPathTransportPrimitive.fieldStrengthTransport : PathOrEdge -> SFGCSite2DFieldStrengthBridge -> SFGCSite2DFieldStrengthBridge"
    ; requestedCovariantDifferenceCarrier =
        "CovariantDifferencePrimitive.covariantDifference : GaugeField -> SFGCSite2DFieldStrengthBridge -> CovariantDifferenceCarrier"
    ; requestedCovariantExtensionLawCarrier =
        "CovariantDifferencePrimitive.flatConnectionExtendsSelectedExteriorDerivative : flat A -> D_A on 0-forms agrees with SFGC.sfgcSite2Dδ0"
    ; requestedGaugeInvariantQuadraticPairingCarrier =
        "GaugeInvariantQuadraticDensityPrimitive.density : SFGCSite2DFieldStrengthBridge -> SFGCSite2DPlaquette -> DensityScalar, nonconstant and gauge invariant"
    ; exactSelectedCovariantDerivativeMissingPrimitives =
        canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives
    ; exactSelectedCovariantDerivativeMissingPrimitivesAreCanonical =
        refl
    ; exactActionFunctionalMissingPrimitives =
        canonicalYMSFGCActionFunctionalMissingPrimitives
    ; exactActionFunctionalMissingPrimitivesAreCanonical =
        refl
    ; candidateSurfaceBoundary =
        "Lower primitive candidate bundle instantiates all four primitive record shapes, but only as non-promoting lower candidates"
        ∷ "Primitive 1 candidate: identity adjoint action on the selected finite C4 field-strength bridge; it is not an edge/path transport derivation"
        ∷ "Primitive 1 lower inhabitant: SFGCSite2DEdge now uses identity, p2, and p3 edges; oriented field-strength transport re-probes the target plaquette"
        ∷ "Primitive 2 candidate: the flat vacuum derivative on 0-forms is exactly selected δ0; it is not a general covariant derivative on field strengths"
        ∷ "Primitive 2 lower inhabitant: covariantDifference uses A at the reference site to choose an edge transport, but has no derivation as D_A"
        ∷ "Primitive 3 candidate: diagonal phaseKernel4 is a typed plaquette density proxy; it is not a nonconstant trace/Killing-form Yang-Mills density"
        ∷ "Primitive 3 lower inhabitant: phaseKernel4 against φ0 is nonconstant on Phase4 bridge values, but its gauge and trace laws remain target surfaces"
        ∷ "Primitive 4 lower inhabitant: the single-plaquette action proxy evaluates density at one plaquette and has no variation or Euler-Lagrange proof"
        ∷ "Narrowed interface records now name the exact missing carriers: SFGCPathTransportPrimitive, CovariantDifferencePrimitive, GaugeInvariantQuadraticDensityPrimitive, and DiscreteYMActionPrimitive"
        ∷ "The precise promotion blockers remain supplied link/fiber field-strength path transport, covariant-extension law, gauge-invariant trace/Killing density, plaquette integration, and variational pairing"
        ∷ "No D * F = J or D F = 0 promotion is constructed by this candidate surface"
        ∷ []
    }

record YMSFGCSelectedOperatorSkeleton : Set₁ where
  field
    selectedGaugeFieldCarrier :
      Set

    selectedGaugeFieldCarrierIsSFGC :
      selectedGaugeFieldCarrier
      ≡
      SFGC.GaugeField

    selectedGaugeConnectionTo1Form :
      SFGC.GaugeField →
      SFGC.SFGCSite2DDiscrete1Form

    selectedGaugeConnectionTo1FormIsSFGC :
      selectedGaugeConnectionTo1Form
      ≡
      SFGC.sfgcSite2DConnectionTo1Form

    selectedCurvature2Form :
      SFGC.GaugeField →
      SFGC.SFGCSite2DDiscrete2Form

    selectedCurvature2FormIsδ₁Connection :
      selectedCurvature2Form
      ≡
      sfgcSelectedCurvature2Form

    selectedFieldStrengthBridge :
      SFGC.GaugeField →
      SFGC.SFGCSite2DFieldStrengthBridge

    selectedFieldStrengthBridgeIsSFGC :
      selectedFieldStrengthBridge
      ≡
      sfgcSelectedFieldStrengthBridge

    selectedCurvatureEvaluation :
      SFGC.SFGCSite2DDiscrete2Form →
      SFGC.SFGCSite2DPlaquette →
      SPTI4.Phase4

    selectedCurvatureEvaluationIsSFGC :
      selectedCurvatureEvaluation
      ≡
      SFGC.sfgcSite2DEvaluate2

    selectedMatterCovariantOperatorPackage :
      SFGC.ShiftFiniteGaugeCoupling

    selectedMatterCovariantOperatorPackageIsSFGC :
      selectedMatterCovariantOperatorPackage
      ≡
      SFGC.shiftFiniteGaugeCoupling

    selectedFieldStrengthTransportCandidate :
      YMSFGCSelectedFieldStrengthAdjointTransportCandidate

    selectedFieldStrengthTransportCandidateIsCanonical :
      selectedFieldStrengthTransportCandidate
      ≡
      canonicalYMSFGCSelectedFieldStrengthAdjointTransportCandidate

    flatConnectionExteriorExtensionWitness :
      YMSFGCFlatConnectionExteriorExtensionWitness

    flatConnectionExteriorExtensionWitnessIsCanonical :
      flatConnectionExteriorExtensionWitness
      ≡
      canonicalYMSFGCFlatConnectionExteriorExtensionWitness

    curvatureQuadraticDensityProxy :
      YMSFGCCurvatureQuadraticDensityProxy

    curvatureQuadraticDensityProxyIsCanonical :
      curvatureQuadraticDensityProxy
      ≡
      canonicalYMSFGCCurvatureQuadraticDensityProxy

    primitiveDefinitionCandidateSurface :
      YMSFGCPrimitiveDefinitionCandidateSurface

    primitiveDefinitionCandidateSurfaceIsCanonical :
      primitiveDefinitionCandidateSurface
      ≡
      canonicalYMSFGCPrimitiveDefinitionCandidateSurface

    primitiveInterfaceRequest :
      YMSFGCPrimitiveInterfaceRequest

    primitiveInterfaceRequestIsCanonical :
      primitiveInterfaceRequest
      ≡
      canonicalYMSFGCPrimitiveInterfaceRequest

    exactSelectedCovariantDerivativeMissingPrimitives :
      List YMSFGCSelectedCovariantDerivativeMissingPrimitive

    exactSelectedCovariantDerivativeMissingPrimitivesAreCanonical :
      exactSelectedCovariantDerivativeMissingPrimitives
      ≡
      canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives

    exactActionFunctionalMissingPrimitives :
      List YMSFGCActionFunctionalMissingPrimitive

    exactActionFunctionalMissingPrimitivesAreCanonical :
      exactActionFunctionalMissingPrimitives
      ≡
      canonicalYMSFGCActionFunctionalMissingPrimitives

    firstCovariantDerivativePrimitive :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    firstCovariantDerivativePrimitiveIsTransportAction :
      firstCovariantDerivativePrimitive
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    firstActionFunctionalPrimitive :
      YMSFGCActionFunctionalMissingPrimitive

    firstActionFunctionalPrimitiveIsCurvatureQuadraticDensity :
      firstActionFunctionalPrimitive
      ≡
      missingCurvatureQuadraticDensityOnPhase4Plaquettes

    skeletonBoundary :
      List String

canonicalYMSFGCSelectedOperatorSkeleton :
  YMSFGCSelectedOperatorSkeleton
canonicalYMSFGCSelectedOperatorSkeleton =
  record
    { selectedGaugeFieldCarrier =
        SFGC.GaugeField
    ; selectedGaugeFieldCarrierIsSFGC =
        refl
    ; selectedGaugeConnectionTo1Form =
        SFGC.sfgcSite2DConnectionTo1Form
    ; selectedGaugeConnectionTo1FormIsSFGC =
        refl
    ; selectedCurvature2Form =
        sfgcSelectedCurvature2Form
    ; selectedCurvature2FormIsδ₁Connection =
        refl
    ; selectedFieldStrengthBridge =
        sfgcSelectedFieldStrengthBridge
    ; selectedFieldStrengthBridgeIsSFGC =
        refl
    ; selectedCurvatureEvaluation =
        SFGC.sfgcSite2DEvaluate2
    ; selectedCurvatureEvaluationIsSFGC =
        refl
    ; selectedMatterCovariantOperatorPackage =
        SFGC.shiftFiniteGaugeCoupling
    ; selectedMatterCovariantOperatorPackageIsSFGC =
        refl
    ; selectedFieldStrengthTransportCandidate =
        canonicalYMSFGCSelectedFieldStrengthAdjointTransportCandidate
    ; selectedFieldStrengthTransportCandidateIsCanonical =
        refl
    ; flatConnectionExteriorExtensionWitness =
        canonicalYMSFGCFlatConnectionExteriorExtensionWitness
    ; flatConnectionExteriorExtensionWitnessIsCanonical =
        refl
    ; curvatureQuadraticDensityProxy =
        canonicalYMSFGCCurvatureQuadraticDensityProxy
    ; curvatureQuadraticDensityProxyIsCanonical =
        refl
    ; primitiveDefinitionCandidateSurface =
        canonicalYMSFGCPrimitiveDefinitionCandidateSurface
    ; primitiveDefinitionCandidateSurfaceIsCanonical =
        refl
    ; primitiveInterfaceRequest =
        canonicalYMSFGCPrimitiveInterfaceRequest
    ; primitiveInterfaceRequestIsCanonical =
        refl
    ; exactSelectedCovariantDerivativeMissingPrimitives =
        canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives
    ; exactSelectedCovariantDerivativeMissingPrimitivesAreCanonical =
        refl
    ; exactActionFunctionalMissingPrimitives =
        canonicalYMSFGCActionFunctionalMissingPrimitives
    ; exactActionFunctionalMissingPrimitivesAreCanonical =
        refl
    ; firstCovariantDerivativePrimitive =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; firstCovariantDerivativePrimitiveIsTransportAction =
        refl
    ; firstActionFunctionalPrimitive =
        missingCurvatureQuadraticDensityOnPhase4Plaquettes
    ; firstActionFunctionalPrimitiveIsCurvatureQuadraticDensity =
        refl
    ; skeletonBoundary =
        "Wired honestly: selected curvature is δ1(connectionTo1Form A) on the SFGCSite2D p2/p3 plaquette surface"
        ∷ "Wired honestly: selected field strength is the existing SFGCSite2DFieldStrengthBridge from that curvature"
        ∷ "Wired honestly: the only local covariant operator package is the finite matter covariantLaplacian"
        ∷ "Narrowed: a lower edge-target probe transport exists for SFGCSite2D field-strength bridges, but no supplied link/fiber transport package is available"
        ∷ "Narrowed: the flat vacuum connection extends the selected 0-form exterior derivative by the δ0 candidate only"
        ∷ "Narrowed: diagonal phaseKernel4 gives a typed finite plaquette-density proxy, but not a Killing-form/tr(F^2) density"
        ∷ "Narrowed: exact primitive interfaces are now recorded for path transport, covariant difference, gauge-invariant quadratic density, and discrete YM action"
        ∷ "Not wired: no promoted covariant difference operation on selected field-strength values is available"
        ∷ "Not wired: no curvature quadratic density, plaquette integration, or trace pairing exists for a Yang-Mills action functional"
        ∷ "Therefore this is an operator/action skeleton only; it is not D * F = J or D F = 0"
        ∷ []
    }

record YMSFGCBianchiDFEqualsZeroBlocker : Set₁ where
  field
    selectedExteriorDerivativeSquaredZeroWitness :
      YMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    selectedExteriorDerivativeSquaredZeroWitnessIsCanonical :
      selectedExteriorDerivativeSquaredZeroWitness
      ≡
      canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    selectedCurvatureCarrier :
      G2DCC.DiscreteCurvatureCarrier SFGC.GaugeField

    selectedCurvatureCarrierIsCanonical :
      selectedCurvatureCarrier
      ≡
      canonicalYMSFGCDiscreteCurvatureCarrier

    exactBianchiTransportMissingPrimitives :
      List YangMillsBianchiMissingPrimitive

    exactBianchiTransportMissingPrimitivesAreCanonical :
      exactBianchiTransportMissingPrimitives
      ≡
      canonicalYangMillsBianchiMissingPrimitives

    exactCovariantDerivativeMissingPrimitives :
      List YMSFGCSelectedCovariantDerivativeMissingPrimitive

    exactCovariantDerivativeMissingPrimitivesAreCanonical :
      exactCovariantDerivativeMissingPrimitives
      ≡
      canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives

    requestedDFEqualsZeroTransportLaw :
      String

    independentOfHodgeStarAndCurrentAtThisStage :
      Bool

    independentOfHodgeStarAndCurrentAtThisStageIsTrue :
      independentOfHodgeStarAndCurrentAtThisStage ≡ true

    dFEqualsZeroPromoted :
      Bool

    dFEqualsZeroPromotedIsFalse :
      dFEqualsZeroPromoted ≡ false

    blockerBoundary :
      List String

canonicalYMSFGCBianchiDFEqualsZeroBlocker :
  YMSFGCBianchiDFEqualsZeroBlocker
canonicalYMSFGCBianchiDFEqualsZeroBlocker =
  record
    { selectedExteriorDerivativeSquaredZeroWitness =
        canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness
    ; selectedExteriorDerivativeSquaredZeroWitnessIsCanonical =
        refl
    ; selectedCurvatureCarrier =
        canonicalYMSFGCDiscreteCurvatureCarrier
    ; selectedCurvatureCarrierIsCanonical =
        refl
    ; exactBianchiTransportMissingPrimitives =
        canonicalYangMillsBianchiMissingPrimitives
    ; exactBianchiTransportMissingPrimitivesAreCanonical =
        refl
    ; exactCovariantDerivativeMissingPrimitives =
        canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives
    ; exactCovariantDerivativeMissingPrimitivesAreCanonical =
        refl
    ; requestedDFEqualsZeroTransportLaw =
        "transportSelectedExteriorD2ZeroToCovariantBianchi : selected δ1∘δ0 = 0 -> D_A F_A = 0"
    ; independentOfHodgeStarAndCurrentAtThisStage =
        true
    ; independentOfHodgeStarAndCurrentAtThisStageIsTrue =
        refl
    ; dFEqualsZeroPromoted =
        false
    ; dFEqualsZeroPromotedIsFalse =
        refl
    ; blockerBoundary =
        "Homogeneous side only: selected exterior δ1(δ0 f) = 0 is available on SFGCSite2D plaquette evaluation"
        ∷ "The remaining D F = 0 blocker is transport from exterior nilpotency to a covariant derivative on selected field strength"
        ∷ "This blocker is separate from Hodge star, current source, action variation, and D * F = J"
        ∷ "No covariant Yang-Mills Bianchi identity is promoted"
        ∷ []
    }

record YMSFGCBianchiAndDiscreteHodgeRouteAProgress : Set₁ where
  field
    selectedExteriorDerivativeSquaredZeroWitness :
      YMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    selectedExteriorDerivativeSquaredZeroWitnessIsCanonical :
      selectedExteriorDerivativeSquaredZeroWitness
      ≡
      canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    discreteBianchiReceipt :
      Bianchi.DiscreteBianchiIdentityReceipt

    discreteBianchiReceiptIsCanonical :
      discreteBianchiReceipt
      ≡
      Bianchi.canonicalDiscreteBianchiIdentityReceipt

    bianchiDFEqualsZeroBlocker :
      YMSFGCBianchiDFEqualsZeroBlocker

    bianchiDFEqualsZeroBlockerIsCanonical :
      bianchiDFEqualsZeroBlocker
      ≡
      canonicalYMSFGCBianchiDFEqualsZeroBlocker

    flatConnectionGaugeCompatibilityOfBianchiWitness :
      YMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness

    flatConnectionGaugeCompatibilityOfBianchiWitnessIsCanonical :
      flatConnectionGaugeCompatibilityOfBianchiWitness
      ≡
      canonicalYMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness

    typedDiscreteHodgeCovariantDerivativePrimitiveRequest :
      DiscreteHodgeCovariantDerivativePrimitiveTypedRequest

    typedDiscreteHodgeCovariantDerivativePrimitiveRequestIsCanonical :
      typedDiscreteHodgeCovariantDerivativePrimitiveRequest
      ≡
      canonicalDiscreteHodgeCovariantDerivativePrimitiveTypedRequest

    firstMissingRouteAPrerequisite :
      YangMillsFieldEquationMissingPrerequisite

    firstMissingRouteAPrerequisiteIsCovariantDerivative :
      firstMissingRouteAPrerequisite
      ≡
      missingCovariantDerivativeOnSelectedGaugeBundle

    secondMissingRouteAPrerequisite :
      YangMillsFieldEquationMissingPrerequisite

    secondMissingRouteAPrerequisiteIsHodgeStar :
      secondMissingRouteAPrerequisite
      ≡
      missingHodgeStarOnDiscreteCurvature

    routeAProgressPromoted :
      Bool

    routeAProgressPromotedIsFalse :
      routeAProgressPromoted ≡ false

    progressBoundary :
      List String

canonicalYMSFGCBianchiAndDiscreteHodgeRouteAProgress :
  YMSFGCBianchiAndDiscreteHodgeRouteAProgress
canonicalYMSFGCBianchiAndDiscreteHodgeRouteAProgress =
  record
    { selectedExteriorDerivativeSquaredZeroWitness =
        canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness
    ; selectedExteriorDerivativeSquaredZeroWitnessIsCanonical =
        refl
    ; discreteBianchiReceipt =
        Bianchi.canonicalDiscreteBianchiIdentityReceipt
    ; discreteBianchiReceiptIsCanonical =
        refl
    ; bianchiDFEqualsZeroBlocker =
        canonicalYMSFGCBianchiDFEqualsZeroBlocker
    ; bianchiDFEqualsZeroBlockerIsCanonical =
        refl
    ; flatConnectionGaugeCompatibilityOfBianchiWitness =
        canonicalYMSFGCFlatConnectionGaugeCompatibilityOfBianchiWitness
    ; flatConnectionGaugeCompatibilityOfBianchiWitnessIsCanonical =
        refl
    ; typedDiscreteHodgeCovariantDerivativePrimitiveRequest =
        canonicalDiscreteHodgeCovariantDerivativePrimitiveTypedRequest
    ; typedDiscreteHodgeCovariantDerivativePrimitiveRequestIsCanonical =
        refl
    ; firstMissingRouteAPrerequisite =
        missingCovariantDerivativeOnSelectedGaugeBundle
    ; firstMissingRouteAPrerequisiteIsCovariantDerivative =
        refl
    ; secondMissingRouteAPrerequisite =
        missingHodgeStarOnDiscreteCurvature
    ; secondMissingRouteAPrerequisiteIsHodgeStar =
        refl
    ; routeAProgressPromoted =
        false
    ; routeAProgressPromotedIsFalse =
        refl
    ; progressBoundary =
        "Route A baseline: selected exterior δ1∘δ0 = 0 and discrete Bianchi receipt are wired on the SFGCSite2D carrier"
        ∷ "Flat local progress: gauge compatibility of that bounded Bianchi plaquette law is witnessed for the selected vacuum-connection route"
        ∷ "Bianchi transport remains blocked on covariant derivative extension from selected exterior derivative to D_A on field-strength values"
        ∷ "Discrete Hodge-star/covariant-derivative target remains a typed request only; no local Hodge-star inhabitant is supplied"
        ∷ "Route A progress stays non-promoting until covariant derivative and Hodge-star prerequisites are inhabited"
        ∷ []
    }

record YMSFGCSourcedDStarFEqualsJBlocker : Set₁ where
  field
    selectedOperatorSkeleton :
      YMSFGCSelectedOperatorSkeleton

    selectedOperatorSkeletonIsCanonical :
      selectedOperatorSkeleton
      ≡
      canonicalYMSFGCSelectedOperatorSkeleton

    exactVariationalMissingPrimitives :
      List YangMillsVariationalEquationMissingPrimitive

    exactVariationalMissingPrimitivesAreCanonical :
      exactVariationalMissingPrimitives
      ≡
      canonicalYangMillsVariationalEquationMissingPrimitives

    exactActionFunctionalMissingPrimitives :
      List YMSFGCActionFunctionalMissingPrimitive

    exactActionFunctionalMissingPrimitivesAreCanonical :
      exactActionFunctionalMissingPrimitives
      ≡
      canonicalYMSFGCActionFunctionalMissingPrimitives

    requestedHodgeStarField :
      String

    requestedCurrentSourceField :
      String

    requestedActionVariationLaw :
      String

    notDischargedBySelectedExteriorD2Zero :
      Bool

    notDischargedBySelectedExteriorD2ZeroIsTrue :
      notDischargedBySelectedExteriorD2Zero ≡ true

    dStarFEqualsJPromoted :
      Bool

    dStarFEqualsJPromotedIsFalse :
      dStarFEqualsJPromoted ≡ false

    blockerBoundary :
      List String

canonicalYMSFGCSourcedDStarFEqualsJBlocker :
  YMSFGCSourcedDStarFEqualsJBlocker
canonicalYMSFGCSourcedDStarFEqualsJBlocker =
  record
    { selectedOperatorSkeleton =
        canonicalYMSFGCSelectedOperatorSkeleton
    ; selectedOperatorSkeletonIsCanonical =
        refl
    ; exactVariationalMissingPrimitives =
        canonicalYangMillsVariationalEquationMissingPrimitives
    ; exactVariationalMissingPrimitivesAreCanonical =
        refl
    ; exactActionFunctionalMissingPrimitives =
        canonicalYMSFGCActionFunctionalMissingPrimitives
    ; exactActionFunctionalMissingPrimitivesAreCanonical =
        refl
    ; requestedHodgeStarField =
        "hodgeStarOnSFGCSite2DDiscreteCurvature : SFGCSite2DDiscrete2Form -> DualCurvatureCarrier"
    ; requestedCurrentSourceField =
        "currentSourceForSFGCSite2D : CurrentCarrier with coupling to D * F"
    ; requestedActionVariationLaw =
        "variationalDStarFEqualsJLaw : variation of selected Yang-Mills action yields D * F = J"
    ; notDischargedBySelectedExteriorD2Zero =
        true
    ; notDischargedBySelectedExteriorD2ZeroIsTrue =
        refl
    ; dStarFEqualsJPromoted =
        false
    ; dStarFEqualsJPromotedIsFalse =
        refl
    ; blockerBoundary =
        "Sourced side only: D * F = J is blocked by missing Hodge star, current carrier/coupling, action functional, variation pairing, and Euler-Lagrange law"
        ∷ "The selected exterior d^2 = 0 witness does not discharge this sourced equation"
        ∷ "This blocker is separate from the homogeneous D F = 0 transport blocker"
        ∷ "No variational Yang-Mills field equation is promoted"
        ∷ []
    }

record YMSFGCCovariantHodgeCurrentPackageRequest : Set₁ where
  field
    selectedCurvatureCarrier :
      G2DCC.DiscreteCurvatureCarrier SFGC.GaugeField

    selectedCurvatureCarrierIsCanonical :
      selectedCurvatureCarrier
      ≡
      canonicalYMSFGCDiscreteCurvatureCarrier

    availableFiniteMatterGaugeCoupling :
      SFGC.ShiftFiniteGaugeCoupling

    availableFiniteMatterGaugeCouplingIsCanonical :
      availableFiniteMatterGaugeCoupling
      ≡
      SFGC.shiftFiniteGaugeCoupling

    availableDiscreteExteriorDerivative0 :
      SFGC.SFGCSite2DDiscrete0Form →
      SFGC.SFGCSite2DDiscrete1Form

    availableDiscreteExteriorDerivative0IsSFGC :
      availableDiscreteExteriorDerivative0
      ≡
      SFGC.sfgcSite2Dδ₀

    availableDiscreteExteriorDerivative1 :
      SFGC.SFGCSite2DDiscrete1Form →
      SFGC.SFGCSite2DDiscrete2Form

    availableDiscreteExteriorDerivative1IsSFGC :
      availableDiscreteExteriorDerivative1
      ≡
      SFGC.sfgcSite2Dδ₁

    availableCurvatureToFieldStrength :
      SFGC.SFGCSite2DDiscrete2Form →
      SFGC.SFGCSite2DFieldStrengthBridge

    availableCurvatureToFieldStrengthIsSFGC :
      availableCurvatureToFieldStrength
      ≡
      SFGC.sfgcSite2DFieldStrengthFromCurvature

    selectedExteriorDerivativeSquaredZeroWitness :
      YMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    selectedExteriorDerivativeSquaredZeroWitnessIsCanonical :
      selectedExteriorDerivativeSquaredZeroWitness
      ≡
      canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    selectedOperatorSkeleton :
      YMSFGCSelectedOperatorSkeleton

    selectedOperatorSkeletonIsCanonical :
      selectedOperatorSkeleton
      ≡
      canonicalYMSFGCSelectedOperatorSkeleton

    bianchiDFEqualsZeroBlocker :
      YMSFGCBianchiDFEqualsZeroBlocker

    bianchiDFEqualsZeroBlockerIsCanonical :
      bianchiDFEqualsZeroBlocker
      ≡
      canonicalYMSFGCBianchiDFEqualsZeroBlocker

    routeABianchiAndDiscreteHodgeProgress :
      YMSFGCBianchiAndDiscreteHodgeRouteAProgress

    routeABianchiAndDiscreteHodgeProgressIsCanonical :
      routeABianchiAndDiscreteHodgeProgress
      ≡
      canonicalYMSFGCBianchiAndDiscreteHodgeRouteAProgress

    sourcedDStarFEqualsJBlocker :
      YMSFGCSourcedDStarFEqualsJBlocker

    sourcedDStarFEqualsJBlockerIsCanonical :
      sourcedDStarFEqualsJBlocker
      ≡
      canonicalYMSFGCSourcedDStarFEqualsJBlocker

    primitiveInterfaceRequest :
      YMSFGCPrimitiveInterfaceRequest

    primitiveInterfaceRequestIsCanonical :
      primitiveInterfaceRequest
      ≡
      canonicalYMSFGCPrimitiveInterfaceRequest

    exactMissingFields :
      List YangMillsFieldEquationMissingPrerequisite

    exactMissingFieldsAreCanonical :
      exactMissingFields
      ≡
      canonicalYangMillsFieldEquationMissingPrerequisites

    requestedCovariantDerivativeField :
      String

    requestedHodgeStarField :
      String

    requestedCurrentSourceField :
      String

    requestedDStarFEqualsJLawField :
      String

    requestedYangMillsBianchiLawField :
      String

    exactVariationalEquationMissingFields :
      List YangMillsVariationalEquationMissingPrimitive

    exactVariationalEquationMissingFieldsAreCanonical :
      exactVariationalEquationMissingFields
      ≡
      canonicalYangMillsVariationalEquationMissingPrimitives

    exactBianchiTransportMissingFields :
      List YangMillsBianchiMissingPrimitive

    exactBianchiTransportMissingFieldsAreCanonical :
      exactBianchiTransportMissingFields
      ≡
      canonicalYangMillsBianchiMissingPrimitives

    exactSelectedCovariantDerivativeMissingPrimitives :
      List YMSFGCSelectedCovariantDerivativeMissingPrimitive

    exactSelectedCovariantDerivativeMissingPrimitivesAreCanonical :
      exactSelectedCovariantDerivativeMissingPrimitives
      ≡
      canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives

    exactActionFunctionalMissingPrimitives :
      List YMSFGCActionFunctionalMissingPrimitive

    exactActionFunctionalMissingPrimitivesAreCanonical :
      exactActionFunctionalMissingPrimitives
      ≡
      canonicalYMSFGCActionFunctionalMissingPrimitives

    requestedBianchiTransportField :
      String

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

    packageBoundary :
      List String

canonicalYMSFGCCovariantHodgeCurrentPackageRequest :
  YMSFGCCovariantHodgeCurrentPackageRequest
canonicalYMSFGCCovariantHodgeCurrentPackageRequest =
  record
    { selectedCurvatureCarrier =
        canonicalYMSFGCDiscreteCurvatureCarrier
    ; selectedCurvatureCarrierIsCanonical =
        refl
    ; availableFiniteMatterGaugeCoupling =
        SFGC.shiftFiniteGaugeCoupling
    ; availableFiniteMatterGaugeCouplingIsCanonical =
        refl
    ; availableDiscreteExteriorDerivative0 =
        SFGC.sfgcSite2Dδ₀
    ; availableDiscreteExteriorDerivative0IsSFGC =
        refl
    ; availableDiscreteExteriorDerivative1 =
        SFGC.sfgcSite2Dδ₁
    ; availableDiscreteExteriorDerivative1IsSFGC =
        refl
    ; availableCurvatureToFieldStrength =
        SFGC.sfgcSite2DFieldStrengthFromCurvature
    ; availableCurvatureToFieldStrengthIsSFGC =
        refl
    ; selectedExteriorDerivativeSquaredZeroWitness =
        canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness
    ; selectedExteriorDerivativeSquaredZeroWitnessIsCanonical =
        refl
    ; selectedOperatorSkeleton =
        canonicalYMSFGCSelectedOperatorSkeleton
    ; selectedOperatorSkeletonIsCanonical =
        refl
    ; bianchiDFEqualsZeroBlocker =
        canonicalYMSFGCBianchiDFEqualsZeroBlocker
    ; bianchiDFEqualsZeroBlockerIsCanonical =
        refl
    ; routeABianchiAndDiscreteHodgeProgress =
        canonicalYMSFGCBianchiAndDiscreteHodgeRouteAProgress
    ; routeABianchiAndDiscreteHodgeProgressIsCanonical =
        refl
    ; sourcedDStarFEqualsJBlocker =
        canonicalYMSFGCSourcedDStarFEqualsJBlocker
    ; sourcedDStarFEqualsJBlockerIsCanonical =
        refl
    ; primitiveInterfaceRequest =
        canonicalYMSFGCPrimitiveInterfaceRequest
    ; primitiveInterfaceRequestIsCanonical =
        refl
    ; exactMissingFields =
        canonicalYangMillsFieldEquationMissingPrerequisites
    ; exactMissingFieldsAreCanonical =
        refl
    ; requestedCovariantDerivativeField =
        "covariantDerivativeOnSFGCSite2DFieldStrength : GaugeField -> SFGCSite2DFieldStrengthBridge -> Set"
    ; requestedHodgeStarField =
        "hodgeStarOnSFGCSite2DDiscreteCurvature : SFGCSite2DDiscrete2Form -> Set"
    ; requestedCurrentSourceField =
        "currentSourceForSFGCSite2D : Set with coupling to D * F"
    ; requestedDStarFEqualsJLawField =
        "dStarFEqualsJLaw : covariantDerivativeOnSFGCSite2DFieldStrength A (* F) == J"
    ; requestedYangMillsBianchiLawField =
        "yangMillsBianchiDFEqualsZeroLaw : covariantDerivativeOnSFGCSite2DFieldStrength A F == 0"
    ; exactVariationalEquationMissingFields =
        canonicalYangMillsVariationalEquationMissingPrimitives
    ; exactVariationalEquationMissingFieldsAreCanonical =
        refl
    ; exactBianchiTransportMissingFields =
        canonicalYangMillsBianchiMissingPrimitives
    ; exactBianchiTransportMissingFieldsAreCanonical =
        refl
    ; exactSelectedCovariantDerivativeMissingPrimitives =
        canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives
    ; exactSelectedCovariantDerivativeMissingPrimitivesAreCanonical =
        refl
    ; exactActionFunctionalMissingPrimitives =
        canonicalYMSFGCActionFunctionalMissingPrimitives
    ; exactActionFunctionalMissingPrimitivesAreCanonical =
        refl
    ; requestedBianchiTransportField =
        "transportSelectedExteriorD2ZeroToCovariantBianchi : selected δ1∘δ0 = 0 -> D_A F_A = 0"
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
    ; packageBoundary =
        "Wired honestly: selected curvature is δ1(connectionTo1Form A), and selected field strength is SFGC.sfgcSite2DFieldStrengthFromCurvature of that curvature"
        ∷ "Wired honestly: SFGC supplies finite matter covariantLaplacian, not a Yang-Mills derivative on curvature"
        ∷ "Wired honestly: SFGCSite2D supplies δ0, δ1, Wilson-loop curvature, and curvature-to-field-strength bridge"
        ∷ "Wired honestly: SFGC.sfgcSite2DP2P3BoundaryOfBoundaryZero supplies selected exterior d^2 = 0 on p2/p3 plaquette evaluation"
        ∷ "Split blocker: homogeneous D F = 0 is gated only on covariant transport from selected exterior d^2 = 0"
        ∷ "Split blocker: sourced D * F = J is gated on Hodge star, current coupling, action functional, variation pairing, and Euler-Lagrange law"
        ∷ "First covariant-derivative primitive missing: field-strength transport/action on the selected gauge bundle"
        ∷ "First action-functional primitive missing: curvature quadratic density on Phase4 plaquette values"
        ∷ "No local primitive supplies a Hodge star on SFGCSite2DDiscrete2Form"
        ∷ "No local primitive supplies a current/source carrier coupled to D * F"
        ∷ "Lower local candidates inhabit SFGCPathTransportPrimitive, CovariantDifferencePrimitive, GaugeInvariantQuadraticDensityPrimitive, and DiscreteYMActionPrimitive only as non-promoting surfaces"
        ∷ "Closed first path blocker: identityPathTargetLaw for SFGCSite2DEdge is supplied by SFGC.sfgcSite2DIdentityEdgeTargetLaw"
        ∷ "Next path promotion blocker: no link/fiber field-strength transport law along p2/p3 SFGCSite2DEdge paths is supplied"
        ∷ "No local primitive supplies the variational Yang-Mills equation D * F = J"
        ∷ "No local primitive transports selected exterior d^2 = 0 to covariant Yang-Mills D F = 0"
        ∷ "All YM, Maxwell, spectral-gap, continuum-Clay, and terminal promotions remain false"
        ∷ []
    }

record YMSFGCFieldStrengthTransportActionVariationAbsenceLedger : Set₁ where
  field
    lowerPrimitiveCandidateBundle :
      YMSFGCLowerPrimitiveCandidateBundle

    lowerPrimitiveCandidateBundleIsCanonical :
      lowerPrimitiveCandidateBundle
      ≡
      canonicalYMSFGCLowerPrimitiveCandidateBundle

    compiledFieldStrengthTransport :
      SFGC.SFGCSite2DEdge →
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    compiledFieldStrengthTransportIsEdgeProbe :
      compiledFieldStrengthTransport
      ≡
      sfgcEdgeFieldStrengthTransportCandidate

    finalPrimitiveLowerLawCandidate :
      YMSFGCFinalPrimitiveLowerLawCandidate

    finalPrimitiveLowerLawCandidateIsCanonical :
      finalPrimitiveLowerLawCandidate
      ≡
      canonicalYMSFGCFinalPrimitiveLowerLawCandidate

    arbitraryGaugeHolonomyKillingAttempt :
      YMSFGCArbitraryGaugeHolonomyKillingAttempt

    arbitraryGaugeHolonomyKillingAttemptIsCanonical :
      arbitraryGaugeHolonomyKillingAttempt
      ≡
      canonicalYMSFGCArbitraryGaugeHolonomyKillingAttempt

    requestedFieldStrengthFibreActionType :
      Set

    requestedGaugeCovarianceLawType :
      Set

    requestedActionVariationTargetType :
      Set

    requestedHolonomyConjugationUnderGaugeTransformType :
      Set

    requestedKillingFormAdInvarianceType :
      Set

    requestedDiscreteVariationIBPType :
      Set

    realYMPrimitiveSupplyRequestPack :
      YMSFGCRealYMPrimitiveSupplyRequestPack

    realYMPrimitiveSupplyRequestPackIsCanonical :
      realYMPrimitiveSupplyRequestPack
      ≡
      canonicalYMSFGCRealYMPrimitiveSupplyRequestPack

    userSuppliedRealYMPrimitiveTypedRequest :
      YMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    userSuppliedRealYMPrimitiveTypedRequestIsCanonical :
      userSuppliedRealYMPrimitiveTypedRequest
      ≡
      canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    finalPrimitiveMathBlockers :
      List YMSFGCFinalPrimitiveMathBlocker

    finalPrimitiveMathBlockersAreCanonical :
      finalPrimitiveMathBlockers
      ≡
      canonicalYMSFGCFinalPrimitiveMathBlockers

    firstTransportBlocker :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    firstTransportBlockerIsFieldStrengthAction :
      firstTransportBlocker
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    firstVariationalBlocker :
      YangMillsVariationalEquationMissingPrimitive

    firstVariationalBlockerIsVariationPairing :
      firstVariationalBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    ledgerPromoted :
      Bool

    ledgerPromotedIsFalse :
      ledgerPromoted ≡ false

    absenceBoundary :
      List String

record YMSFGCNonFlatHodgeCurrentActionSupplyProgress : Set₁ where
  field
    realYMPrimitiveSupplyRequestPack :
      YMSFGCRealYMPrimitiveSupplyRequestPack

    realYMPrimitiveSupplyRequestPackIsCanonical :
      realYMPrimitiveSupplyRequestPack
      ≡
      canonicalYMSFGCRealYMPrimitiveSupplyRequestPack

    covariantHodgeCurrentPackageRequest :
      YMSFGCCovariantHodgeCurrentPackageRequest

    covariantHodgeCurrentPackageRequestIsCanonical :
      covariantHodgeCurrentPackageRequest
      ≡
      canonicalYMSFGCCovariantHodgeCurrentPackageRequest

    transportActionVariationAbsenceLedger :
      YMSFGCFieldStrengthTransportActionVariationAbsenceLedger

    transportActionVariationAbsenceLedgerIsCanonical :
      transportActionVariationAbsenceLedger
      ≡
      transportActionVariationAbsenceLedger

    routeAFirstMissingPrimitive :
      YangMillsBianchiMissingPrimitive

    routeAFirstMissingPrimitiveIsCovariantExtension :
      routeAFirstMissingPrimitive
      ≡
      missingCovariantDerivativeExtendsSelectedExteriorDerivative

    routeBFirstMissingPrimitive :
      YangMillsVariationalEquationMissingPrimitive

    routeBFirstMissingPrimitiveIsVariationPairing :
      routeBFirstMissingPrimitive
      ≡
      missingVariationPairingForSelectedHodgeStar

    gate4EinsteinTensorSymbol :
      FVMetric.FactorVecTangentDirection →
      FVMetric.FactorVecTangentDirection →
      ℚ

    gate4EinsteinTensorSymbolIsCanonical :
      gate4EinsteinTensorSymbol
      ≡
      FVMetric.factorVecUnitP2LorentzEinsteinTensor

    supplyPromoted :
      Bool

    supplyPromotedIsFalse :
      supplyPromoted ≡ false

    supplyBoundary :
      List String

canonicalYMSFGCFieldStrengthTransportActionVariationAbsenceLedger :
  YMSFGCFieldStrengthTransportActionVariationAbsenceLedger
canonicalYMSFGCFieldStrengthTransportActionVariationAbsenceLedger =
  record
    { lowerPrimitiveCandidateBundle =
        canonicalYMSFGCLowerPrimitiveCandidateBundle
    ; lowerPrimitiveCandidateBundleIsCanonical =
        refl
    ; compiledFieldStrengthTransport =
        sfgcEdgeFieldStrengthTransportCandidate
    ; compiledFieldStrengthTransportIsEdgeProbe =
        refl
    ; finalPrimitiveLowerLawCandidate =
        canonicalYMSFGCFinalPrimitiveLowerLawCandidate
    ; finalPrimitiveLowerLawCandidateIsCanonical =
        refl
    ; arbitraryGaugeHolonomyKillingAttempt =
        canonicalYMSFGCArbitraryGaugeHolonomyKillingAttempt
    ; arbitraryGaugeHolonomyKillingAttemptIsCanonical =
        refl
    ; requestedFieldStrengthFibreActionType =
        SFGC.SFGCSite2DEdge →
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; requestedGaugeCovarianceLawType =
        (transport :
          SFGC.SFGCSite2DEdge →
          SFGC.SFGCSite2DFieldStrengthBridge →
          SFGC.SFGCSite2DFieldStrengthBridge) →
        (gauge : SFGS.GaugeTransform) →
        (edge : SFGC.SFGCSite2DEdge) →
        (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
        SFGC.SFGCSite2DFieldStrengthBridge.curvature2Form
          (transport edge fieldStrength)
        ≡
        SFGC.SFGCSite2DFieldStrengthBridge.curvature2Form
          fieldStrength
    ; requestedActionVariationTargetType =
        SFGC.GaugeField →
        YangMillsVariationalEquationMissingPrimitive
    ; requestedHolonomyConjugationUnderGaugeTransformType =
        (gauge : SFGS.GaugeTransform) →
        (A : SFGC.GaugeField) →
        (plaquette : SFGC.SFGCSite2DPlaquette) →
        SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
          (sfgcSelectedFieldStrengthBridge
            (SFGC.transformGauge gauge A))
          plaquette
        ≡
        SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
          (sfgcSelectedFieldStrengthAdjointTransportCandidate
            gauge
            (sfgcSelectedFieldStrengthBridge A))
          plaquette
    ; requestedKillingFormAdInvarianceType =
        (density :
          SFGC.SFGCSite2DFieldStrengthBridge →
          SFGC.SFGCSite2DPlaquette →
          ℤ) →
        (gauge : SFGS.GaugeTransform) →
        (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
        (plaquette : SFGC.SFGCSite2DPlaquette) →
        density
          (sfgcSelectedFieldStrengthAdjointTransportCandidate
            gauge fieldStrength)
          plaquette
        ≡
        density fieldStrength plaquette
    ; requestedDiscreteVariationIBPType =
        (variationOfAction :
          SFGC.GaugeField →
          SFGC.GaugeField →
          ℤ) →
        (eulerLagrangePairing :
          SFGC.GaugeField →
          SFGC.GaugeField →
          ℤ) →
        (boundaryTerm :
          SFGC.GaugeField →
          SFGC.GaugeField →
          ℤ) →
        (A δA : SFGC.GaugeField) →
        variationOfAction A δA
        ≡
        _+ℤ_
          (eulerLagrangePairing A δA)
          (boundaryTerm A δA)
    ; realYMPrimitiveSupplyRequestPack =
        canonicalYMSFGCRealYMPrimitiveSupplyRequestPack
    ; realYMPrimitiveSupplyRequestPackIsCanonical =
        refl
    ; userSuppliedRealYMPrimitiveTypedRequest =
        canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; userSuppliedRealYMPrimitiveTypedRequestIsCanonical =
        refl
    ; finalPrimitiveMathBlockers =
        canonicalYMSFGCFinalPrimitiveMathBlockers
    ; finalPrimitiveMathBlockersAreCanonical =
        refl
    ; firstTransportBlocker =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; firstTransportBlockerIsFieldStrengthAction =
        refl
    ; firstVariationalBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; firstVariationalBlockerIsVariationPairing =
        refl
    ; ledgerPromoted =
        false
    ; ledgerPromotedIsFalse =
        refl
    ; absenceBoundary =
        "Exact supplied-interface gap: the compiled transport is the edge-target probe, not a supplied gauge-covariant fibre action"
        ∷ "Round-2 holonomy result: arbitrary selected SFGC holonomy conjugation is closed by flat finite-C4 square cancellation"
        ∷ "Lower final-law candidates discharge only constant-gauge vacuum holonomy covariance, trivial-adjoint phase-zero density invariance, and zero-variation IBP"
        ∷ "Exact non-flat covariance gap: no proof inhabits a requested non-flat transport covariance law for arbitrary selected SFGCSite2DEdge transport"
        ∷ "Exact action-variation gap: no variation pairing for the selected Hodge-star/action surface is supplied"
        ∷ "Precise missing math 1: holonomy conjugation under gauge transform for selected SFGCSite2D plaquette field strength"
        ∷ "Precise missing math 2: Killing-form/trace Ad-invariance for the selected finite field-strength algebra"
        ∷ "Precise missing math 3: discrete variation/integration-by-parts deriving the Euler-Lagrange D * F = J target"
        ∷ "Typed request pack names the exact user-supplied non-flat connection, holonomy telescoping, Lie/trace Ad-invariance, discrete Hodge/covariant derivative, and discrete IBP supplies needed beyond the selected flat C4 candidates"
        ∷ "The ledger records typed holes only and keeps Yang-Mills promotion false"
        ∷ []
    }

canonicalYMSFGCNonFlatHodgeCurrentActionSupplyProgress :
  YMSFGCNonFlatHodgeCurrentActionSupplyProgress
canonicalYMSFGCNonFlatHodgeCurrentActionSupplyProgress =
  record
    { realYMPrimitiveSupplyRequestPack =
        canonicalYMSFGCRealYMPrimitiveSupplyRequestPack
    ; realYMPrimitiveSupplyRequestPackIsCanonical =
        refl
    ; covariantHodgeCurrentPackageRequest =
        canonicalYMSFGCCovariantHodgeCurrentPackageRequest
    ; covariantHodgeCurrentPackageRequestIsCanonical =
        refl
    ; transportActionVariationAbsenceLedger =
        canonicalYMSFGCFieldStrengthTransportActionVariationAbsenceLedger
    ; transportActionVariationAbsenceLedgerIsCanonical =
        refl
    ; routeAFirstMissingPrimitive =
        missingCovariantDerivativeExtendsSelectedExteriorDerivative
    ; routeAFirstMissingPrimitiveIsCovariantExtension =
        refl
    ; routeBFirstMissingPrimitive =
        missingVariationPairingForSelectedHodgeStar
    ; routeBFirstMissingPrimitiveIsVariationPairing =
        refl
    ; gate4EinsteinTensorSymbol =
        FVMetric.factorVecUnitP2LorentzEinsteinTensor
    ; gate4EinsteinTensorSymbolIsCanonical =
        refl
    ; supplyPromoted =
        false
    ; supplyPromotedIsFalse =
        refl
    ; supplyBoundary =
        "Non-flat/Hodge/current/action supply surface is wired to the canonical real primitive request pack and covariant-Hodge-current package request"
        ∷ "Route A first strict blocker remains covariant transport from selected exterior nilpotency to D F = 0"
        ∷ "Route B first strict blocker remains variation pairing for the selected Hodge-star/action surface"
        ∷ "This progress surface records exact supply dependencies only and keeps Yang-Mills promotion false"
        ∷ []
    }

record YMSFGCYMActionIBPSourceProgress : Set₁ where
  field
    nonFlatHodgeCurrentActionSupplyProgress :
      YMSFGCNonFlatHodgeCurrentActionSupplyProgress

    nonFlatHodgeCurrentActionSupplyProgressIsCanonical :
      nonFlatHodgeCurrentActionSupplyProgress
      ≡
      canonicalYMSFGCNonFlatHodgeCurrentActionSupplyProgress

    killingAdInvarianceFirstMissingPrimitive :
      YMSFGCRealKillingAdInvarianceIrreducibility

    killingAdInvarianceFirstMissingPrimitiveIsLieAlgebraCarrier :
      killingAdInvarianceFirstMissingPrimitive
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    actionVariationIBPFirstMissingPrimitive :
      YangMillsVariationalEquationMissingPrimitive

    actionVariationIBPFirstMissingPrimitiveIsVariationPairing :
      actionVariationIBPFirstMissingPrimitive
      ≡
      missingVariationPairingForSelectedHodgeStar

    sourcedDStarFEqualsJBlocker :
      YMSFGCSourcedDStarFEqualsJBlocker

    sourcedDStarFEqualsJBlockerIsCanonical :
      sourcedDStarFEqualsJBlocker
      ≡
      canonicalYMSFGCSourcedDStarFEqualsJBlocker

    homogeneousBianchiDFEqualsZeroBlocker :
      YMSFGCBianchiDFEqualsZeroBlocker

    homogeneousBianchiDFEqualsZeroBlockerIsCanonical :
      homogeneousBianchiDFEqualsZeroBlocker
      ≡
      canonicalYMSFGCBianchiDFEqualsZeroBlocker

    routeAFirstMissingPrimitive :
      YangMillsBianchiMissingPrimitive

    routeAFirstMissingPrimitiveIsCovariantExtension :
      routeAFirstMissingPrimitive
      ≡
      missingCovariantDerivativeExtendsSelectedExteriorDerivative

    routeBFirstMissingPrimitive :
      YangMillsVariationalEquationMissingPrimitive

    routeBFirstMissingPrimitiveIsVariationPairing :
      routeBFirstMissingPrimitive
      ≡
      missingVariationPairingForSelectedHodgeStar

    routeABSeparationMaintained :
      Bool

    routeABSeparationMaintainedIsTrue :
      routeABSeparationMaintained ≡ true

    progressPromoted :
      Bool

    progressPromotedIsFalse :
      progressPromoted ≡ false

    progressBoundary :
      List String

canonicalYMSFGCYMActionIBPSourceProgress :
  YMSFGCYMActionIBPSourceProgress
canonicalYMSFGCYMActionIBPSourceProgress =
  record
    { nonFlatHodgeCurrentActionSupplyProgress =
        canonicalYMSFGCNonFlatHodgeCurrentActionSupplyProgress
    ; nonFlatHodgeCurrentActionSupplyProgressIsCanonical =
        refl
    ; killingAdInvarianceFirstMissingPrimitive =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; killingAdInvarianceFirstMissingPrimitiveIsLieAlgebraCarrier =
        refl
    ; actionVariationIBPFirstMissingPrimitive =
        missingVariationPairingForSelectedHodgeStar
    ; actionVariationIBPFirstMissingPrimitiveIsVariationPairing =
        refl
    ; sourcedDStarFEqualsJBlocker =
        canonicalYMSFGCSourcedDStarFEqualsJBlocker
    ; sourcedDStarFEqualsJBlockerIsCanonical =
        refl
    ; homogeneousBianchiDFEqualsZeroBlocker =
        canonicalYMSFGCBianchiDFEqualsZeroBlocker
    ; homogeneousBianchiDFEqualsZeroBlockerIsCanonical =
        refl
    ; routeAFirstMissingPrimitive =
        missingCovariantDerivativeExtendsSelectedExteriorDerivative
    ; routeAFirstMissingPrimitiveIsCovariantExtension =
        refl
    ; routeBFirstMissingPrimitive =
        missingVariationPairingForSelectedHodgeStar
    ; routeBFirstMissingPrimitiveIsVariationPairing =
        refl
    ; routeABSeparationMaintained =
        true
    ; routeABSeparationMaintainedIsTrue =
        refl
    ; progressPromoted =
        false
    ; progressPromotedIsFalse =
        refl
    ; progressBoundary =
        "Route A/B separation remains explicit: homogeneous D F = 0 stays on the Bianchi transport blocker while sourced D * F = J stays on the action-variation blocker"
        ∷ "Killing-side first strict blocker remains a supplied Lie-algebra carrier for a nontrivial finite gauge sector"
        ∷ "Action/IBP-side first strict blocker remains variation pairing for the selected Hodge-star/action surface"
        ∷ "No Yang-Mills promotion follows from this progress surface"
        ∷ []
    }

sfgcSelectedHodgeStarLowerCandidate :
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2DFieldStrengthBridge
sfgcSelectedHodgeStarLowerCandidate fieldStrength =
  fieldStrength

record YMSFGCMiddleM1M2ImplementationProgress : Set₁ where
  field
    endpointGaugeFactor :
      SFGS.GaugeTransform →
      SFGC.SFGCSite2D →
      SPTI4.Phase4

    endpointGaugeFactorIsSelectedPrimaryCoordinate :
      endpointGaugeFactor
      ≡
      sfgcSelectedEndpointGaugeFactor

    selectedEndpointPlaquetteConjugationLaw :
      (gauge : SFGS.GaugeTransform) →
      (A : SFGC.GaugeField) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        (sfgcSelectedFieldStrengthBridge
          (SFGC.transformGauge gauge A))
        plaquette
      ≡
      sfgcPhase4ConjugateBy
        (sfgcSelectedEndpointGaugeFactor
          gauge
          (SFGC.sfgcSite2DPlaquetteSW plaquette))
        (SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
          (sfgcSelectedFieldStrengthBridge A)
          plaquette)

    selectedEndpointPlaquetteConjugationLawIsFlatC4 :
      selectedEndpointPlaquetteConjugationLaw
      ≡
      sfgcSelectedEndpointPlaquetteConjugationLaw

    endpointGaugeFactorSourceTargetReceipt :
      YMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt

    endpointGaugeFactorSourceTargetReceiptIsCanonical :
      endpointGaugeFactorSourceTargetReceipt
      ≡
      canonicalYMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt

    nonFlatPlaquetteConjugationTargetSurface :
      Set

    nonFlatPlaquetteConjugationTargetSurfaceIsUserSuppliedRequest :
      nonFlatPlaquetteConjugationTargetSurface
      ≡
      YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedHolonomyConjugationLawType
        canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    finiteLieAlgebraCarrier :
      Set

    finiteLieAlgebraCarrierIsLocalFiniteLie3 :
      finiteLieAlgebraCarrier
      ≡
      YMSFGCLocalFiniteLie3Carrier

    finiteLieBracket :
      YMSFGCLocalFiniteLie3Carrier →
      YMSFGCLocalFiniteLie3Carrier →
      YMSFGCLocalFiniteLie3Carrier

    finiteLieBracketIsLocalFiniteLie3 :
      finiteLieBracket
      ≡
      localFiniteLie3Bracket

    connectionOneFormAsFibreAlgebraLocalReceipt :
      YMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt

    connectionOneFormAsFibreAlgebraLocalReceiptIsCanonical :
      connectionOneFormAsFibreAlgebraLocalReceipt
      ≡
      canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt

    nontrivialFieldStrengthAdjointAction :
      SPTI4.Phase4 →
      YMSFGCLocalFiniteLie3Carrier →
      YMSFGCLocalFiniteLie3Carrier

    nontrivialFieldStrengthAdjointActionIsLocalPhaseAdjoint :
      nontrivialFieldStrengthAdjointAction
      ≡
      localFiniteLie3PhaseAdjointAction

    nontrivialFieldStrengthAdjointActionWitness :
      nontrivialFieldStrengthAdjointAction
        SPTI4.φ1
        (lieBasis signPos axisX)
      ≡
      lieBasis signNeg axisX

    traceOrKillingPairing :
      YMSFGCLocalFiniteLie3Carrier →
      YMSFGCLocalFiniteLie3Carrier →
      ℤ

    traceOrKillingPairingIsLocalTraceProbe :
      traceOrKillingPairing
      ≡
      localFiniteLie3TracePairing

    traceOrKillingAdInvariance :
      (phase : SPTI4.Phase4) →
      (x y : YMSFGCLocalFiniteLie3Carrier) →
      traceOrKillingPairing
        (nontrivialFieldStrengthAdjointAction phase x)
        (nontrivialFieldStrengthAdjointAction phase y)
      ≡
      traceOrKillingPairing x y

    endpointGaugeTraceOrKillingAdInvariance :
      (gauge : SFGS.GaugeTransform) →
      (site : SFGC.SFGCSite2D) →
      (x y : YMSFGCLocalFiniteLie3Carrier) →
      traceOrKillingPairing
        (sfgcEndpointPhaseAdjointAction gauge site x)
        (sfgcEndpointPhaseAdjointAction gauge site y)
      ≡
      traceOrKillingPairing x y

    hodgeStarTargetSurface :
      Set

    hodgeStarTargetSurfaceIsSelectedFieldStrengthEndomap :
      hodgeStarTargetSurface
      ≡
      (SFGC.SFGCSite2DFieldStrengthBridge →
       SFGC.SFGCSite2DFieldStrengthBridge)

    hodgeStarLowerCandidate :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    hodgeStarLowerCandidateIsIdentityProbe :
      hodgeStarLowerCandidate
      ≡
      sfgcSelectedHodgeStarLowerCandidate

    routeBDStarFEqualsJTargetSurface :
      Set

    routeBDStarFEqualsJTargetSurfaceIsUserSuppliedRequest :
      routeBDStarFEqualsJTargetSurface
      ≡
      YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedDStarFEqualsJLawType
        canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    routeBDiscreteIBPTargetSurface :
      Set

    routeBDiscreteIBPTargetSurfaceIsFull :
      routeBDiscreteIBPTargetSurface
      ≡
      YMSFGCFullDiscreteVariationIBPLawType

    zeroVariationIBPLowerCandidate :
      YMSFGCDiscreteVariationIBPLowerCandidate

    zeroVariationIBPLowerCandidateIsCanonical :
      zeroVariationIBPLowerCandidate
      ≡
      canonicalYMSFGCDiscreteVariationIBPLowerCandidate

    firstM1Blocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstM1BlockerIsNonFlatCurvature :
      firstM1Blocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    firstM2Blocker :
      YangMillsVariationalEquationMissingPrimitive

    firstM2BlockerIsVariationPairing :
      firstM2Blocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    nonFlatCurvatureTheoremSurface :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    nonFlatCurvatureTheoremSurfaceIsCurvature :
      nonFlatCurvatureTheoremSurface
      ≡
      nonFlatCurvatureWitness sfgcCanonicalNonFlatCurvature2Form

    ymPromoted :
      Bool

    ymPromotedIsFalse :
      ymPromoted ≡ false

    progressBoundary :
      List String

canonicalYMSFGCMiddleM1M2ImplementationProgress :
  YMSFGCMiddleM1M2ImplementationProgress
canonicalYMSFGCMiddleM1M2ImplementationProgress =
  record
    { endpointGaugeFactor =
        sfgcSelectedEndpointGaugeFactor
    ; endpointGaugeFactorIsSelectedPrimaryCoordinate =
        refl
    ; selectedEndpointPlaquetteConjugationLaw =
        sfgcSelectedEndpointPlaquetteConjugationLaw
    ; selectedEndpointPlaquetteConjugationLawIsFlatC4 =
        refl
    ; endpointGaugeFactorSourceTargetReceipt =
        canonicalYMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt
    ; endpointGaugeFactorSourceTargetReceiptIsCanonical =
        refl
    ; nonFlatPlaquetteConjugationTargetSurface =
        YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedHolonomyConjugationLawType
          canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; nonFlatPlaquetteConjugationTargetSurfaceIsUserSuppliedRequest =
        refl
    ; finiteLieAlgebraCarrier =
        YMSFGCLocalFiniteLie3Carrier
    ; finiteLieAlgebraCarrierIsLocalFiniteLie3 =
        refl
    ; finiteLieBracket =
        localFiniteLie3Bracket
    ; finiteLieBracketIsLocalFiniteLie3 =
        refl
    ; connectionOneFormAsFibreAlgebraLocalReceipt =
        canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt
    ; connectionOneFormAsFibreAlgebraLocalReceiptIsCanonical =
        refl
    ; nontrivialFieldStrengthAdjointAction =
        localFiniteLie3PhaseAdjointAction
    ; nontrivialFieldStrengthAdjointActionIsLocalPhaseAdjoint =
        refl
    ; nontrivialFieldStrengthAdjointActionWitness =
        localFiniteLie3PhaseAdjointActionNontrivial
    ; traceOrKillingPairing =
        localFiniteLie3TracePairing
    ; traceOrKillingPairingIsLocalTraceProbe =
        refl
    ; traceOrKillingAdInvariance =
        localFiniteLie3PhaseAdjointTraceAdInvariance
    ; endpointGaugeTraceOrKillingAdInvariance =
        sfgcEndpointPhaseAdjointTraceAdInvariance
    ; hodgeStarTargetSurface =
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; hodgeStarTargetSurfaceIsSelectedFieldStrengthEndomap =
        refl
    ; hodgeStarLowerCandidate =
        sfgcSelectedHodgeStarLowerCandidate
    ; hodgeStarLowerCandidateIsIdentityProbe =
        refl
    ; routeBDStarFEqualsJTargetSurface =
        YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedDStarFEqualsJLawType
          canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; routeBDStarFEqualsJTargetSurfaceIsUserSuppliedRequest =
        refl
    ; routeBDiscreteIBPTargetSurface =
        YMSFGCFullDiscreteVariationIBPLawType
    ; routeBDiscreteIBPTargetSurfaceIsFull =
        refl
    ; zeroVariationIBPLowerCandidate =
        canonicalYMSFGCDiscreteVariationIBPLowerCandidate
    ; zeroVariationIBPLowerCandidateIsCanonical =
        refl
    ; firstM1Blocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; firstM1BlockerIsNonFlatCurvature =
        refl
    ; firstM2Blocker =
        missingVariationPairingForSelectedHodgeStar
    ; firstM2BlockerIsVariationPairing =
        refl
    ; nonFlatCurvatureTheoremSurface =
        nonFlatCurvatureWitness sfgcCanonicalNonFlatCurvature2Form
    ; nonFlatCurvatureTheoremSurfaceIsCurvature =
        refl
    ; ymPromoted =
        false
    ; ymPromotedIsFalse =
        refl
    ; progressBoundary =
        "m1 staged: endpoint gauge factors are exact Phase4 factors at the SFGCSite2D primary coordinate of the plaquette SW endpoint"
        ∷ "m1 strengthened: endpoint gauge factors are exposed at edge sources and targets, with bottom/left source factors tied to the plaquette SW corner"
        ∷ "m1 lower law: selected endpoint plaquette conjugation is inhabited only because the current SFGC Wilson-loop curvature cancels to φ0"
        ∷ "m1 target retained: the real non-flat plaquette conjugation law remains the user-supplied holonomy request over a non-flat connection carrier"
        ∷ "m1 finite carrier: local finite 3-axis Lie bracket, nontrivial phase-adjoint sign action, trace/Killing probe, and Ad-invariance are inhabited locally"
        ∷ "u2 staged: selected connectionOneFormAsFibreAlgebra maps the start-point Phase4 gauge value into local finite Lie3 and embeds it into the local SU3 scaffold"
        ∷ "m1 blocker retained: no SFGC field-strength representation law or non-flat connection curvature maps the selected plaquette field strength into that finite carrier"
        ∷ "m2 staged: selected Hodge star is only an identity endomap target on field-strength bridges, not a metric Hodge operator"
        ∷ "m2 lower law: zero IBP remains the only inhabited variational shape"
        ∷ "m2 target retained: D * F = J and full discrete IBP remain user-supplied Route B targets gated by variation pairing, Hodge star, source coupling, and action variation"
        ∷ "No non-flat curvature, Yang-Mills equation, Maxwell closure, or promotion flag is constructed"
        ∷ []
    }

record YangMillsFieldEquationObstruction : Set₁ where
  field
    status :
      YangMillsFieldEquationObstructionStatus

    upstreamCurvatureObstruction :
      G2DCC.G2ShiftGaugeCurvatureUpstreamObstruction

    upstreamCurvatureObstructionIsCanonical :
      upstreamCurvatureObstruction
      ≡
      G2DCC.canonicalSFGCGaugeCurvatureUpstreamObstruction

    upstreamFirstMissing :
      G2DCC.G2ShiftGaugeCurvatureMissingField

    upstreamFirstMissingIsPrimeLattice2CellLayer :
      upstreamFirstMissing
      ≡
      G2DCC.missingPrimeLattice2CellLayer

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

    nondegeneratePlaquetteRequest :
      G2DCC.SFGCNondegeneratePlaquetteCarrierRequest

    nondegeneratePlaquetteRequestIsCanonical :
      nondegeneratePlaquetteRequest
      ≡
      G2DCC.canonicalSFGCNondegeneratePlaquetteCarrierRequest

    nondegeneratePlaquetteMissingAPIs :
      List G2DCC.SFGCNondegeneratePlaquetteMissingAPI

    nondegeneratePlaquetteMissingAPIsAreCanonical :
      nondegeneratePlaquetteMissingAPIs
      ≡
      G2DCC.SFGCNondegeneratePlaquetteCarrierRequest.missingAPIs
        G2DCC.canonicalSFGCNondegeneratePlaquetteCarrierRequest

    implementedNondegeneratePlaquetteAPI :
      G2NP.RequiredNondegenerateSFGCPlaquetteAPI SFGC.GaugeField

    implementedNondegeneratePlaquetteAPIIsCanonical :
      implementedNondegeneratePlaquetteAPI
      ≡
      canonicalYMSFGCNondegeneratePlaquetteAPI

    implementedDiscreteCurvatureCarrier :
      G2DCC.DiscreteCurvatureCarrier SFGC.GaugeField

    implementedDiscreteCurvatureCarrierIsFromPlaquetteAPI :
      implementedDiscreteCurvatureCarrier
      ≡
      canonicalYMSFGCDiscreteCurvatureCarrier

    discreteBianchiReceipt :
      Bianchi.DiscreteBianchiIdentityReceipt

    discreteBianchiReceiptIsCanonical :
      discreteBianchiReceipt
      ≡
      Bianchi.canonicalDiscreteBianchiIdentityReceipt

    covariantHodgeCurrentPackageRequest :
      YMSFGCCovariantHodgeCurrentPackageRequest

    covariantHodgeCurrentPackageRequestIsCanonical :
      covariantHodgeCurrentPackageRequest
      ≡
      canonicalYMSFGCCovariantHodgeCurrentPackageRequest

    selectedOperatorSkeleton :
      YMSFGCSelectedOperatorSkeleton

    selectedOperatorSkeletonIsCanonical :
      selectedOperatorSkeleton
      ≡
      canonicalYMSFGCSelectedOperatorSkeleton

    primitiveInterfaceRequest :
      YMSFGCPrimitiveInterfaceRequest

    primitiveInterfaceRequestIsCanonical :
      primitiveInterfaceRequest
      ≡
      canonicalYMSFGCPrimitiveInterfaceRequest

    nonAbelianCovariantDerivativeTheoremThinReceipt :
      YMSFGCNonAbelianCovariantDerivativeTheoremThinReceipt

    nonAbelianCovariantDerivativeTheoremThinReceiptIsCanonical :
      nonAbelianCovariantDerivativeTheoremThinReceipt
      ≡
      canonicalYMSFGCNonAbelianCovariantDerivativeTheoremThinReceipt

    transportActionVariationAbsenceLedger :
      YMSFGCFieldStrengthTransportActionVariationAbsenceLedger

    transportActionVariationAbsenceLedgerIsCanonical :
      transportActionVariationAbsenceLedger
      ≡
      canonicalYMSFGCFieldStrengthTransportActionVariationAbsenceLedger

    realYMPrimitiveSupplyRequestPack :
      YMSFGCRealYMPrimitiveSupplyRequestPack

    realYMPrimitiveSupplyRequestPackIsCanonical :
      realYMPrimitiveSupplyRequestPack
      ≡
      canonicalYMSFGCRealYMPrimitiveSupplyRequestPack

    gate3NonFlatSFGCSite2DHandoffReceipt :
      YMSFGCGate3NonFlatSFGCSite2DHandoffReceipt

    gate3NonFlatSFGCSite2DHandoffReceiptIsCanonical :
      gate3NonFlatSFGCSite2DHandoffReceipt
      ≡
      canonicalYMSFGCGate3NonFlatSFGCSite2DHandoffReceipt

    gate3M1NonFlatCurvatureBlockerChainLedger :
      YMSFGCGate3M1NonFlatCurvatureBlockerChainLedger

    gate3M1NonFlatCurvatureBlockerChainLedgerIsCanonical :
      gate3M1NonFlatCurvatureBlockerChainLedger
      ≡
      canonicalYMSFGCGate3M1NonFlatCurvatureBlockerChainLedger

    gate3NonFlatCurvaturePrimitiveAdvancement :
      YMSFGCGate3NonFlatCurvaturePrimitiveAdvancement

    gate3NonFlatCurvaturePrimitiveAdvancementIsCanonical :
      gate3NonFlatCurvaturePrimitiveAdvancement
      ≡
      canonicalYMSFGCGate3NonFlatCurvaturePrimitiveAdvancement

    userSuppliedRealYMPrimitiveTypedRequest :
      YMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    userSuppliedRealYMPrimitiveTypedRequestIsCanonical :
      userSuppliedRealYMPrimitiveTypedRequest
      ≡
      canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    arbitraryGaugeHolonomyKillingAttempt :
      YMSFGCArbitraryGaugeHolonomyKillingAttempt

    arbitraryGaugeHolonomyKillingAttemptIsCanonical :
      arbitraryGaugeHolonomyKillingAttempt
      ≡
      canonicalYMSFGCArbitraryGaugeHolonomyKillingAttempt

    bianchiDFEqualsZeroBlocker :
      YMSFGCBianchiDFEqualsZeroBlocker

    bianchiDFEqualsZeroBlockerIsCanonical :
      bianchiDFEqualsZeroBlocker
      ≡
      canonicalYMSFGCBianchiDFEqualsZeroBlocker

    sourcedDStarFEqualsJBlocker :
      YMSFGCSourcedDStarFEqualsJBlocker

    sourcedDStarFEqualsJBlockerIsCanonical :
      sourcedDStarFEqualsJBlocker
      ≡
      canonicalYMSFGCSourcedDStarFEqualsJBlocker

    ymActionIBPSourceProgress :
      YMSFGCYMActionIBPSourceProgress

    ymActionIBPSourceProgressIsCanonical :
      ymActionIBPSourceProgress
      ≡
      canonicalYMSFGCYMActionIBPSourceProgress

    middleM1M2ImplementationProgress :
      YMSFGCMiddleM1M2ImplementationProgress

    middleM1M2ImplementationProgressIsCanonical :
      middleM1M2ImplementationProgress
      ≡
      canonicalYMSFGCMiddleM1M2ImplementationProgress

    finalPrimitiveLowerLawCandidate :
      YMSFGCFinalPrimitiveLowerLawCandidate

    finalPrimitiveLowerLawCandidateIsCanonical :
      finalPrimitiveLowerLawCandidate
      ≡
      canonicalYMSFGCFinalPrimitiveLowerLawCandidate

    exactCanonicalMissingPrimitiveSummary :
      YMSFGCExactCanonicalMissingPrimitiveSummary

    exactCanonicalMissingPrimitiveSummaryIsCanonical :
      exactCanonicalMissingPrimitiveSummary
      ≡
      canonicalYMSFGCExactCanonicalMissingPrimitiveSummary

    firstMissingPrerequisite :
      YangMillsFieldEquationMissingPrerequisite

    firstMissingPrerequisiteIsCovariantDerivative :
      firstMissingPrerequisite
      ≡
      missingCovariantDerivativeOnSelectedGaugeBundle

    missingPrerequisites :
      List YangMillsFieldEquationMissingPrerequisite

    missingPrerequisitesAreCanonical :
      missingPrerequisites
      ≡
      canonicalYangMillsFieldEquationMissingPrerequisites

    bianchiMissingPrimitives :
      List YangMillsBianchiMissingPrimitive

    bianchiMissingPrimitivesAreCanonical :
      bianchiMissingPrimitives
      ≡
      canonicalYangMillsBianchiMissingPrimitives

    selectedExteriorDerivativeSquaredZeroWitness :
      YMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    selectedExteriorDerivativeSquaredZeroWitnessIsCanonical :
      selectedExteriorDerivativeSquaredZeroWitness
      ≡
      canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    variationalEquationMissingPrimitives :
      List YangMillsVariationalEquationMissingPrimitive

    variationalEquationMissingPrimitivesAreCanonical :
      variationalEquationMissingPrimitives
      ≡
      canonicalYangMillsVariationalEquationMissingPrimitives

    selectedCovariantDerivativeMissingPrimitives :
      List YMSFGCSelectedCovariantDerivativeMissingPrimitive

    selectedCovariantDerivativeMissingPrimitivesAreCanonical :
      selectedCovariantDerivativeMissingPrimitives
      ≡
      canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives

    selectedFiniteGaugeSectorBridge :
      YMSFGCSelectedFiniteGaugeSectorBridge

    selectedFiniteGaugeSectorBridgeIsCanonical :
      selectedFiniteGaugeSectorBridge
      ≡
      canonicalYMSFGCSelectedFiniteGaugeSectorBridge

    nonAbelianCovariantDerivativeMissingPrimitives :
      List YMSFGCNonAbelianCovariantDerivativeMissingPrimitive

    nonAbelianCovariantDerivativeMissingPrimitivesAreCanonical :
      nonAbelianCovariantDerivativeMissingPrimitives
      ≡
      canonicalYMSFGCNonAbelianCovariantDerivativeMissingPrimitives

    actionFunctionalMissingPrimitives :
      List YMSFGCActionFunctionalMissingPrimitive

    actionFunctionalMissingPrimitivesAreCanonical :
      actionFunctionalMissingPrimitives
      ≡
      canonicalYMSFGCActionFunctionalMissingPrimitives

    requiredInterface :
      List String

    nonPromotionBoundary :
      List String

canonicalYangMillsFieldEquationObstruction :
  YangMillsFieldEquationObstruction
canonicalYangMillsFieldEquationObstruction =
  record
    { status =
        blockedBeforeSFGCCurvatureCarrierNoPromotion
    ; upstreamCurvatureObstruction =
        G2DCC.canonicalSFGCGaugeCurvatureUpstreamObstruction
    ; upstreamCurvatureObstructionIsCanonical =
        refl
    ; upstreamFirstMissing =
        G2DCC.G2ShiftGaugeCurvatureUpstreamObstruction.firstMissing
          G2DCC.canonicalSFGCGaugeCurvatureUpstreamObstruction
    ; upstreamFirstMissingIsPrimeLattice2CellLayer =
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
    ; nondegeneratePlaquetteRequest =
        G2DCC.canonicalSFGCNondegeneratePlaquetteCarrierRequest
    ; nondegeneratePlaquetteRequestIsCanonical =
        refl
    ; nondegeneratePlaquetteMissingAPIs =
        G2DCC.SFGCNondegeneratePlaquetteCarrierRequest.missingAPIs
          G2DCC.canonicalSFGCNondegeneratePlaquetteCarrierRequest
    ; nondegeneratePlaquetteMissingAPIsAreCanonical =
        refl
    ; implementedNondegeneratePlaquetteAPI =
        canonicalYMSFGCNondegeneratePlaquetteAPI
    ; implementedNondegeneratePlaquetteAPIIsCanonical =
        refl
    ; implementedDiscreteCurvatureCarrier =
        canonicalYMSFGCDiscreteCurvatureCarrier
    ; implementedDiscreteCurvatureCarrierIsFromPlaquetteAPI =
        refl
    ; discreteBianchiReceipt =
        Bianchi.canonicalDiscreteBianchiIdentityReceipt
    ; discreteBianchiReceiptIsCanonical =
        refl
    ; covariantHodgeCurrentPackageRequest =
        canonicalYMSFGCCovariantHodgeCurrentPackageRequest
    ; covariantHodgeCurrentPackageRequestIsCanonical =
        refl
    ; selectedOperatorSkeleton =
        canonicalYMSFGCSelectedOperatorSkeleton
    ; selectedOperatorSkeletonIsCanonical =
        refl
    ; primitiveInterfaceRequest =
        canonicalYMSFGCPrimitiveInterfaceRequest
    ; primitiveInterfaceRequestIsCanonical =
        refl
    ; nonAbelianCovariantDerivativeTheoremThinReceipt =
        canonicalYMSFGCNonAbelianCovariantDerivativeTheoremThinReceipt
    ; nonAbelianCovariantDerivativeTheoremThinReceiptIsCanonical =
        refl
    ; transportActionVariationAbsenceLedger =
        canonicalYMSFGCFieldStrengthTransportActionVariationAbsenceLedger
    ; transportActionVariationAbsenceLedgerIsCanonical =
        refl
    ; realYMPrimitiveSupplyRequestPack =
        canonicalYMSFGCRealYMPrimitiveSupplyRequestPack
    ; realYMPrimitiveSupplyRequestPackIsCanonical =
        refl
    ; gate3NonFlatSFGCSite2DHandoffReceipt =
        canonicalYMSFGCGate3NonFlatSFGCSite2DHandoffReceipt
    ; gate3NonFlatSFGCSite2DHandoffReceiptIsCanonical =
        refl
    ; gate3M1NonFlatCurvatureBlockerChainLedger =
        canonicalYMSFGCGate3M1NonFlatCurvatureBlockerChainLedger
    ; gate3M1NonFlatCurvatureBlockerChainLedgerIsCanonical =
        refl
    ; gate3NonFlatCurvaturePrimitiveAdvancement =
        canonicalYMSFGCGate3NonFlatCurvaturePrimitiveAdvancement
    ; gate3NonFlatCurvaturePrimitiveAdvancementIsCanonical =
        refl
    ; userSuppliedRealYMPrimitiveTypedRequest =
        canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; userSuppliedRealYMPrimitiveTypedRequestIsCanonical =
        refl
    ; arbitraryGaugeHolonomyKillingAttempt =
        canonicalYMSFGCArbitraryGaugeHolonomyKillingAttempt
    ; arbitraryGaugeHolonomyKillingAttemptIsCanonical =
        refl
    ; bianchiDFEqualsZeroBlocker =
        canonicalYMSFGCBianchiDFEqualsZeroBlocker
    ; bianchiDFEqualsZeroBlockerIsCanonical =
        refl
    ; sourcedDStarFEqualsJBlocker =
        canonicalYMSFGCSourcedDStarFEqualsJBlocker
    ; sourcedDStarFEqualsJBlockerIsCanonical =
        refl
    ; ymActionIBPSourceProgress =
        canonicalYMSFGCYMActionIBPSourceProgress
    ; ymActionIBPSourceProgressIsCanonical =
        refl
    ; middleM1M2ImplementationProgress =
        canonicalYMSFGCMiddleM1M2ImplementationProgress
    ; middleM1M2ImplementationProgressIsCanonical =
        refl
    ; finalPrimitiveLowerLawCandidate =
        canonicalYMSFGCFinalPrimitiveLowerLawCandidate
    ; finalPrimitiveLowerLawCandidateIsCanonical =
        refl
    ; exactCanonicalMissingPrimitiveSummary =
        canonicalYMSFGCExactCanonicalMissingPrimitiveSummary
    ; exactCanonicalMissingPrimitiveSummaryIsCanonical =
        refl
    ; firstMissingPrerequisite =
        missingCovariantDerivativeOnSelectedGaugeBundle
    ; firstMissingPrerequisiteIsCovariantDerivative =
        refl
    ; missingPrerequisites =
        canonicalYangMillsFieldEquationMissingPrerequisites
    ; missingPrerequisitesAreCanonical =
        refl
    ; bianchiMissingPrimitives =
        canonicalYangMillsBianchiMissingPrimitives
    ; bianchiMissingPrimitivesAreCanonical =
        refl
    ; selectedExteriorDerivativeSquaredZeroWitness =
        canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness
    ; selectedExteriorDerivativeSquaredZeroWitnessIsCanonical =
        refl
    ; variationalEquationMissingPrimitives =
        canonicalYangMillsVariationalEquationMissingPrimitives
    ; variationalEquationMissingPrimitivesAreCanonical =
        refl
    ; selectedCovariantDerivativeMissingPrimitives =
        canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives
    ; selectedCovariantDerivativeMissingPrimitivesAreCanonical =
        refl
    ; selectedFiniteGaugeSectorBridge =
        canonicalYMSFGCSelectedFiniteGaugeSectorBridge
    ; selectedFiniteGaugeSectorBridgeIsCanonical =
        refl
    ; nonAbelianCovariantDerivativeMissingPrimitives =
        canonicalYMSFGCNonAbelianCovariantDerivativeMissingPrimitives
    ; nonAbelianCovariantDerivativeMissingPrimitivesAreCanonical =
        refl
    ; actionFunctionalMissingPrimitives =
        canonicalYMSFGCActionFunctionalMissingPrimitives
    ; actionFunctionalMissingPrimitivesAreCanonical =
        refl
    ; requiredInterface =
        "SFGCSite2D nondegenerate plaquette API now supplies DiscreteCurvatureCarrier SFGC.GaugeField"
        ∷ "SFGC.shiftFiniteGaugeCoupling supplies a finite matter covariantLaplacian only; it is not the requested Yang-Mills derivative on curvature"
        ∷ "Selected operator skeleton now wires A -> δ1(connectionTo1Form A) -> SFGCSite2DFieldStrengthBridge"
        ∷ "First covariant derivative primitive below the top-level blocker: field-strength transport/action on the selected gauge bundle"
        ∷ "Non-abelian covariant derivative receipt now names fibre bracket, Jacobi witness, D_A = d + [A,_], and D_A^2(s) = [F_A,s] as theorem-thin targets"
        ∷ "Local finite 3-axis bracket witness inhabits bracket/negation/antisymmetry/Jacobi and now includes a concrete typed SFGC fibre representation candidate into local finite SU(3)"
        ∷ "First non-abelian fibre blocker after that candidate map is the missing connection one-form as a fibre-algebra element"
        ∷ "First action functional primitive below the top-level blocker: curvature quadratic density on Phase4 plaquette values"
        ∷ "Exact primitive request records: SFGCPathTransportPrimitive, CovariantDifferencePrimitive, NonAbelianCovariantDerivativePrimitive, GaugeInvariantQuadraticDensityPrimitive, DiscreteYMActionPrimitive"
        ∷ "Exact absence ledger now pins the remaining supplied fibre-action, transport covariance, and action-variation holes"
        ∷ "Exact real primitive supply requests now pin user-supplied non-flat lattice connection, holonomy telescoping, Lie/trace Ad-invariance, discrete Hodge/covariant derivative, and discrete IBP supplies"
        ∷ "Gate 3 m1 blocker-chain ledger now exposes the first missing non-flat curvature field plus endpoint, holonomy, Ad-action, Lie-carrier, pairing, and Ad-invariance request types"
        ∷ "Gate 3 m1 primitive advancement now wires the concrete SFGCSite2DDiscrete1Form curvature probe, finite C4 endpoint factors, finite C4 plaquette holonomy conjugation, and finite C4 trace/Ad receipt into the main obstruction record"
        ∷ "Middle m1/m2 progress stages endpoint gauge factors, selected endpoint conjugation, finite Lie trace/Ad probes, a Hodge target surface, and a Route B IBP target without constructing non-flat curvature"
        ∷ "Arbitrary-gauge selected holonomy conjugation is now closed by finite-C4 flat square cancellation"
        ∷ "Non-flat holonomy conjugation remains irreducible without non-flat plaquette curvature, endpoint gauge factors, and nontrivial Ad action"
        ∷ "Killing Ad-invariance remains irreducible beyond the trivial selected C4 identity-adjoint density law"
        ∷ "D F = 0 and D * F = J blockers are split into separate canonical records"
        ∷ "Lower final-law candidates now discharge constant-gauge vacuum holonomy covariance, trivial-adjoint phase-zero density invariance, and zero-variation IBP only"
        ∷ "Final primitive math blockers: non-flat holonomy conjugation under gauge transform, Killing-form Ad-invariance, and discrete variation/IBP"
        ∷ "SFGC.sfgcSite2DP2P3BoundaryOfBoundaryZero supplies selected exterior d^2 = 0 over the p2/p3 plaquette evaluation"
        ∷ "Next required: covariantDerivative acting on the selected field-strength and dual-field carriers"
        ∷ "hodgeStar for the selected discrete 2-form/field-strength carrier"
        ∷ "currentSource carrier and coupling law J for D * F = J"
        ∷ "Variational Yang-Mills law D * F = J derived from an action, variation pairing, Hodge star, and source coupling"
        ∷ "Bianchi transport law D F = 0 derived from selected exterior nilpotency plus covariant-derivative compatibility, Stokes, or Jacobi data"
        ∷ []
    ; nonPromotionBoundary =
        "This obstruction now packages the available SFGCSite2D curvature carrier"
        ∷ "It also packages an operator/action skeleton from connectionTo1Form, δ1, fieldStrengthFromCurvature, and curvature evaluation"
        ∷ "It packages typed primitive interfaces plus lower non-promoting inhabitants for transport, covariant difference, density, and action"
        ∷ "It packages a theorem-thin non-abelian D_A receipt and a local finite 3-axis bracket witness"
        ∷ "The local bracket witness plus typed representation candidate does not promote because no gauge-compatible representation law or connection one-form action into that carrier is supplied"
        ∷ "It records an exact typed absence ledger for field-strength fibre action covariance and action variation"
        ∷ "It records a real primitive supply request pack rather than treating the flat Phase4 candidates as non-flat Yang-Mills primitives"
        ∷ "It records that SFGC already exposes the exact site/edge/plaquette endpoints needed by a user-supplied non-flat connection request"
        ∷ "It records the Gate 3 m1 first missing field as a user-supplied non-flat plaquette curvature field and keeps curvatureConstructed false"
        ∷ "It records the concrete finite C4 lower advancement while keeping promotionClaimed false and the strict non-flat/SU3 promotion blocker intact"
        ∷ "It records middle m1/m2 staged surfaces for endpoint gauge factors, selected endpoint conjugation, finite trace/Ad probes, Hodge target, and IBP target while keeping non-flat curvature unconstructed"
        ∷ "It proves arbitrary selected SFGC holonomy conjugation by reducing both transformed and untransformed selected Wilson loops to φ0"
        ∷ "It splits homogeneous D F = 0 from sourced D * F = J blockers"
        ∷ "It records degenerate lower final-law candidates while preserving the arbitrary-law blockers"
        ∷ "The final ledger names the missing non-flat holonomy-conjugation, Killing Ad-invariance, and discrete variation/IBP primitives"
        ∷ "Legacy G2DCC obstruction records still report missingShiftGaugeFieldGaugeConnection for the older right-edge-only API"
        ∷ "It proves only selected exterior δ1(δ0 f) vanishing on plaquette evaluation"
        ∷ "It does not construct a covariant derivative, Hodge star, or current source"
        ∷ "It does not prove D * F = J"
        ∷ "It does not transport exterior d^2 = 0 to covariant Yang-Mills D F = 0"
        ∷ "It does not promote Yang-Mills closure, Maxwell closure, spectral gap, mass gap, Clay, or terminal claims"
        ∷ []
    }

yangMillsCovariantHodgeCurrentPackageRequestIsExact :
  YangMillsFieldEquationObstruction.covariantHodgeCurrentPackageRequest
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCCovariantHodgeCurrentPackageRequest
yangMillsCovariantHodgeCurrentPackageRequestIsExact =
  refl

yangMillsSelectedOperatorSkeletonIsExact :
  YangMillsFieldEquationObstruction.selectedOperatorSkeleton
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCSelectedOperatorSkeleton
yangMillsSelectedOperatorSkeletonIsExact =
  refl

yangMillsPrimitiveDefinitionCandidateSurfaceLowerBundleIsExact :
  YMSFGCPrimitiveDefinitionCandidateSurface.lowerPrimitiveCandidateBundle
    canonicalYMSFGCPrimitiveDefinitionCandidateSurface
  ≡
  canonicalYMSFGCLowerPrimitiveCandidateBundle
yangMillsPrimitiveDefinitionCandidateSurfaceLowerBundleIsExact =
  refl

yangMillsTransportActionVariationAbsenceLedgerIsExact :
  YangMillsFieldEquationObstruction.transportActionVariationAbsenceLedger
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCFieldStrengthTransportActionVariationAbsenceLedger
yangMillsTransportActionVariationAbsenceLedgerIsExact =
  refl

yangMillsGate3M1NonFlatCurvatureBlockerChainLedgerIsExact :
  YangMillsFieldEquationObstruction.gate3M1NonFlatCurvatureBlockerChainLedger
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCGate3M1NonFlatCurvatureBlockerChainLedger
yangMillsGate3M1NonFlatCurvatureBlockerChainLedgerIsExact =
  refl

yangMillsGate3M1FirstRemainingHolonomyBlockerIsExact :
  YMSFGCGate3M1NonFlatCurvatureBlockerChainLedger.firstRemainingHolonomyBlocker
    canonicalYMSFGCGate3M1NonFlatCurvatureBlockerChainLedger
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsGate3M1FirstRemainingHolonomyBlockerIsExact =
  refl

yangMillsGate3NonFlatCurvaturePrimitiveAdvancementIsExact :
  YangMillsFieldEquationObstruction.gate3NonFlatCurvaturePrimitiveAdvancement
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCGate3NonFlatCurvaturePrimitiveAdvancement
yangMillsGate3NonFlatCurvaturePrimitiveAdvancementIsExact =
  refl

yangMillsGate3NonFlatCurvaturePrimitiveAdvancementStillNonPromoting :
  YMSFGCGate3NonFlatCurvaturePrimitiveAdvancement.promotionClaimed
    canonicalYMSFGCGate3NonFlatCurvaturePrimitiveAdvancement
  ≡
  false
yangMillsGate3NonFlatCurvaturePrimitiveAdvancementStillNonPromoting =
  refl

yangMillsGate3NonFlatCurvaturePrimitiveAdvancementResidualBlocker :
  YMSFGCGate3NonFlatCurvaturePrimitiveAdvancement.advancedNonFlatCurvaturePrimitive
    canonicalYMSFGCGate3NonFlatCurvaturePrimitiveAdvancement
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsGate3NonFlatCurvaturePrimitiveAdvancementResidualBlocker =
  refl

yangMillsRealYMPrimitiveSupplyRequestPackIsExact :
  YangMillsFieldEquationObstruction.realYMPrimitiveSupplyRequestPack
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCRealYMPrimitiveSupplyRequestPack
yangMillsRealYMPrimitiveSupplyRequestPackIsExact =
  refl

yangMillsGate3NonFlatSFGCSite2DHandoffReceiptIsExact :
  YangMillsFieldEquationObstruction.gate3NonFlatSFGCSite2DHandoffReceipt
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCGate3NonFlatSFGCSite2DHandoffReceipt
yangMillsGate3NonFlatSFGCSite2DHandoffReceiptIsExact =
  refl

yangMillsUserSuppliedRealYMPrimitiveTypedRequestIsExact :
  YangMillsFieldEquationObstruction.userSuppliedRealYMPrimitiveTypedRequest
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
yangMillsUserSuppliedRealYMPrimitiveTypedRequestIsExact =
  refl

yangMillsTransportActionVariationFinalPrimitiveMathBlockers :
  YMSFGCFieldStrengthTransportActionVariationAbsenceLedger.finalPrimitiveMathBlockers
    canonicalYMSFGCFieldStrengthTransportActionVariationAbsenceLedger
  ≡
  canonicalYMSFGCFinalPrimitiveMathBlockers
yangMillsTransportActionVariationFinalPrimitiveMathBlockers =
  refl

yangMillsArbitraryGaugeHolonomyKillingAttemptIsExact :
  YangMillsFieldEquationObstruction.arbitraryGaugeHolonomyKillingAttempt
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCArbitraryGaugeHolonomyKillingAttempt
yangMillsArbitraryGaugeHolonomyKillingAttemptIsExact =
  refl

yangMillsBianchiDFEqualsZeroBlockerIsExact :
  YangMillsFieldEquationObstruction.bianchiDFEqualsZeroBlocker
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCBianchiDFEqualsZeroBlocker
yangMillsBianchiDFEqualsZeroBlockerIsExact =
  refl

yangMillsSourcedDStarFEqualsJBlockerIsExact :
  YangMillsFieldEquationObstruction.sourcedDStarFEqualsJBlocker
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCSourcedDStarFEqualsJBlocker
yangMillsSourcedDStarFEqualsJBlockerIsExact =
  refl

yangMillsYMActionIBPSourceProgressIsExact :
  YangMillsFieldEquationObstruction.ymActionIBPSourceProgress
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCYMActionIBPSourceProgress
yangMillsYMActionIBPSourceProgressIsExact =
  refl

yangMillsMiddleM1M2ImplementationProgressIsExact :
  YangMillsFieldEquationObstruction.middleM1M2ImplementationProgress
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCMiddleM1M2ImplementationProgress
yangMillsMiddleM1M2ImplementationProgressIsExact =
  refl

yangMillsMiddleM1M2EndpointGaugeFactorSourceTargetReceiptIsExact :
  YMSFGCMiddleM1M2ImplementationProgress.endpointGaugeFactorSourceTargetReceipt
    canonicalYMSFGCMiddleM1M2ImplementationProgress
  ≡
  canonicalYMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt
yangMillsMiddleM1M2EndpointGaugeFactorSourceTargetReceiptIsExact =
  refl

yangMillsMiddleM1M2ConnectionOneFormAsFibreAlgebraLocalReceiptIsExact :
  YMSFGCMiddleM1M2ImplementationProgress.connectionOneFormAsFibreAlgebraLocalReceipt
    canonicalYMSFGCMiddleM1M2ImplementationProgress
  ≡
  canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt
yangMillsMiddleM1M2ConnectionOneFormAsFibreAlgebraLocalReceiptIsExact =
  refl

yangMillsMiddleM1M2FirstM1BlockerIsNonFlatCurvature :
  YMSFGCMiddleM1M2ImplementationProgress.firstM1Blocker
    canonicalYMSFGCMiddleM1M2ImplementationProgress
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsMiddleM1M2FirstM1BlockerIsNonFlatCurvature =
  refl

yangMillsMiddleM1M2FirstM2BlockerIsVariationPairing :
  YMSFGCMiddleM1M2ImplementationProgress.firstM2Blocker
    canonicalYMSFGCMiddleM1M2ImplementationProgress
  ≡
  missingVariationPairingForSelectedHodgeStar
yangMillsMiddleM1M2FirstM2BlockerIsVariationPairing =
  refl

yangMillsYMActionIBPSourceNonFlatHodgeCurrentActionSupplyProgressIsExact :
  YMSFGCYMActionIBPSourceProgress.nonFlatHodgeCurrentActionSupplyProgress
    (YangMillsFieldEquationObstruction.ymActionIBPSourceProgress
      canonicalYangMillsFieldEquationObstruction)
  ≡
  canonicalYMSFGCNonFlatHodgeCurrentActionSupplyProgress
yangMillsYMActionIBPSourceNonFlatHodgeCurrentActionSupplyProgressIsExact =
  refl

yangMillsFinalPrimitiveLowerLawCandidateIsExact :
  YangMillsFieldEquationObstruction.finalPrimitiveLowerLawCandidate
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCFinalPrimitiveLowerLawCandidate
yangMillsFinalPrimitiveLowerLawCandidateIsExact =
  refl

yangMillsExactCanonicalMissingPrimitiveSummaryIsExact :
  YangMillsFieldEquationObstruction.exactCanonicalMissingPrimitiveSummary
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCExactCanonicalMissingPrimitiveSummary
yangMillsExactCanonicalMissingPrimitiveSummaryIsExact =
  refl

yangMillsFinalPrimitiveLowerLawCandidateBlockersAreExact :
  YMSFGCFinalPrimitiveLowerLawCandidate.finalPrimitiveMathBlockers
    canonicalYMSFGCFinalPrimitiveLowerLawCandidate
  ≡
  canonicalYMSFGCFinalPrimitiveMathBlockers
yangMillsFinalPrimitiveLowerLawCandidateBlockersAreExact =
  refl

yangMillsFieldEquationObstructionFirstMissing :
  YangMillsFieldEquationObstruction.firstMissingPrerequisite
    canonicalYangMillsFieldEquationObstruction
  ≡
  missingCovariantDerivativeOnSelectedGaugeBundle
yangMillsFieldEquationObstructionFirstMissing =
  refl

yangMillsFieldEquationPromoted :
  Bool
yangMillsFieldEquationPromoted =
  false

yangMillsFieldEquationPromotedIsFalse :
  yangMillsFieldEquationPromoted ≡ false
yangMillsFieldEquationPromotedIsFalse =
  refl

yangMillsFieldEquationObstructionStatusIsBlockedBeforeSFGCCurvatureCarrierNoPromotion :
  YangMillsFieldEquationObstruction.status
    canonicalYangMillsFieldEquationObstruction
  ≡
  blockedBeforeSFGCCurvatureCarrierNoPromotion
yangMillsFieldEquationObstructionStatusIsBlockedBeforeSFGCCurvatureCarrierNoPromotion =
  refl

yangMillsGate3NonFlatSFGCSite2DHandoffReceiptStatusIsNoPromotion :
  YMSFGCGate3NonFlatSFGCSite2DHandoffReceipt.status
    canonicalYMSFGCGate3NonFlatSFGCSite2DHandoffReceipt
  ≡
  gate3NonFlatSFGCSite2DPrimitivesStagedNoPromotion
yangMillsGate3NonFlatSFGCSite2DHandoffReceiptStatusIsNoPromotion =
  refl

yangMillsGate3M1NonFlatCurvatureBlockerChainLedgerStatusIsNoPromotion :
  YMSFGCGate3M1NonFlatCurvatureBlockerChainLedger.status
    canonicalYMSFGCGate3M1NonFlatCurvatureBlockerChainLedger
  ≡
  gate3M1FirstMissingCurvatureFieldsExposedNoPromotion
yangMillsGate3M1NonFlatCurvatureBlockerChainLedgerStatusIsNoPromotion =
  refl

yangMillsFieldEquationObstructionCurvatureCarrierImplemented :
  YangMillsFieldEquationObstruction.implementedDiscreteCurvatureCarrier
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCDiscreteCurvatureCarrier
yangMillsFieldEquationObstructionCurvatureCarrierImplemented =
  refl

yangMillsFieldEquationObstructionUpstreamFirstMissing :
  YangMillsFieldEquationObstruction.upstreamFirstMissing
    canonicalYangMillsFieldEquationObstruction
  ≡
  G2DCC.missingPrimeLattice2CellLayer
yangMillsFieldEquationObstructionUpstreamFirstMissing =
  refl

yangMillsFieldEquationObstructionUpstreamAPIFirstMissing :
  YangMillsFieldEquationObstruction.upstreamCurvatureAPIFirstMissing
    canonicalYangMillsFieldEquationObstruction
  ≡
  G2DCC.missingShiftGaugeFieldGaugeConnection
yangMillsFieldEquationObstructionUpstreamAPIFirstMissing =
  refl

yangMillsFieldEquationObstructionNondegeneratePlaquetteMissingAPIs :
  YangMillsFieldEquationObstruction.nondegeneratePlaquetteMissingAPIs
    canonicalYangMillsFieldEquationObstruction
  ≡
  G2DCC.SFGCNondegeneratePlaquetteCarrierRequest.missingAPIs
    G2DCC.canonicalSFGCNondegeneratePlaquetteCarrierRequest
yangMillsFieldEquationObstructionNondegeneratePlaquetteMissingAPIs =
  refl

yangMillsBianchiMissingPrimitivesAreExact :
  YangMillsFieldEquationObstruction.bianchiMissingPrimitives
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYangMillsBianchiMissingPrimitives
yangMillsBianchiMissingPrimitivesAreExact =
  refl

yangMillsSelectedCovariantDerivativeMissingPrimitivesAreExact :
  YangMillsFieldEquationObstruction.selectedCovariantDerivativeMissingPrimitives
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCSelectedCovariantDerivativeMissingPrimitives
yangMillsSelectedCovariantDerivativeMissingPrimitivesAreExact =
  refl

yangMillsSelectedExteriorDerivativeSquaredZeroWitnessIsExact :
  YangMillsFieldEquationObstruction.selectedExteriorDerivativeSquaredZeroWitness
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness
yangMillsSelectedExteriorDerivativeSquaredZeroWitnessIsExact =
  refl

yangMillsVariationalEquationMissingPrimitivesAreExact :
  YangMillsFieldEquationObstruction.variationalEquationMissingPrimitives
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYangMillsVariationalEquationMissingPrimitives
yangMillsVariationalEquationMissingPrimitivesAreExact =
  refl

yangMillsActionFunctionalMissingPrimitivesAreExact :
  YangMillsFieldEquationObstruction.actionFunctionalMissingPrimitives
    canonicalYangMillsFieldEquationObstruction
  ≡
  canonicalYMSFGCActionFunctionalMissingPrimitives
yangMillsActionFunctionalMissingPrimitivesAreExact =
  refl

record YMSFGCLower6M1M2U2ConsolidatedHandoffReceipt : Set₁ where
  field
    m1ReferenceNonFlatCurvatureAtReference :
      SFGC.sfgcSite2DEvaluate2
        sfgcReferenceNonFlatCurvature2Form
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    m1ReferenceFieldStrengthAtReference :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        sfgcReferenceNonFlatFieldStrengthBridge
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    m1EndpointGaugeFactor :
      SFGS.GaugeTransform →
      SFGC.SFGCSite2D →
      SPTI4.Phase4

    m1EndpointGaugeFactorIsSelectedPrimaryCoordinate :
      m1EndpointGaugeFactor
      ≡
      sfgcSelectedEndpointGaugeFactor

    m1SelectedEndpointPlaquetteConjugationLaw :
      (gauge : SFGS.GaugeTransform) →
      (A : SFGC.GaugeField) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        (sfgcSelectedFieldStrengthBridge
          (SFGC.transformGauge gauge A))
        plaquette
      ≡
      sfgcPhase4ConjugateBy
        (sfgcSelectedEndpointGaugeFactor
          gauge
          (SFGC.sfgcSite2DPlaquetteSW plaquette))
        (SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
          (sfgcSelectedFieldStrengthBridge A)
          plaquette)

    u2CoefficientAwareSU3RouteReceipt :
      YMSFGCSU3JacobiGlobalCarrierRouteReceipt

    u2CoefficientAwareSU3RouteReceiptIsCanonical :
      u2CoefficientAwareSU3RouteReceipt
      ≡
      canonicalYMSFGCSU3JacobiGlobalCarrierRouteReceipt

    finiteLieAlgebraCarrier :
      Set

    finiteLieAlgebraCarrierIsLocalFiniteLie3 :
      finiteLieAlgebraCarrier
      ≡
      YMSFGCLocalFiniteLie3Carrier

    finiteLieBracket :
      YMSFGCLocalFiniteLie3Carrier →
      YMSFGCLocalFiniteLie3Carrier →
      YMSFGCLocalFiniteLie3Carrier

    finiteLieBracketIsLocalFiniteLie3 :
      finiteLieBracket
      ≡
      localFiniteLie3Bracket

    finiteLieBracketNonAbelianWitness :
      finiteLieBracket
        (lieBasis signPos axisX)
        (lieBasis signPos axisY)
      ≡
      lieBasis signPos axisZ

    nontrivialAdjointAction :
      SPTI4.Phase4 →
      YMSFGCLocalFiniteLie3Carrier →
      YMSFGCLocalFiniteLie3Carrier

    nontrivialAdjointActionIsLocalPhaseAdjoint :
      nontrivialAdjointAction
      ≡
      localFiniteLie3PhaseAdjointAction

    nontrivialAdjointActionWitness :
      nontrivialAdjointAction
        SPTI4.φ1
        (lieBasis signPos axisX)
      ≡
      lieBasis signNeg axisX

    tracePairing :
      YMSFGCLocalFiniteLie3Carrier →
      YMSFGCLocalFiniteLie3Carrier →
      ℤ

    tracePairingIsLocalProbe :
      tracePairing
      ≡
      localFiniteLie3TracePairing

    tracePairingXXIsOne :
      tracePairing
        (lieBasis signPos axisX)
        (lieBasis signPos axisX)
      ≡
      + 1

    tracePairingXYIsZero :
      tracePairing
        (lieBasis signPos axisX)
        (lieBasis signPos axisY)
      ≡
      + 0

    tracePairingAdInvariance :
      (phase : SPTI4.Phase4) →
      (x y : YMSFGCLocalFiniteLie3Carrier) →
      tracePairing
        (nontrivialAdjointAction phase x)
        (nontrivialAdjointAction phase y)
      ≡
      tracePairing x y

    endpointGaugeTracePairingAdInvariance :
      (gauge : SFGS.GaugeTransform) →
      (site : SFGC.SFGCSite2D) →
      (x y : YMSFGCLocalFiniteLie3Carrier) →
      tracePairing
        (sfgcEndpointPhaseAdjointAction gauge site x)
        (sfgcEndpointPhaseAdjointAction gauge site y)
      ≡
      tracePairing x y

    m2HodgeStarLowerCandidate :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    m2HodgeStarLowerCandidateIsIdentityProbe :
      m2HodgeStarLowerCandidate
      ≡
      sfgcSelectedHodgeStarLowerCandidate

    m2ZeroVariationIBPLowerCandidate :
      YMSFGCDiscreteVariationIBPLowerCandidate

    m2ZeroVariationIBPLowerCandidateIsCanonical :
      m2ZeroVariationIBPLowerCandidate
      ≡
      canonicalYMSFGCDiscreteVariationIBPLowerCandidate

    firstStrictSU3GlobalCarrierBlocker :
      YMSFGCLocalFiniteSU3MissingPrimitive

    firstStrictSU3GlobalCarrierBlockerIsSFGCFibreRepresentation :
      firstStrictSU3GlobalCarrierBlocker
      ≡
      missingSFGCFibreRepresentationIntoSU3Carrier

    firstStrictNonFlatHolonomyBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictNonFlatHolonomyBlockerIsCurvature :
      firstStrictNonFlatHolonomyBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    firstStrictTransportBlocker :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    firstStrictTransportBlockerIsFieldStrengthAction :
      firstStrictTransportBlocker
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    firstStrictRouteBBlocker :
      YangMillsVariationalEquationMissingPrimitive

    firstStrictRouteBBlockerIsVariationPairing :
      firstStrictRouteBBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    nonFlatYangMillsPromoted :
      Bool

    nonFlatYangMillsPromotedIsFalse :
      nonFlatYangMillsPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    handoffBoundary :
      List String

canonicalYMSFGCLower6M1M2U2ConsolidatedHandoffReceipt :
  YMSFGCLower6M1M2U2ConsolidatedHandoffReceipt
canonicalYMSFGCLower6M1M2U2ConsolidatedHandoffReceipt =
  record
    { m1ReferenceNonFlatCurvatureAtReference =
        sfgcReferenceNonFlatCurvatureAtReference
    ; m1ReferenceFieldStrengthAtReference =
        sfgcReferenceNonFlatFieldStrengthAtReference
    ; m1EndpointGaugeFactor =
        sfgcSelectedEndpointGaugeFactor
    ; m1EndpointGaugeFactorIsSelectedPrimaryCoordinate =
        refl
    ; m1SelectedEndpointPlaquetteConjugationLaw =
        sfgcSelectedEndpointPlaquetteConjugationLaw
    ; u2CoefficientAwareSU3RouteReceipt =
        canonicalYMSFGCSU3JacobiGlobalCarrierRouteReceipt
    ; u2CoefficientAwareSU3RouteReceiptIsCanonical =
        refl
    ; finiteLieAlgebraCarrier =
        YMSFGCLocalFiniteLie3Carrier
    ; finiteLieAlgebraCarrierIsLocalFiniteLie3 =
        refl
    ; finiteLieBracket =
        localFiniteLie3Bracket
    ; finiteLieBracketIsLocalFiniteLie3 =
        refl
    ; finiteLieBracketNonAbelianWitness =
        localFiniteLie3BracketIsNonAbelian
    ; nontrivialAdjointAction =
        localFiniteLie3PhaseAdjointAction
    ; nontrivialAdjointActionIsLocalPhaseAdjoint =
        refl
    ; nontrivialAdjointActionWitness =
        localFiniteLie3PhaseAdjointActionNontrivial
    ; tracePairing =
        localFiniteLie3TracePairing
    ; tracePairingIsLocalProbe =
        refl
    ; tracePairingXXIsOne =
        refl
    ; tracePairingXYIsZero =
        refl
    ; tracePairingAdInvariance =
        localFiniteLie3PhaseAdjointTraceAdInvariance
    ; endpointGaugeTracePairingAdInvariance =
        sfgcEndpointPhaseAdjointTraceAdInvariance
    ; m2HodgeStarLowerCandidate =
        sfgcSelectedHodgeStarLowerCandidate
    ; m2HodgeStarLowerCandidateIsIdentityProbe =
        refl
    ; m2ZeroVariationIBPLowerCandidate =
        canonicalYMSFGCDiscreteVariationIBPLowerCandidate
    ; m2ZeroVariationIBPLowerCandidateIsCanonical =
        refl
    ; firstStrictSU3GlobalCarrierBlocker =
        missingSFGCFibreRepresentationIntoSU3Carrier
    ; firstStrictSU3GlobalCarrierBlockerIsSFGCFibreRepresentation =
        refl
    ; firstStrictNonFlatHolonomyBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; firstStrictNonFlatHolonomyBlockerIsCurvature =
        refl
    ; firstStrictTransportBlocker =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; firstStrictTransportBlockerIsFieldStrengthAction =
        refl
    ; firstStrictRouteBBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; firstStrictRouteBBlockerIsVariationPairing =
        refl
    ; nonFlatYangMillsPromoted =
        false
    ; nonFlatYangMillsPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; handoffBoundary =
        "lower6 consolidation: m1 reference curvature and field-strength evaluate to φ1 on the reference SFGCSite2D plaquette"
        ∷ "lower6 consolidation: endpoint gauge factors, selected flat endpoint conjugation, local finite Lie bracket, nontrivial phase adjoint, and trace-pairing Ad-invariance are all inhabited"
        ∷ "lower6 consolidation: u2 coefficient-aware SU(3) route receipt is consumed, with the strict global-carrier blocker still at missingSFGCFibreRepresentationIntoSU3Carrier"
        ∷ "lower6 consolidation: m2 has only the identity Hodge probe and zero-variation IBP lower candidate"
        ∷ "Strict non-flat Yang-Mills remains blocked at missingNonFlatSFGCSite2DConnectionCurvature, missingFieldStrengthTransportActionOnSelectedGaugeBundle, and missingVariationPairingForSelectedHodgeStar"
        ∷ "This receipt is a non-promoting ledger; no D * F = J, D F = 0, mass gap, Clay, or terminal claim is asserted"
        ∷ []
    }

yangMillsLower6M1M2U2ConsolidatedHandoffReceiptIsNonPromoting :
  YMSFGCLower6M1M2U2ConsolidatedHandoffReceipt.nonFlatYangMillsPromoted
    canonicalYMSFGCLower6M1M2U2ConsolidatedHandoffReceipt
  ≡
  false
yangMillsLower6M1M2U2ConsolidatedHandoffReceiptIsNonPromoting =
  refl

yangMillsLower6M1M2U2FirstStrictSU3BlockerIsExact :
  YMSFGCLower6M1M2U2ConsolidatedHandoffReceipt.firstStrictSU3GlobalCarrierBlocker
    canonicalYMSFGCLower6M1M2U2ConsolidatedHandoffReceipt
  ≡
  missingSFGCFibreRepresentationIntoSU3Carrier
yangMillsLower6M1M2U2FirstStrictSU3BlockerIsExact =
  refl

yangMillsLower6M1M2U2FirstStrictNonFlatBlockerIsExact :
  YMSFGCLower6M1M2U2ConsolidatedHandoffReceipt.firstStrictNonFlatHolonomyBlocker
    canonicalYMSFGCLower6M1M2U2ConsolidatedHandoffReceipt
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsLower6M1M2U2FirstStrictNonFlatBlockerIsExact =
  refl

yangMillsLower6M1M2U2FirstStrictRouteBBlockerIsExact :
  YMSFGCLower6M1M2U2ConsolidatedHandoffReceipt.firstStrictRouteBBlocker
    canonicalYMSFGCLower6M1M2U2ConsolidatedHandoffReceipt
  ≡
  missingVariationPairingForSelectedHodgeStar
yangMillsLower6M1M2U2FirstStrictRouteBBlockerIsExact =
  refl

data YMSFGCGate3Wave2FiniteHolonomyMathStatus : Set where
  gate3Wave2FiniteCurvatureHolonomyTraceClosedNoPromotion :
    YMSFGCGate3Wave2FiniteHolonomyMathStatus

record YMSFGCGate3Wave2FiniteHolonomyMathReceipt : Set₁ where
  field
    status :
      YMSFGCGate3Wave2FiniteHolonomyMathStatus

    finiteNonFlatCurvatureAdvancement :
      YMSFGCGate3NonFlatCurvaturePrimitiveAdvancement

    finiteNonFlatCurvatureAdvancementIsCanonical :
      finiteNonFlatCurvatureAdvancement
      ≡
      canonicalYMSFGCGate3NonFlatCurvaturePrimitiveAdvancement

    finiteConnectionCarrier :
      Set

    finiteConnectionCarrierIsSFGCSite2DDiscrete1Form :
      finiteConnectionCarrier
      ≡
      SFGC.SFGCSite2DDiscrete1Form

    finiteConnectionCurvature :
      SFGC.SFGCSite2DDiscrete1Form →
      SFGC.SFGCSite2DDiscrete2Form

    finiteConnectionCurvatureIsDelta1 :
      finiteConnectionCurvature
      ≡
      SFGC.sfgcSite2Dδ₁

    finiteReferenceConnection :
      SFGC.SFGCSite2DDiscrete1Form

    finiteReferenceConnectionIsCanonical :
      finiteReferenceConnection
      ≡
      sfgcReferenceNonFlat1Form

    finiteReferenceCurvatureIsQuarterTurn :
      SFGC.sfgcSite2DEvaluate2
        (finiteConnectionCurvature finiteReferenceConnection)
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    finiteReferenceFieldStrength :
      SFGC.SFGCSite2DFieldStrengthBridge

    finiteReferenceFieldStrengthIsCurvatureBridge :
      finiteReferenceFieldStrength
      ≡
      SFGC.sfgcSite2DFieldStrengthFromCurvature
        (finiteConnectionCurvature finiteReferenceConnection)

    finiteReferenceFieldStrengthWilsonLoopIsQuarterTurn :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        finiteReferenceFieldStrength
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    finiteEndpointGaugeFactors :
      YMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt

    finiteEndpointGaugeFactorsAreCanonical :
      finiteEndpointGaugeFactors
      ≡
      canonicalYMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt

    finiteHolonomyTelescopingLaw :
      (connection : SFGC.SFGCSite2DDiscrete1Form) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      SFGS.phaseAdd4
        (SFGS.phaseAdd4
          (SFGS.phaseAdd4
            (SFGC.sfgcSite2DEvaluate1
              connection
              (SFGC.sfgcSite2DPlaquetteBottomEdge plaquette))
            (SFGC.sfgcSite2DEvaluate1
              connection
              (SFGC.sfgcSite2DPlaquetteRightEdge plaquette)))
          (SFGS.phaseInv4
            (SFGC.sfgcSite2DEvaluate1
              connection
              (SFGC.sfgcSite2DPlaquetteTopEdge plaquette))))
        (SFGS.phaseInv4
          (SFGC.sfgcSite2DEvaluate1
            connection
            (SFGC.sfgcSite2DPlaquetteLeftEdge plaquette)))
      ≡
      sfgcFiniteC4PlaquetteHolonomy connection plaquette

    finiteHolonomyTelescopingLawIsCanonical :
      finiteHolonomyTelescopingLaw
      ≡
      sfgcFiniteC4HolonomyTelescopingLaw

    finiteHolonomyConjugationLaw :
      (gauge : SFGS.GaugeTransform) →
      (connection : SFGC.SFGCSite2DDiscrete1Form) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      sfgcFiniteC4PlaquetteHolonomy
        (sfgcFiniteC4ConnectionGaugeTransformCandidate gauge connection)
        plaquette
      ≡
      sfgcFiniteC4ConjugateBy
        (sfgcFiniteC4EndpointGaugeFactor
          gauge
          (SFGC.sfgcSite2DPlaquetteSW plaquette))
        (sfgcFiniteC4PlaquetteHolonomy connection plaquette)

    finiteHolonomyConjugationLawIsCanonical :
      finiteHolonomyConjugationLaw
      ≡
      sfgcFiniteC4HolonomyConjugationLaw

    selectedFiniteLieAlgebraSupply :
      YMSFGCNonAbelianCovariantDerivativePrimitiveSupply

    selectedFiniteLieAlgebraSupplyIsLocalFiniteLie3 :
      selectedFiniteLieAlgebraSupply
      ≡
      canonicalYMSFGCLocalFiniteLie3PrimitiveSupply

    selectedFiniteTraceAdInvarianceSupply :
      YMSFGCLieAlgebraTraceAdInvariancePrimitiveSupply

    selectedFiniteTraceAdInvarianceSupplyIsFiniteC4 :
      selectedFiniteTraceAdInvarianceSupply
      ≡
      canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply

    finiteLieBracketNonAbelian :
      localFiniteLie3Bracket
        (lieBasis signPos axisX)
        (lieBasis signPos axisY)
      ≡
      lieBasis signPos axisZ

    finiteLieBracketAntisymmetry :
      (x y : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3Bracket x y
      ≡
      localFiniteLie3Neg (localFiniteLie3Bracket y x)

    finiteLieJacobi :
      (x y z : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3JacobiAdd
        (localFiniteLie3JacobiAdd
          (localFiniteLie3Bracket x (localFiniteLie3Bracket y z))
          (localFiniteLie3Bracket y (localFiniteLie3Bracket z x)))
        (localFiniteLie3Bracket z (localFiniteLie3Bracket x y))
      ≡
      lieZero

    finiteAdjointActionNontrivial :
      localFiniteLie3PhaseAdjointAction
        SPTI4.φ1
        (lieBasis signPos axisX)
      ≡
      lieBasis signNeg axisX

    finiteTracePairingNonconstantSamePhase :
      SPTI4.phaseKernel4 SPTI4.φ0 SPTI4.φ0
      ≡
      + 1

    finiteTracePairingNonconstantOrthogonal :
      SPTI4.phaseKernel4 SPTI4.φ0 SPTI4.φ1
      ≡
      + 0

    finiteTracePairingAdInvariant :
      (gauge : SFGS.GaugeTransform) →
      (x y : SPTI4.Phase4) →
      SPTI4.phaseKernel4
        (sfgcFiniteC4AdjointAction gauge x)
        (sfgcFiniteC4AdjointAction gauge y)
      ≡
      SPTI4.phaseKernel4 x y

    finiteLocalCurvatureHolonomyTraceClosed :
      Bool

    finiteLocalCurvatureHolonomyTraceClosedIsTrue :
      finiteLocalCurvatureHolonomyTraceClosed ≡ true

    strictRealNonFlatYMPromotionBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    strictRealNonFlatYMPromotionBlockerIsCurvature :
      strictRealNonFlatYMPromotionBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    strictRealSelectedGaugeSectorBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    strictRealSelectedGaugeSectorBlockerIsLieAlgebraCarrier :
      strictRealSelectedGaugeSectorBlocker
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    strictRouteBBlocker :
      YangMillsVariationalEquationMissingPrimitive

    strictRouteBBlockerIsVariationPairing :
      strictRouteBBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    finiteReceiptPromotedToRealYM :
      Bool

    finiteReceiptPromotedToRealYMIsFalse :
      finiteReceiptPromotedToRealYM ≡ false

    receiptBoundary :
      List String

canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt :
  YMSFGCGate3Wave2FiniteHolonomyMathReceipt
canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt =
  record
    { status =
        gate3Wave2FiniteCurvatureHolonomyTraceClosedNoPromotion
    ; finiteNonFlatCurvatureAdvancement =
        canonicalYMSFGCGate3NonFlatCurvaturePrimitiveAdvancement
    ; finiteNonFlatCurvatureAdvancementIsCanonical =
        refl
    ; finiteConnectionCarrier =
        SFGC.SFGCSite2DDiscrete1Form
    ; finiteConnectionCarrierIsSFGCSite2DDiscrete1Form =
        refl
    ; finiteConnectionCurvature =
        SFGC.sfgcSite2Dδ₁
    ; finiteConnectionCurvatureIsDelta1 =
        refl
    ; finiteReferenceConnection =
        sfgcReferenceNonFlat1Form
    ; finiteReferenceConnectionIsCanonical =
        refl
    ; finiteReferenceCurvatureIsQuarterTurn =
        sfgcReferenceNonFlatCurvatureAtReference
    ; finiteReferenceFieldStrength =
        sfgcReferenceNonFlatFieldStrengthBridge
    ; finiteReferenceFieldStrengthIsCurvatureBridge =
        refl
    ; finiteReferenceFieldStrengthWilsonLoopIsQuarterTurn =
        sfgcReferenceNonFlatFieldStrengthAtReference
    ; finiteEndpointGaugeFactors =
        canonicalYMSFGCSelectedEndpointGaugeFactorSourceTargetReceipt
    ; finiteEndpointGaugeFactorsAreCanonical =
        refl
    ; finiteHolonomyTelescopingLaw =
        sfgcFiniteC4HolonomyTelescopingLaw
    ; finiteHolonomyTelescopingLawIsCanonical =
        refl
    ; finiteHolonomyConjugationLaw =
        sfgcFiniteC4HolonomyConjugationLaw
    ; finiteHolonomyConjugationLawIsCanonical =
        refl
    ; selectedFiniteLieAlgebraSupply =
        canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
    ; selectedFiniteLieAlgebraSupplyIsLocalFiniteLie3 =
        refl
    ; selectedFiniteTraceAdInvarianceSupply =
        canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply
    ; selectedFiniteTraceAdInvarianceSupplyIsFiniteC4 =
        refl
    ; finiteLieBracketNonAbelian =
        localFiniteLie3BracketIsNonAbelian
    ; finiteLieBracketAntisymmetry =
        localFiniteLie3BracketAntisymmetry
    ; finiteLieJacobi =
        localFiniteLie3JacobiWitness
    ; finiteAdjointActionNontrivial =
        localFiniteLie3PhaseAdjointActionNontrivial
    ; finiteTracePairingNonconstantSamePhase =
        SPTI4.samePhaseConstructiveKernel SPTI4.φ0
    ; finiteTracePairingNonconstantOrthogonal =
        SPTI4.orthogonalPhaseNeutralKernel
    ; finiteTracePairingAdInvariant =
        sfgcFiniteC4TraceAdInvarianceLaw
    ; finiteLocalCurvatureHolonomyTraceClosed =
        true
    ; finiteLocalCurvatureHolonomyTraceClosedIsTrue =
        refl
    ; strictRealNonFlatYMPromotionBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; strictRealNonFlatYMPromotionBlockerIsCurvature =
        refl
    ; strictRealSelectedGaugeSectorBlocker =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; strictRealSelectedGaugeSectorBlockerIsLieAlgebraCarrier =
        refl
    ; strictRouteBBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; strictRouteBBlockerIsVariationPairing =
        refl
    ; finiteReceiptPromotedToRealYM =
        false
    ; finiteReceiptPromotedToRealYMIsFalse =
        refl
    ; receiptBoundary =
        "Wave 2 finite YM progress: the SFGCSite2DDiscrete1Form carrier has an explicit non-flat reference 1-form whose δ1 curvature is φ1 at the reference plaquette"
        ∷ "Wave 2 finite YM progress: plaquette holonomy is the SFGC Wilson-loop phase, and its boundary telescoping law is closed definitionally"
        ∷ "Wave 2 finite YM progress: finite C4 endpoint conjugation is closed for the identity connection-action candidate, so this remains abelian finite holonomy math"
        ∷ "Wave 2 finite YM progress: local finite Lie3 supplies zero, negation, bracket, antisymmetry, and Jacobi; Phase4 supplies a nonconstant trace proxy and table-checked Ad invariance"
        ∷ "Not promoted: the strict real/non-abelian Yang-Mills curvature symbol still requires a supplied non-flat connection action, real fibre representation, and nontrivial holonomy transport"
        ∷ "Not promoted: Route B still lacks a selected Hodge/action variation pairing and matter current coupling"
        ∷ []
    }

yangMillsGate3Wave2FiniteHolonomyMathReceiptIsNonPromoting :
  YMSFGCGate3Wave2FiniteHolonomyMathReceipt.finiteReceiptPromotedToRealYM
    canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt
  ≡
  false
yangMillsGate3Wave2FiniteHolonomyMathReceiptIsNonPromoting =
  refl

yangMillsGate3Wave2FiniteReferenceCurvatureIsQuarterTurn :
  YMSFGCGate3Wave2FiniteHolonomyMathReceipt.finiteReferenceCurvatureIsQuarterTurn
    canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt
  ≡
  sfgcReferenceNonFlatCurvatureAtReference
yangMillsGate3Wave2FiniteReferenceCurvatureIsQuarterTurn =
  refl

yangMillsGate3Wave2StrictRealBlockerIsStillCurvature :
  YMSFGCGate3Wave2FiniteHolonomyMathReceipt.strictRealNonFlatYMPromotionBlocker
    canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsGate3Wave2StrictRealBlockerIsStillCurvature =
  refl

yangMillsGate3Wave2StrictRouteBBlockerIsStillVariationPairing :
  YMSFGCGate3Wave2FiniteHolonomyMathReceipt.strictRouteBBlocker
    canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt
  ≡
  missingVariationPairingForSelectedHodgeStar
yangMillsGate3Wave2StrictRouteBBlockerIsStillVariationPairing =
  refl

data YMSFGCGate3Wave3StrictPromotionDecisionStatus : Set where
  gate3Wave3FiniteLocalEvidenceCannotPromoteToStrictRealYM :
    YMSFGCGate3Wave3StrictPromotionDecisionStatus

record YMSFGCGate3Wave3StrictPromotionDecisionReceipt : Set₁ where
  field
    status :
      YMSFGCGate3Wave3StrictPromotionDecisionStatus

    wave2FiniteHolonomyMathReceipt :
      YMSFGCGate3Wave2FiniteHolonomyMathReceipt

    wave2FiniteHolonomyMathReceiptIsCanonical :
      wave2FiniteHolonomyMathReceipt
      ≡
      canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt

    finiteConnectionCarrier :
      Set

    finiteConnectionCarrierIsSFGCSite2DDiscrete1Form :
      finiteConnectionCarrier
      ≡
      SFGC.SFGCSite2DDiscrete1Form

    strictRequestedConnectionCarrier :
      Set

    strictRequestedConnectionCarrierIsUserSupplied :
      strictRequestedConnectionCarrier
      ≡
      YMSFGCUserSuppliedNonFlatConnectionCarrier

    finiteHolonomyCarrier :
      Set

    finiteHolonomyCarrierIsPhase4 :
      finiteHolonomyCarrier
      ≡
      SPTI4.Phase4

    strictRequestedHolonomyCarrier :
      Set

    strictRequestedHolonomyCarrierIsUserSupplied :
      strictRequestedHolonomyCarrier
      ≡
      YMSFGCUserSuppliedHolonomyCarrier

    finiteLieCarrier :
      Set

    finiteLieCarrierIsLocalFiniteLie3 :
      finiteLieCarrier
      ≡
      YMSFGCLocalFiniteLie3Carrier

    strictRequestedLieCarrier :
      Set

    strictRequestedLieCarrierIsUserSupplied :
      strictRequestedLieCarrier
      ≡
      YMSFGCUserSuppliedLieAlgebraCarrier

    finiteReferenceCurvatureWitness :
      SFGC.sfgcSite2DEvaluate2
        (SFGC.sfgcSite2Dδ₁ sfgcReferenceNonFlat1Form)
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    finiteReferenceFieldStrengthWitness :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        sfgcReferenceNonFlatFieldStrengthBridge
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    finiteHolonomyConjugationLaw :
      (gauge : SFGS.GaugeTransform) →
      (connection : SFGC.SFGCSite2DDiscrete1Form) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      sfgcFiniteC4PlaquetteHolonomy
        (sfgcFiniteC4ConnectionGaugeTransformCandidate gauge connection)
        plaquette
      ≡
      sfgcFiniteC4ConjugateBy
        (sfgcFiniteC4EndpointGaugeFactor
          gauge
          (SFGC.sfgcSite2DPlaquetteSW plaquette))
        (sfgcFiniteC4PlaquetteHolonomy connection plaquette)

    finiteHolonomyConjugationLawIsCanonical :
      finiteHolonomyConjugationLaw
      ≡
      sfgcFiniteC4HolonomyConjugationLaw

    finiteLieAlgebraSupply :
      YMSFGCNonAbelianCovariantDerivativePrimitiveSupply

    finiteLieAlgebraSupplyIsLocalFiniteLie3 :
      finiteLieAlgebraSupply
      ≡
      canonicalYMSFGCLocalFiniteLie3PrimitiveSupply

    finiteTraceAdInvarianceSupply :
      YMSFGCLieAlgebraTraceAdInvariancePrimitiveSupply

    finiteTraceAdInvarianceSupplyIsFiniteC4 :
      finiteTraceAdInvarianceSupply
      ≡
      canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply

    finiteHodgeLowerCandidate :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    finiteHodgeLowerCandidateIsIdentityProbe :
      finiteHodgeLowerCandidate
      ≡
      sfgcSelectedHodgeStarLowerCandidate

    requiredExactConnectionSectionLawType :
      Set

    requiredExactConnectionSectionLawTypeIsSFGCSection :
      requiredExactConnectionSectionLawType
      ≡
      ((section : SFGC.SFGCSite2DDiscrete1Form → SFGC.GaugeField) →
       (connection : SFGC.SFGCSite2DDiscrete1Form) →
       SFGC.sfgcSite2DConnectionTo1Form (section connection)
       ≡
       connection)

    requiredStrictConnectionCarrierBridgeType :
      Set

    requiredStrictConnectionCarrierBridgeTypeIsFiniteToUserSupplied :
      requiredStrictConnectionCarrierBridgeType
      ≡
      (SFGC.SFGCSite2DDiscrete1Form →
       YMSFGCUserSuppliedNonFlatConnectionCarrier)

    requiredStrictHolonomyCarrierBridgeType :
      Set

    requiredStrictHolonomyCarrierBridgeTypeIsPhase4ToUserSupplied :
      requiredStrictHolonomyCarrierBridgeType
      ≡
      (SPTI4.Phase4 → YMSFGCUserSuppliedHolonomyCarrier)

    requiredStrictLieCarrierBridgeType :
      Set

    requiredStrictLieCarrierBridgeTypeIsLie3ToUserSupplied :
      requiredStrictLieCarrierBridgeType
      ≡
      (YMSFGCLocalFiniteLie3Carrier →
       YMSFGCUserSuppliedLieAlgebraCarrier)

    requiredStrictDualCurvatureBridgeType :
      Set

    requiredStrictDualCurvatureBridgeTypeIsFieldStrengthToUserSupplied :
      requiredStrictDualCurvatureBridgeType
      ≡
      (SFGC.SFGCSite2DFieldStrengthBridge →
       YMSFGCUserSuppliedDualCurvatureCarrier)

    firstStrictNonFlatHolonomyBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictNonFlatHolonomyBlockerIsCurvature :
      firstStrictNonFlatHolonomyBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    firstStrictGaugeSectorBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    firstStrictGaugeSectorBlockerIsLieCarrier :
      firstStrictGaugeSectorBlocker
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    firstStrictRouteBBlocker :
      YangMillsVariationalEquationMissingPrimitive

    firstStrictRouteBBlockerIsVariationPairing :
      firstStrictRouteBBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    finiteLocalEvidencePromotedToStrictRealYM :
      Bool

    finiteLocalEvidencePromotedToStrictRealYMIsFalse :
      finiteLocalEvidencePromotedToStrictRealYM ≡ false

    finalLocalBoundary :
      List String

canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt :
  YMSFGCGate3Wave3StrictPromotionDecisionReceipt
canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt =
  record
    { status =
        gate3Wave3FiniteLocalEvidenceCannotPromoteToStrictRealYM
    ; wave2FiniteHolonomyMathReceipt =
        canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt
    ; wave2FiniteHolonomyMathReceiptIsCanonical =
        refl
    ; finiteConnectionCarrier =
        SFGC.SFGCSite2DDiscrete1Form
    ; finiteConnectionCarrierIsSFGCSite2DDiscrete1Form =
        refl
    ; strictRequestedConnectionCarrier =
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; strictRequestedConnectionCarrierIsUserSupplied =
        refl
    ; finiteHolonomyCarrier =
        SPTI4.Phase4
    ; finiteHolonomyCarrierIsPhase4 =
        refl
    ; strictRequestedHolonomyCarrier =
        YMSFGCUserSuppliedHolonomyCarrier
    ; strictRequestedHolonomyCarrierIsUserSupplied =
        refl
    ; finiteLieCarrier =
        YMSFGCLocalFiniteLie3Carrier
    ; finiteLieCarrierIsLocalFiniteLie3 =
        refl
    ; strictRequestedLieCarrier =
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; strictRequestedLieCarrierIsUserSupplied =
        refl
    ; finiteReferenceCurvatureWitness =
        sfgcReferenceNonFlatCurvatureAtReference
    ; finiteReferenceFieldStrengthWitness =
        sfgcReferenceNonFlatFieldStrengthAtReference
    ; finiteHolonomyConjugationLaw =
        sfgcFiniteC4HolonomyConjugationLaw
    ; finiteHolonomyConjugationLawIsCanonical =
        refl
    ; finiteLieAlgebraSupply =
        canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
    ; finiteLieAlgebraSupplyIsLocalFiniteLie3 =
        refl
    ; finiteTraceAdInvarianceSupply =
        canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply
    ; finiteTraceAdInvarianceSupplyIsFiniteC4 =
        refl
    ; finiteHodgeLowerCandidate =
        sfgcSelectedHodgeStarLowerCandidate
    ; finiteHodgeLowerCandidateIsIdentityProbe =
        refl
    ; requiredExactConnectionSectionLawType =
        (section : SFGC.SFGCSite2DDiscrete1Form → SFGC.GaugeField) →
        (connection : SFGC.SFGCSite2DDiscrete1Form) →
        SFGC.sfgcSite2DConnectionTo1Form (section connection)
        ≡
        connection
    ; requiredExactConnectionSectionLawTypeIsSFGCSection =
        refl
    ; requiredStrictConnectionCarrierBridgeType =
        SFGC.SFGCSite2DDiscrete1Form →
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; requiredStrictConnectionCarrierBridgeTypeIsFiniteToUserSupplied =
        refl
    ; requiredStrictHolonomyCarrierBridgeType =
        SPTI4.Phase4 → YMSFGCUserSuppliedHolonomyCarrier
    ; requiredStrictHolonomyCarrierBridgeTypeIsPhase4ToUserSupplied =
        refl
    ; requiredStrictLieCarrierBridgeType =
        YMSFGCLocalFiniteLie3Carrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requiredStrictLieCarrierBridgeTypeIsLie3ToUserSupplied =
        refl
    ; requiredStrictDualCurvatureBridgeType =
        SFGC.SFGCSite2DFieldStrengthBridge →
        YMSFGCUserSuppliedDualCurvatureCarrier
    ; requiredStrictDualCurvatureBridgeTypeIsFieldStrengthToUserSupplied =
        refl
    ; firstStrictNonFlatHolonomyBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; firstStrictNonFlatHolonomyBlockerIsCurvature =
        refl
    ; firstStrictGaugeSectorBlocker =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; firstStrictGaugeSectorBlockerIsLieCarrier =
        refl
    ; firstStrictRouteBBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; firstStrictRouteBBlockerIsVariationPairing =
        refl
    ; finiteLocalEvidencePromotedToStrictRealYM =
        false
    ; finiteLocalEvidencePromotedToStrictRealYMIsFalse =
        refl
    ; finalLocalBoundary =
        "Wave 3 final-local decision: finite curvature, finite C4 holonomy conjugation, local Lie3 bracket/Jacobi, finite trace Ad-invariance, and identity Hodge probe are all consumed"
        ∷ "No strict promotion: the finite carrier now adapts into the user-supplied non-flat connection carrier, but the strict holonomy/law surface remains unclosed"
        ∷ "No exact SFGC section is supplied from arbitrary SFGCSite2DDiscrete1Form back to GaugeField with sfgcSite2DConnectionTo1Form section connection = connection"
        ∷ "Strict bridges are now supplied for SFGCSite2DDiscrete1Form -> user non-flat connection and SFGCSite2DFieldStrengthBridge -> user dual curvature"
        ∷ "Phase4 holonomy, local Lie3/Lie, and strict variation-law bridges remain absent, so the exact blockers stay missingNonFlatSFGCSite2DConnectionCurvature, missingLieAlgebraCarrierForSelectedFiniteGaugeSector, and missingVariationPairingForSelectedHodgeStar"
        ∷ []
    }

yangMillsGate3Wave3StrictPromotionDecisionIsNonPromoting :
  YMSFGCGate3Wave3StrictPromotionDecisionReceipt.finiteLocalEvidencePromotedToStrictRealYM
    canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt
  ≡
  false
yangMillsGate3Wave3StrictPromotionDecisionIsNonPromoting =
  refl

yangMillsGate3Wave3FirstStrictNonFlatBlockerIsCurvature :
  YMSFGCGate3Wave3StrictPromotionDecisionReceipt.firstStrictNonFlatHolonomyBlocker
    canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsGate3Wave3FirstStrictNonFlatBlockerIsCurvature =
  refl

yangMillsGate3Wave3FirstStrictGaugeSectorBlockerIsLieCarrier :
  YMSFGCGate3Wave3StrictPromotionDecisionReceipt.firstStrictGaugeSectorBlocker
    canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt
  ≡
  missingLieAlgebraCarrierForSelectedFiniteGaugeSector
yangMillsGate3Wave3FirstStrictGaugeSectorBlockerIsLieCarrier =
  refl

yangMillsGate3Wave3FirstStrictRouteBBlockerIsVariationPairing :
  YMSFGCGate3Wave3StrictPromotionDecisionReceipt.firstStrictRouteBBlocker
    canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt
  ≡
  missingVariationPairingForSelectedHodgeStar
yangMillsGate3Wave3FirstStrictRouteBBlockerIsVariationPairing =
  refl

data YMSFGCGate3M1U2M2WorkerFinalStatus : Set where
  gate3M1U2M2FiniteStagingConsumedStrictRealYMBlocked :
    YMSFGCGate3M1U2M2WorkerFinalStatus

record YMSFGCGate3M1U2M2WorkerFinalReceipt : Set₁ where
  field
    status :
      YMSFGCGate3M1U2M2WorkerFinalStatus

    consumedLower6Handoff :
      YMSFGCLower6M1M2U2ConsolidatedHandoffReceipt

    consumedLower6HandoffIsCanonical :
      consumedLower6Handoff
      ≡
      canonicalYMSFGCLower6M1M2U2ConsolidatedHandoffReceipt

    consumedWave2FiniteHolonomyMath :
      YMSFGCGate3Wave2FiniteHolonomyMathReceipt

    consumedWave2FiniteHolonomyMathIsCanonical :
      consumedWave2FiniteHolonomyMath
      ≡
      canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt

    consumedWave3StrictPromotionDecision :
      YMSFGCGate3Wave3StrictPromotionDecisionReceipt

    consumedWave3StrictPromotionDecisionIsCanonical :
      consumedWave3StrictPromotionDecision
      ≡
      canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt

    m1ReferenceConnection :
      SFGC.SFGCSite2DDiscrete1Form

    m1ReferenceConnectionIsCanonical :
      m1ReferenceConnection
      ≡
      sfgcReferenceNonFlat1Form

    m1ReferenceCurvature :
      SFGC.SFGCSite2DDiscrete2Form

    m1ReferenceCurvatureIsCanonical :
      m1ReferenceCurvature
      ≡
      sfgcReferenceNonFlatCurvature2Form

    m1ReferenceCurvatureAtReference :
      SFGC.sfgcSite2DEvaluate2
        m1ReferenceCurvature
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    m1ReferenceFieldStrengthAtReference :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        sfgcReferenceNonFlatFieldStrengthBridge
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    m1FiniteHolonomyTelescopingLaw :
      (connection : SFGC.SFGCSite2DDiscrete1Form) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      SFGS.phaseAdd4
        (SFGS.phaseAdd4
          (SFGS.phaseAdd4
            (SFGC.sfgcSite2DEvaluate1
              connection
              (SFGC.sfgcSite2DPlaquetteBottomEdge plaquette))
            (SFGC.sfgcSite2DEvaluate1
              connection
              (SFGC.sfgcSite2DPlaquetteRightEdge plaquette)))
          (SFGS.phaseInv4
            (SFGC.sfgcSite2DEvaluate1
              connection
              (SFGC.sfgcSite2DPlaquetteTopEdge plaquette))))
        (SFGS.phaseInv4
          (SFGC.sfgcSite2DEvaluate1
            connection
            (SFGC.sfgcSite2DPlaquetteLeftEdge plaquette)))
      ≡
      sfgcFiniteC4PlaquetteHolonomy connection plaquette

    m1FiniteHolonomyConjugationLaw :
      (gauge : SFGS.GaugeTransform) →
      (connection : SFGC.SFGCSite2DDiscrete1Form) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      sfgcFiniteC4PlaquetteHolonomy
        (sfgcFiniteC4ConnectionGaugeTransformCandidate gauge connection)
        plaquette
      ≡
      sfgcFiniteC4ConjugateBy
        (sfgcFiniteC4EndpointGaugeFactor
          gauge
          (SFGC.sfgcSite2DPlaquetteSW plaquette))
        (sfgcFiniteC4PlaquetteHolonomy connection plaquette)

    u2ConnectionOneFormAsFibreAlgebraLocalReceipt :
      YMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt

    u2ConnectionOneFormAsFibreAlgebraLocalReceiptIsCanonical :
      u2ConnectionOneFormAsFibreAlgebraLocalReceipt
      ≡
      canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt

    u2LocalFiniteLieValuedFormsAndCurvature :
      YMSFGCLocalFiniteLieValuedFormsAndCurvature

    u2LocalFiniteLieValuedFormsAndCurvatureIsCanonical :
      u2LocalFiniteLieValuedFormsAndCurvature
      ≡
      canonicalYMSFGCLocalFiniteLieValuedFormsAndCurvature

    u2LocalDASquaredEqualsBracketF :
      (A : SFGC.GaugeField) →
      (section : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3DA0Form
        A
        (localFiniteLie3DA0Form A (lieValued0 section))
      ≡
      localFiniteLie3CurvatureBracketActionOn0Form
        (localFiniteLie3FA2Form A)
        (lieValued0 section)

    m2HodgeStarLowerCandidate :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    m2HodgeStarLowerCandidateIsIdentityProbe :
      m2HodgeStarLowerCandidate
      ≡
      sfgcSelectedHodgeStarLowerCandidate

    m2ZeroVariationIBPLowerCandidate :
      YMSFGCDiscreteVariationIBPLowerCandidate

    m2ZeroVariationIBPLowerCandidateIsCanonical :
      m2ZeroVariationIBPLowerCandidate
      ≡
      canonicalYMSFGCDiscreteVariationIBPLowerCandidate

    m2FinalPrimitiveLowerLawCandidate :
      YMSFGCFinalPrimitiveLowerLawCandidate

    m2FinalPrimitiveLowerLawCandidateIsCanonical :
      m2FinalPrimitiveLowerLawCandidate
      ≡
      canonicalYMSFGCFinalPrimitiveLowerLawCandidate

    strictRequestedConnectionCarrier :
      Set

    strictRequestedConnectionCarrierIsUserSupplied :
      strictRequestedConnectionCarrier
      ≡
      YMSFGCUserSuppliedNonFlatConnectionCarrier

    strictConnectionBridgeRequest :
      Set

    strictConnectionBridgeRequestIsFiniteToUserSupplied :
      strictConnectionBridgeRequest
      ≡
      (SFGC.SFGCSite2DDiscrete1Form →
       YMSFGCUserSuppliedNonFlatConnectionCarrier)

    strictDualCurvatureBridgeRequest :
      Set

    strictDualCurvatureBridgeRequestIsFieldStrengthToUserSupplied :
      strictDualCurvatureBridgeRequest
      ≡
      (SFGC.SFGCSite2DFieldStrengthBridge →
       YMSFGCUserSuppliedDualCurvatureCarrier)

    firstStrictM1Blocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictM1BlockerIsNonFlatCurvature :
      firstStrictM1Blocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    firstStrictU2TransportBlocker :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    firstStrictU2TransportBlockerIsFieldStrengthAction :
      firstStrictU2TransportBlocker
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    firstStrictU2CarrierBlocker :
      YMSFGCLocalFiniteSU3MissingPrimitive

    firstStrictU2CarrierBlockerIsSFGCFibreRepresentation :
      firstStrictU2CarrierBlocker
      ≡
      missingSFGCFibreRepresentationIntoSU3Carrier

    firstStrictM2Blocker :
      YangMillsVariationalEquationMissingPrimitive

    firstStrictM2BlockerIsVariationPairing :
      firstStrictM2Blocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    strictRealYMPromoted :
      Bool

    strictRealYMPromotedIsFalse :
      strictRealYMPromoted ≡ false

    consumedStaging :
      List String

    failClosedBoundary :
      List String

canonicalYMSFGCGate3M1U2M2WorkerFinalReceipt :
  YMSFGCGate3M1U2M2WorkerFinalReceipt
canonicalYMSFGCGate3M1U2M2WorkerFinalReceipt =
  record
    { status =
        gate3M1U2M2FiniteStagingConsumedStrictRealYMBlocked
    ; consumedLower6Handoff =
        canonicalYMSFGCLower6M1M2U2ConsolidatedHandoffReceipt
    ; consumedLower6HandoffIsCanonical =
        refl
    ; consumedWave2FiniteHolonomyMath =
        canonicalYMSFGCGate3Wave2FiniteHolonomyMathReceipt
    ; consumedWave2FiniteHolonomyMathIsCanonical =
        refl
    ; consumedWave3StrictPromotionDecision =
        canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt
    ; consumedWave3StrictPromotionDecisionIsCanonical =
        refl
    ; m1ReferenceConnection =
        sfgcReferenceNonFlat1Form
    ; m1ReferenceConnectionIsCanonical =
        refl
    ; m1ReferenceCurvature =
        sfgcReferenceNonFlatCurvature2Form
    ; m1ReferenceCurvatureIsCanonical =
        refl
    ; m1ReferenceCurvatureAtReference =
        sfgcReferenceNonFlatCurvatureAtReference
    ; m1ReferenceFieldStrengthAtReference =
        sfgcReferenceNonFlatFieldStrengthAtReference
    ; m1FiniteHolonomyTelescopingLaw =
        sfgcFiniteC4HolonomyTelescopingLaw
    ; m1FiniteHolonomyConjugationLaw =
        sfgcFiniteC4HolonomyConjugationLaw
    ; u2ConnectionOneFormAsFibreAlgebraLocalReceipt =
        canonicalYMSFGCConnectionOneFormAsFibreAlgebraLocalReceipt
    ; u2ConnectionOneFormAsFibreAlgebraLocalReceiptIsCanonical =
        refl
    ; u2LocalFiniteLieValuedFormsAndCurvature =
        canonicalYMSFGCLocalFiniteLieValuedFormsAndCurvature
    ; u2LocalFiniteLieValuedFormsAndCurvatureIsCanonical =
        refl
    ; u2LocalDASquaredEqualsBracketF =
        localFiniteLie3DASquaredEqualsBracketFAOn0Forms
    ; m2HodgeStarLowerCandidate =
        sfgcSelectedHodgeStarLowerCandidate
    ; m2HodgeStarLowerCandidateIsIdentityProbe =
        refl
    ; m2ZeroVariationIBPLowerCandidate =
        canonicalYMSFGCDiscreteVariationIBPLowerCandidate
    ; m2ZeroVariationIBPLowerCandidateIsCanonical =
        refl
    ; m2FinalPrimitiveLowerLawCandidate =
        canonicalYMSFGCFinalPrimitiveLowerLawCandidate
    ; m2FinalPrimitiveLowerLawCandidateIsCanonical =
        refl
    ; strictRequestedConnectionCarrier =
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; strictRequestedConnectionCarrierIsUserSupplied =
        refl
    ; strictConnectionBridgeRequest =
        SFGC.SFGCSite2DDiscrete1Form →
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; strictConnectionBridgeRequestIsFiniteToUserSupplied =
        refl
    ; strictDualCurvatureBridgeRequest =
        SFGC.SFGCSite2DFieldStrengthBridge →
        YMSFGCUserSuppliedDualCurvatureCarrier
    ; strictDualCurvatureBridgeRequestIsFieldStrengthToUserSupplied =
        refl
    ; firstStrictM1Blocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; firstStrictM1BlockerIsNonFlatCurvature =
        refl
    ; firstStrictU2TransportBlocker =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; firstStrictU2TransportBlockerIsFieldStrengthAction =
        refl
    ; firstStrictU2CarrierBlocker =
        missingSFGCFibreRepresentationIntoSU3Carrier
    ; firstStrictU2CarrierBlockerIsSFGCFibreRepresentation =
        refl
    ; firstStrictM2Blocker =
        missingVariationPairingForSelectedHodgeStar
    ; firstStrictM2BlockerIsVariationPairing =
        refl
    ; strictRealYMPromoted =
        false
    ; strictRealYMPromotedIsFalse =
        refl
    ; consumedStaging =
        "m1 consumed: reference SFGCSite2DDiscrete1Form, δ1 curvature, φ1 reference-plaquette witness, finite C4 holonomy telescoping, and finite C4 conjugation"
        ∷ "u2 consumed: connectionOneFormAsFibreAlgebra local receipt, local finite Lie-valued forms, D_A formula, and D_A^2 = [F_A,_] local witness"
        ∷ "m2 consumed: identity selected Hodge endomap, zero variation/IBP lower candidate, and final lower-law candidate"
        ∷ "Wave 2 and Wave 3 strict-promotion decision receipts are consumed as non-promoting evidence"
        ∷ []
    ; failClosedBoundary =
        "Fail-closed: the finite non-flat SFGCSite2D curvature witness is real as a local finite Phase4 fact and now has a user-carrier adapter, but strict real Yang-Mills laws are not promoted"
        ∷ "Exact m1 blocker: missingNonFlatSFGCSite2DConnectionCurvature remains as the strict holonomy/law blocker after the finite carrier bridge"
        ∷ "Exact u2 blocker: missingFieldStrengthTransportActionOnSelectedGaugeBundle and missingSFGCFibreRepresentationIntoSU3Carrier"
        ∷ "Exact m2 blocker: missingVariationPairingForSelectedHodgeStar remains after adding the finite SFGCSite2DFieldStrengthBridge -> YMSFGCUserSuppliedDualCurvatureCarrier adapter"
        ∷ "No postulate, authority token, D * F = J theorem, D F = 0 theorem, mass gap, Clay claim, or terminal promotion is introduced"
        ∷ []
    }

yangMillsGate3M1U2M2WorkerFinalReceiptIsNonPromoting :
  YMSFGCGate3M1U2M2WorkerFinalReceipt.strictRealYMPromoted
    canonicalYMSFGCGate3M1U2M2WorkerFinalReceipt
  ≡
  false
yangMillsGate3M1U2M2WorkerFinalReceiptIsNonPromoting =
  refl

yangMillsGate3M1U2M2WorkerFinalM1BlockerIsExact :
  YMSFGCGate3M1U2M2WorkerFinalReceipt.firstStrictM1Blocker
    canonicalYMSFGCGate3M1U2M2WorkerFinalReceipt
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsGate3M1U2M2WorkerFinalM1BlockerIsExact =
  refl

yangMillsGate3M1U2M2WorkerFinalU2TransportBlockerIsExact :
  YMSFGCGate3M1U2M2WorkerFinalReceipt.firstStrictU2TransportBlocker
    canonicalYMSFGCGate3M1U2M2WorkerFinalReceipt
  ≡
  missingFieldStrengthTransportActionOnSelectedGaugeBundle
yangMillsGate3M1U2M2WorkerFinalU2TransportBlockerIsExact =
  refl

yangMillsGate3M1U2M2WorkerFinalM2BlockerIsExact :
  YMSFGCGate3M1U2M2WorkerFinalReceipt.firstStrictM2Blocker
    canonicalYMSFGCGate3M1U2M2WorkerFinalReceipt
  ≡
  missingVariationPairingForSelectedHodgeStar
yangMillsGate3M1U2M2WorkerFinalM2BlockerIsExact =
  refl

data YMSFGCGate3FirstMissingPrimitiveProgressStatus : Set where
  gate3FirstMissingPrimitiveFiniteShapesStagedStrictBridgesAbsent :
    YMSFGCGate3FirstMissingPrimitiveProgressStatus

record YMSFGCGate3FirstMissingPrimitiveProgressReceipt : Set₁ where
  field
    status :
      YMSFGCGate3FirstMissingPrimitiveProgressStatus

    consumedWorkerFinal :
      YMSFGCGate3M1U2M2WorkerFinalReceipt

    consumedWorkerFinalIsCanonical :
      consumedWorkerFinal
      ≡
      canonicalYMSFGCGate3M1U2M2WorkerFinalReceipt

    finiteSU3LikeCarrierShape :
      Set

    finiteSU3LikeCarrierShapeIsLocalFiniteSU3 :
      finiteSU3LikeCarrierShape
      ≡
      YMSFGCLocalFiniteSU3Carrier

    finiteSU3LikeConnectionOneForm :
      SFGC.GaugeField →
      YMSFGCLocalFiniteSU3Carrier

    finiteSU3LikeConnectionOneFormIsEmbedded :
      finiteSU3LikeConnectionOneForm
      ≡
      sfgcSelectedConnectionOneFormAsLocalFiniteSU3

    finiteSU3LikeConnectionProbeNonzero :
      finiteSU3LikeConnectionOneForm
        sfgcSelectedConstantPhi1GaugeField
      ≡
      localFiniteSU3Embed (lieBasis signPos axisX)

    finiteLie3CarrierShape :
      Set

    finiteLie3CarrierShapeIsLocalFiniteLie3 :
      finiteLie3CarrierShape
      ≡
      YMSFGCLocalFiniteLie3Carrier

    finiteLie3PrimitiveSupply :
      YMSFGCNonAbelianCovariantDerivativePrimitiveSupply

    finiteLie3PrimitiveSupplyIsCanonical :
      finiteLie3PrimitiveSupply
      ≡
      canonicalYMSFGCLocalFiniteLie3PrimitiveSupply

    connectionOneFormAsFibreAlgebraLocal :
      SFGC.GaugeField →
      YMSFGCLocalFiniteLie3Carrier

    connectionOneFormAsFibreAlgebraLocalIsSelected :
      connectionOneFormAsFibreAlgebraLocal
      ≡
      sfgcSelectedConnectionOneFormAsLocalFiniteLie3

    covariantDerivativePreStage :
      SFGC.GaugeField →
      YMSFGCLieValued0Form →
      YMSFGCLieValued0Form

    covariantDerivativePreStageIsLocalDA0 :
      covariantDerivativePreStage
      ≡
      localFiniteLie3DA0Form

    covariantDerivativeFormulaPreStage :
      (A : SFGC.GaugeField) →
      (section : YMSFGCLocalFiniteLie3Carrier) →
      covariantDerivativePreStage A (lieValued0 section)
      ≡
      localFiniteLie3DAExpectedRHS0Form A section

    covariantDerivativeSquarePreStage :
      (A : SFGC.GaugeField) →
      (section : YMSFGCLocalFiniteLie3Carrier) →
      covariantDerivativePreStage
        A
        (covariantDerivativePreStage A (lieValued0 section))
      ≡
      localFiniteLie3CurvatureBracketActionOn0Form
        (localFiniteLie3FA2Form A)
        (lieValued0 section)

    hodgeStarFiniteShape :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    hodgeStarFiniteShapeIsIdentityProbe :
      hodgeStarFiniteShape
      ≡
      sfgcSelectedHodgeStarLowerCandidate

    hodgeFiniteArithmeticSamePhase :
      SPTI4.phaseKernel4 SPTI4.φ0 SPTI4.φ0
      ≡
      + 1

    hodgeFiniteArithmeticOrthogonal :
      SPTI4.phaseKernel4 SPTI4.φ0 SPTI4.φ1
      ≡
      + 0

    requiredFiniteLie3ToUserLieBridge :
      Set

    requiredFiniteLie3ToUserLieBridgeIsAbsentShape :
      requiredFiniteLie3ToUserLieBridge
      ≡
      (YMSFGCLocalFiniteLie3Carrier →
       YMSFGCUserSuppliedLieAlgebraCarrier)

    firstExactNonFlatCurvatureBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstExactNonFlatCurvatureBlockerIsMissingNonFlatSFGCSite2DConnectionCurvature :
      firstExactNonFlatCurvatureBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    firstExactSelectedGaugeSectorBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    firstExactSelectedGaugeSectorBlockerIsMissingLieAlgebraCarrier :
      firstExactSelectedGaugeSectorBlocker
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    firstExactVariationPairingBlocker :
      YangMillsVariationalEquationMissingPrimitive

    firstExactVariationPairingBlockerIsMissingVariationPairing :
      firstExactVariationPairingBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    strictPromotion :
      Bool

    strictPromotionIsFalse :
      strictPromotion ≡ false

    progressBoundary :
      List String

canonicalYMSFGCGate3FirstMissingPrimitiveProgressReceipt :
  YMSFGCGate3FirstMissingPrimitiveProgressReceipt
canonicalYMSFGCGate3FirstMissingPrimitiveProgressReceipt =
  record
    { status =
        gate3FirstMissingPrimitiveFiniteShapesStagedStrictBridgesAbsent
    ; consumedWorkerFinal =
        canonicalYMSFGCGate3M1U2M2WorkerFinalReceipt
    ; consumedWorkerFinalIsCanonical =
        refl
    ; finiteSU3LikeCarrierShape =
        YMSFGCLocalFiniteSU3Carrier
    ; finiteSU3LikeCarrierShapeIsLocalFiniteSU3 =
        refl
    ; finiteSU3LikeConnectionOneForm =
        sfgcSelectedConnectionOneFormAsLocalFiniteSU3
    ; finiteSU3LikeConnectionOneFormIsEmbedded =
        refl
    ; finiteSU3LikeConnectionProbeNonzero =
        sfgcSelectedConnectionOneFormAsLocalFiniteSU3Nonzero
    ; finiteLie3CarrierShape =
        YMSFGCLocalFiniteLie3Carrier
    ; finiteLie3CarrierShapeIsLocalFiniteLie3 =
        refl
    ; finiteLie3PrimitiveSupply =
        canonicalYMSFGCLocalFiniteLie3PrimitiveSupply
    ; finiteLie3PrimitiveSupplyIsCanonical =
        refl
    ; connectionOneFormAsFibreAlgebraLocal =
        sfgcSelectedConnectionOneFormAsLocalFiniteLie3
    ; connectionOneFormAsFibreAlgebraLocalIsSelected =
        refl
    ; covariantDerivativePreStage =
        localFiniteLie3DA0Form
    ; covariantDerivativePreStageIsLocalDA0 =
        refl
    ; covariantDerivativeFormulaPreStage =
        localFiniteLie3DAFormulaOn0Forms
    ; covariantDerivativeSquarePreStage =
        localFiniteLie3DASquaredEqualsBracketFAOn0Forms
    ; hodgeStarFiniteShape =
        sfgcSelectedHodgeStarLowerCandidate
    ; hodgeStarFiniteShapeIsIdentityProbe =
        refl
    ; hodgeFiniteArithmeticSamePhase =
        SPTI4.samePhaseConstructiveKernel SPTI4.φ0
    ; hodgeFiniteArithmeticOrthogonal =
        SPTI4.orthogonalPhaseNeutralKernel
    ; requiredFiniteLie3ToUserLieBridge =
        YMSFGCLocalFiniteLie3Carrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; requiredFiniteLie3ToUserLieBridgeIsAbsentShape =
        refl
    ; firstExactNonFlatCurvatureBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; firstExactNonFlatCurvatureBlockerIsMissingNonFlatSFGCSite2DConnectionCurvature =
        refl
    ; firstExactSelectedGaugeSectorBlocker =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; firstExactSelectedGaugeSectorBlockerIsMissingLieAlgebraCarrier =
        refl
    ; firstExactVariationPairingBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; firstExactVariationPairingBlockerIsMissingVariationPairing =
        refl
    ; strictPromotion =
        false
    ; strictPromotionIsFalse =
        refl
    ; progressBoundary =
        "Gate 3 first-missing progress: finite SU3-like carrier shape is staged only as YMSFGCLocalFiniteSU3Carrier via localFiniteSU3Embed"
        ∷ "Gate 3 first-missing progress: connectionOneFormAsFibreAlgebra and D_A pre-stage are local finite Lie3 shapes with D_A = d + [A,_] and D_A^2 = [F_A,_] witnesses"
        ∷ "Gate 3 first-missing progress: the Hodge-star finite arithmetic shape is only the identity field-strength probe plus Phase4 kernel arithmetic"
        ∷ "Fail-closed exact blockers: missingNonFlatSFGCSite2DConnectionCurvature, missingLieAlgebraCarrierForSelectedFiniteGaugeSector, and missingVariationPairingForSelectedHodgeStar"
        ∷ "The SFGC 1-form bridge is supplied; Phase4 holonomy and local Lie3/local SU3-like evidence still do not bridge into the user-supplied holonomy or Lie carriers"
        ∷ []
    }

yangMillsGate3FirstMissingPrimitiveProgressIsNonPromoting :
  YMSFGCGate3FirstMissingPrimitiveProgressReceipt.strictPromotion
    canonicalYMSFGCGate3FirstMissingPrimitiveProgressReceipt
  ≡
  false
yangMillsGate3FirstMissingPrimitiveProgressIsNonPromoting =
  refl

yangMillsGate3FirstMissingPrimitiveProgressNonFlatBlockerIsExact :
  YMSFGCGate3FirstMissingPrimitiveProgressReceipt.firstExactNonFlatCurvatureBlocker
    canonicalYMSFGCGate3FirstMissingPrimitiveProgressReceipt
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsGate3FirstMissingPrimitiveProgressNonFlatBlockerIsExact =
  refl

yangMillsGate3FirstMissingPrimitiveProgressGaugeSectorBlockerIsExact :
  YMSFGCGate3FirstMissingPrimitiveProgressReceipt.firstExactSelectedGaugeSectorBlocker
    canonicalYMSFGCGate3FirstMissingPrimitiveProgressReceipt
  ≡
  missingLieAlgebraCarrierForSelectedFiniteGaugeSector
yangMillsGate3FirstMissingPrimitiveProgressGaugeSectorBlockerIsExact =
  refl

yangMillsGate3FirstMissingPrimitiveProgressVariationBlockerIsExact :
  YMSFGCGate3FirstMissingPrimitiveProgressReceipt.firstExactVariationPairingBlocker
    canonicalYMSFGCGate3FirstMissingPrimitiveProgressReceipt
  ≡
  missingVariationPairingForSelectedHodgeStar
yangMillsGate3FirstMissingPrimitiveProgressVariationBlockerIsExact =
  refl

------------------------------------------------------------------------
-- lower6 next-wave YM arithmetic attempts.
--
-- These receipts name the concrete finite arithmetic attempted for m1/m2 in
-- the next wave.  They deliberately stop at the existing strict bridges:
-- the local finite SU3/Lie3/Phase4 witnesses are not the requested
-- user-supplied real non-flat Yang-Mills carriers.

data YMSFGCNextWaveFiniteSU3CurvatureAttemptStatus : Set where
  nextWaveFiniteSU3CurvatureArithmeticAttemptFailClosed :
    YMSFGCNextWaveFiniteSU3CurvatureAttemptStatus

record YMSFGCNextWaveFiniteSU3NonFlatCurvatureArithmeticAttemptReceipt : Set₁ where
  field
    status :
      YMSFGCNextWaveFiniteSU3CurvatureAttemptStatus

    finiteSU3LikeCarrier :
      Set

    finiteSU3LikeCarrierIsLocalFiniteSU3 :
      finiteSU3LikeCarrier
      ≡
      YMSFGCLocalFiniteSU3Carrier

    finiteSU3LikeBracket :
      YMSFGCLocalFiniteSU3Carrier →
      YMSFGCLocalFiniteSU3Carrier →
      YMSFGCLocalFiniteSU3Carrier

    finiteSU3LikeBracketIsCanonical :
      finiteSU3LikeBracket
      ≡
      localFiniteSU3Bracket

    finiteEmbeddedSU2XYBracketWitness :
      localFiniteSU3Bracket
        (localFiniteSU3Embed (lieBasis signPos axisX))
        (localFiniteSU3Embed (lieBasis signPos axisY))
      ≡
      localFiniteSU3Embed (lieBasis signPos axisZ)

    finiteSU3LikeConnectionOneForm :
      SFGC.GaugeField →
      YMSFGCLocalFiniteSU3Carrier

    finiteSU3LikeConnectionOneFormIsEmbedded :
      finiteSU3LikeConnectionOneForm
      ≡
      sfgcSelectedConnectionOneFormAsLocalFiniteSU3

    finiteSU3LikeConnectionProbeNonzero :
      finiteSU3LikeConnectionOneForm
        sfgcSelectedConstantPhi1GaugeField
      ≡
      localFiniteSU3Embed (lieBasis signPos axisX)

    referenceFiniteConnectionCarrier :
      Set

    referenceFiniteConnectionCarrierIsSFGC1Form :
      referenceFiniteConnectionCarrier
      ≡
      SFGC.SFGCSite2DDiscrete1Form

    referenceFinitePlaquetteCurvatureWitness :
      SFGC.sfgcSite2DEvaluate2
        (SFGC.sfgcSite2Dδ₁ sfgcReferenceNonFlat1Form)
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    referenceFiniteFieldStrengthWitness :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        sfgcReferenceNonFlatFieldStrengthBridge
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    finiteTraceAdInvarianceAttempt :
      YMSFGCLieAlgebraTraceAdInvariancePrimitiveSupply

    finiteTraceAdInvarianceAttemptIsCanonical :
      finiteTraceAdInvarianceAttempt
      ≡
      canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply

    strictConnectionCarrierBridgeRequired :
      Set

    strictConnectionCarrierBridgeRequiredIsFiniteToUserSupplied :
      strictConnectionCarrierBridgeRequired
      ≡
      (SFGC.SFGCSite2DDiscrete1Form →
       YMSFGCUserSuppliedNonFlatConnectionCarrier)

    strictLieCarrierBridgeRequired :
      Set

    strictLieCarrierBridgeRequiredIsFiniteToUserSupplied :
      strictLieCarrierBridgeRequired
      ≡
      (YMSFGCLocalFiniteSU3Carrier →
       YMSFGCUserSuppliedLieAlgebraCarrier)

    exactNonFlatCurvatureBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    exactNonFlatCurvatureBlockerIsMissingNonFlatCurvature :
      exactNonFlatCurvatureBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    exactLieCarrierBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    exactLieCarrierBlockerIsMissingLieAlgebraCarrier :
      exactLieCarrierBlocker
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    strictRealNonFlatCurvaturePromoted :
      Bool

    strictRealNonFlatCurvaturePromotedIsFalse :
      strictRealNonFlatCurvaturePromoted ≡ false

    arithmeticBoundary :
      List String

canonicalYMSFGCNextWaveFiniteSU3NonFlatCurvatureArithmeticAttemptReceipt :
  YMSFGCNextWaveFiniteSU3NonFlatCurvatureArithmeticAttemptReceipt
canonicalYMSFGCNextWaveFiniteSU3NonFlatCurvatureArithmeticAttemptReceipt =
  record
    { status =
        nextWaveFiniteSU3CurvatureArithmeticAttemptFailClosed
    ; finiteSU3LikeCarrier =
        YMSFGCLocalFiniteSU3Carrier
    ; finiteSU3LikeCarrierIsLocalFiniteSU3 =
        refl
    ; finiteSU3LikeBracket =
        localFiniteSU3Bracket
    ; finiteSU3LikeBracketIsCanonical =
        refl
    ; finiteEmbeddedSU2XYBracketWitness =
        localFiniteSU3EmbeddedSU2XYBracket
    ; finiteSU3LikeConnectionOneForm =
        sfgcSelectedConnectionOneFormAsLocalFiniteSU3
    ; finiteSU3LikeConnectionOneFormIsEmbedded =
        refl
    ; finiteSU3LikeConnectionProbeNonzero =
        sfgcSelectedConnectionOneFormAsLocalFiniteSU3Nonzero
    ; referenceFiniteConnectionCarrier =
        SFGC.SFGCSite2DDiscrete1Form
    ; referenceFiniteConnectionCarrierIsSFGC1Form =
        refl
    ; referenceFinitePlaquetteCurvatureWitness =
        sfgcReferenceNonFlatCurvatureAtReference
    ; referenceFiniteFieldStrengthWitness =
        sfgcReferenceNonFlatFieldStrengthAtReference
    ; finiteTraceAdInvarianceAttempt =
        canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply
    ; finiteTraceAdInvarianceAttemptIsCanonical =
        refl
    ; strictConnectionCarrierBridgeRequired =
        SFGC.SFGCSite2DDiscrete1Form →
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; strictConnectionCarrierBridgeRequiredIsFiniteToUserSupplied =
        refl
    ; strictLieCarrierBridgeRequired =
        YMSFGCLocalFiniteSU3Carrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; strictLieCarrierBridgeRequiredIsFiniteToUserSupplied =
        refl
    ; exactNonFlatCurvatureBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; exactNonFlatCurvatureBlockerIsMissingNonFlatCurvature =
        refl
    ; exactLieCarrierBlocker =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; exactLieCarrierBlockerIsMissingLieAlgebraCarrier =
        refl
    ; strictRealNonFlatCurvaturePromoted =
        false
    ; strictRealNonFlatCurvaturePromotedIsFalse =
        refl
    ; arithmeticBoundary =
        "m1 next wave attempts the finite SU3-like arithmetic using the local finite SU3 carrier and bracket already in this module"
        ∷ "The reference finite plaquette curvature and field-strength witnesses are real finite Phase4 facts at the selected reference plaquette"
        ∷ "The finite trace/Ad-invariance attempt consumes the selected finite-C4 trace receipt"
        ∷ "Strict promotion consumes the SFGCSite2DDiscrete1Form bridge, but still requires a local finite SU3/Lie bridge and non-flat holonomy laws over the user-supplied real Yang-Mills carriers"
        ∷ "Therefore missingNonFlatSFGCSite2DConnectionCurvature and missingLieAlgebraCarrierForSelectedFiniteGaugeSector remain exact law blockers"
        ∷ []
    }

data YMSFGCNextWaveHodgeEpsilonAssistanceStatus : Set where
  nextWaveHodgeEpsilonFiniteCaseAssistanceFailClosed :
    YMSFGCNextWaveHodgeEpsilonAssistanceStatus

data YMSFGCNextWaveEpsilonContractionCaseClass : Set where
  epsilonRepeatedIndexZeroCase :
    YMSFGCNextWaveEpsilonContractionCaseClass

  epsilonMatchingPairPositiveCase :
    YMSFGCNextWaveEpsilonContractionCaseClass

  epsilonSwappedPairNegativeCase :
    YMSFGCNextWaveEpsilonContractionCaseClass

  epsilonDisjointPairZeroCase :
    YMSFGCNextWaveEpsilonContractionCaseClass

canonicalYMSFGCNextWaveEpsilonContractionCaseClasses :
  List YMSFGCNextWaveEpsilonContractionCaseClass
canonicalYMSFGCNextWaveEpsilonContractionCaseClasses =
  epsilonRepeatedIndexZeroCase
  ∷ epsilonMatchingPairPositiveCase
  ∷ epsilonSwappedPairNegativeCase
  ∷ epsilonDisjointPairZeroCase
  ∷ []

record YMSFGCNextWaveHodgeEpsilonContractionAssistanceReceipt : Set₁ where
  field
    status :
      YMSFGCNextWaveHodgeEpsilonAssistanceStatus

    epsilonCaseClasses :
      List YMSFGCNextWaveEpsilonContractionCaseClass

    epsilonCaseClassesAreCanonical :
      epsilonCaseClasses
      ≡
      canonicalYMSFGCNextWaveEpsilonContractionCaseClasses

    finiteCaseCountDescription :
      String

    finiteCaseCountDescriptionIsFin4Tensor :
      finiteCaseCountDescription
      ≡
      "Fin4^4 outer indices with Fin4^2 contraction, 256 outer cases"

    samePhaseKernelWitness :
      SPTI4.phaseKernel4 SPTI4.φ0 SPTI4.φ0
      ≡
      + 1

    orthogonalPhaseKernelWitness :
      SPTI4.phaseKernel4 SPTI4.φ0 SPTI4.φ1
      ≡
      + 0

    selectedHodgeLowerCandidate :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    selectedHodgeLowerCandidateIsIdentityProbe :
      selectedHodgeLowerCandidate
      ≡
      sfgcSelectedHodgeStarLowerCandidate

    strictHodgeStarTypeRequired :
      Set

    strictHodgeStarTypeRequiredIsDiscrete2FormToDual :
      strictHodgeStarTypeRequired
      ≡
      (SFGC.SFGCSite2DDiscrete2Form →
       YMSFGCUserSuppliedDualCurvatureCarrier)

    exactVariationPairingBlocker :
      YangMillsVariationalEquationMissingPrimitive

    exactVariationPairingBlockerIsMissingVariationPairing :
      exactVariationPairingBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    epsilonContractionPromotedToMetricHodge :
      Bool

    epsilonContractionPromotedToMetricHodgeIsFalse :
      epsilonContractionPromotedToMetricHodge ≡ false

    assistanceBoundary :
      List String

canonicalYMSFGCNextWaveHodgeEpsilonContractionAssistanceReceipt :
  YMSFGCNextWaveHodgeEpsilonContractionAssistanceReceipt
canonicalYMSFGCNextWaveHodgeEpsilonContractionAssistanceReceipt =
  record
    { status =
        nextWaveHodgeEpsilonFiniteCaseAssistanceFailClosed
    ; epsilonCaseClasses =
        canonicalYMSFGCNextWaveEpsilonContractionCaseClasses
    ; epsilonCaseClassesAreCanonical =
        refl
    ; finiteCaseCountDescription =
        "Fin4^4 outer indices with Fin4^2 contraction, 256 outer cases"
    ; finiteCaseCountDescriptionIsFin4Tensor =
        refl
    ; samePhaseKernelWitness =
        SPTI4.samePhaseConstructiveKernel SPTI4.φ0
    ; orthogonalPhaseKernelWitness =
        SPTI4.orthogonalPhaseNeutralKernel
    ; selectedHodgeLowerCandidate =
        sfgcSelectedHodgeStarLowerCandidate
    ; selectedHodgeLowerCandidateIsIdentityProbe =
        refl
    ; strictHodgeStarTypeRequired =
        SFGC.SFGCSite2DDiscrete2Form →
        YMSFGCUserSuppliedDualCurvatureCarrier
    ; strictHodgeStarTypeRequiredIsDiscrete2FormToDual =
        refl
    ; exactVariationPairingBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; exactVariationPairingBlockerIsMissingVariationPairing =
        refl
    ; epsilonContractionPromotedToMetricHodge =
        false
    ; epsilonContractionPromotedToMetricHodgeIsFalse =
        refl
    ; assistanceBoundary =
        "m2/l6 next wave classifies the finite epsilon contraction into repeated, matching, swapped, and disjoint index cases"
        ∷ "The only inhabited arithmetic reused here is Phase4 kernel arithmetic plus the existing selected Hodge identity probe"
        ∷ "No metric Hodge star on SFGCSite2DDiscrete2Form is constructed; only the finite field-strength-to-dual carrier adapter exists"
        ∷ "missingVariationPairingForSelectedHodgeStar remains the exact Route B blocker"
        ∷ []
    }

yangMillsNextWaveFiniteSU3CurvatureAttemptIsNonPromoting :
  YMSFGCNextWaveFiniteSU3NonFlatCurvatureArithmeticAttemptReceipt.strictRealNonFlatCurvaturePromoted
    canonicalYMSFGCNextWaveFiniteSU3NonFlatCurvatureArithmeticAttemptReceipt
  ≡
  false
yangMillsNextWaveFiniteSU3CurvatureAttemptIsNonPromoting =
  refl

yangMillsNextWaveHodgeEpsilonAssistanceIsNonPromoting :
  YMSFGCNextWaveHodgeEpsilonContractionAssistanceReceipt.epsilonContractionPromotedToMetricHodge
    canonicalYMSFGCNextWaveHodgeEpsilonContractionAssistanceReceipt
  ≡
  false
yangMillsNextWaveHodgeEpsilonAssistanceIsNonPromoting =
  refl

data YMSFGCEmpty : Set where

ymSFGCUserSuppliedReferenceConnection1FormIsReference :
  ymSFGCUserSuppliedConnection1Form
    ymSFGCUserSuppliedReferenceNonFlatConnection
  ≡
  sfgcReferenceNonFlat1Form
ymSFGCUserSuppliedReferenceConnection1FormIsReference =
  refl

ymSFGCUserSuppliedReferenceCurvatureAtReference :
  SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
    (ymSFGCUserSuppliedReferenceNonFlatCurvature
      sfgcReferencePlaquette)
    sfgcReferencePlaquette
  ≡
  SPTI4.φ1
ymSFGCUserSuppliedReferenceCurvatureAtReference =
  refl

phase4φ1Notφ0 :
  SPTI4.φ1 ≡ SPTI4.φ0 →
  YMSFGCEmpty
phase4φ1Notφ0 ()

sfgcReferenceNonFlatCurvatureAtReferenceNotVacuum :
  SFGC.sfgcSite2DEvaluate2
    sfgcReferenceNonFlatCurvature2Form
    sfgcReferencePlaquette
  ≡
  SPTI4.φ0 →
  YMSFGCEmpty
sfgcReferenceNonFlatCurvatureAtReferenceNotVacuum curvatureIsVacuum =
  phase4φ1Notφ0
    (trans
      (symEq sfgcReferenceNonFlatCurvatureAtReference)
      curvatureIsVacuum)

localFiniteLie3EpsilonContractionShape :
  Set
localFiniteLie3EpsilonContractionShape =
  (x y z : YMSFGCLocalFiniteLie3Axis) →
  localFiniteLie3JacobiAdd
    (localFiniteLie3JacobiAdd
      (localFiniteLie3Bracket
        (lieBasis signPos x)
        (localFiniteLie3Bracket (lieBasis signPos y) (lieBasis signPos z)))
      (localFiniteLie3Bracket
        (lieBasis signPos y)
        (localFiniteLie3Bracket (lieBasis signPos z) (lieBasis signPos x))))
    (localFiniteLie3Bracket
      (lieBasis signPos z)
      (localFiniteLie3Bracket (lieBasis signPos x) (lieBasis signPos y)))
  ≡
  lieZero

record YMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals : Set₁ where
  field
    crossProductAntisymmetryResidualShape :
      Set

    crossProductAntisymmetryResidualShapeIsLocalFiniteLie3 :
      crossProductAntisymmetryResidualShape
      ≡
      ((x y : YMSFGCLocalFiniteLie3Carrier) →
       localFiniteLie3Bracket x y
       ≡
       localFiniteLie3Neg (localFiniteLie3Bracket y x))

    crossProductAntisymmetryLocalWitness :
      (x y : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3Bracket x y
      ≡
      localFiniteLie3Neg (localFiniteLie3Bracket y x)

    crossProductJacobiResidualShape :
      Set

    crossProductJacobiResidualShapeIsLocalFiniteLie3 :
      crossProductJacobiResidualShape
      ≡
      ((x y z : YMSFGCLocalFiniteLie3Carrier) →
       localFiniteLie3JacobiAdd
         (localFiniteLie3JacobiAdd
           (localFiniteLie3Bracket x (localFiniteLie3Bracket y z))
           (localFiniteLie3Bracket y (localFiniteLie3Bracket z x)))
         (localFiniteLie3Bracket z (localFiniteLie3Bracket x y))
       ≡
       lieZero)

    crossProductJacobiLocalWitness :
      (x y z : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3JacobiAdd
        (localFiniteLie3JacobiAdd
          (localFiniteLie3Bracket x (localFiniteLie3Bracket y z))
          (localFiniteLie3Bracket y (localFiniteLie3Bracket z x)))
        (localFiniteLie3Bracket z (localFiniteLie3Bracket x y))
      ≡
      lieZero

    referenceWilsonLoopNonzeroResidualShape :
      Set

    referenceWilsonLoopNonzeroResidualShapeIsQuarterTurnNotVacuum :
      referenceWilsonLoopNonzeroResidualShape
      ≡
      (SFGC.sfgcSite2DEvaluate2
        sfgcReferenceNonFlatCurvature2Form
        sfgcReferencePlaquette
       ≡
       SPTI4.φ0 →
       YMSFGCEmpty)

    referenceWilsonLoopQuarterTurnWitness :
      SFGC.sfgcSite2DEvaluate2
        sfgcReferenceNonFlatCurvature2Form
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    referenceWilsonLoopNotVacuumWitness :
      SFGC.sfgcSite2DEvaluate2
        sfgcReferenceNonFlatCurvature2Form
        sfgcReferencePlaquette
      ≡
      SPTI4.φ0 →
      YMSFGCEmpty

    epsilonContractionResidualShape :
      Set

    epsilonContractionResidualShapeIsPositiveAxisJacobi :
      epsilonContractionResidualShape
      ≡
      localFiniteLie3EpsilonContractionShape

    epsilonContractionLocalWitness :
      localFiniteLie3EpsilonContractionShape

    strictRealConnectionCarrierShape :
      Set

    strictRealConnectionCarrierShapeIsUserSupplied :
      strictRealConnectionCarrierShape
      ≡
      YMSFGCUserSuppliedNonFlatConnectionCarrier

    strictRealTransportActionShape :
      Set

    strictRealTransportActionShapeIsMissing :
      strictRealTransportActionShape
      ≡
      ((connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
       SFGC.SFGCSite2DEdge →
       SFGC.SFGCSite2DFieldStrengthBridge →
       SFGC.SFGCSite2DFieldStrengthBridge)

    firstStrictCurvatureBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictCurvatureBlockerIsNonFlatCurvature :
      firstStrictCurvatureBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    firstStrictTransportBlocker :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    firstStrictTransportBlockerIsFieldStrengthAction :
      firstStrictTransportBlocker
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    firstStrictHodgeActionBlocker :
      YangMillsVariationalEquationMissingPrimitive

    firstStrictHodgeActionBlockerIsVariationPairing :
      firstStrictHodgeActionBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    strictPromotion :
      Bool

    strictPromotionIsFalse :
      strictPromotion ≡ false

    residualBoundary :
      List String

canonicalYMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals :
  YMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals
canonicalYMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals =
  record
    { crossProductAntisymmetryResidualShape =
        (x y : YMSFGCLocalFiniteLie3Carrier) →
        localFiniteLie3Bracket x y
        ≡
        localFiniteLie3Neg (localFiniteLie3Bracket y x)
    ; crossProductAntisymmetryResidualShapeIsLocalFiniteLie3 =
        refl
    ; crossProductAntisymmetryLocalWitness =
        localFiniteLie3BracketAntisymmetry
    ; crossProductJacobiResidualShape =
        (x y z : YMSFGCLocalFiniteLie3Carrier) →
        localFiniteLie3JacobiAdd
          (localFiniteLie3JacobiAdd
            (localFiniteLie3Bracket x (localFiniteLie3Bracket y z))
            (localFiniteLie3Bracket y (localFiniteLie3Bracket z x)))
          (localFiniteLie3Bracket z (localFiniteLie3Bracket x y))
        ≡
        lieZero
    ; crossProductJacobiResidualShapeIsLocalFiniteLie3 =
        refl
    ; crossProductJacobiLocalWitness =
        localFiniteLie3JacobiWitness
    ; referenceWilsonLoopNonzeroResidualShape =
        SFGC.sfgcSite2DEvaluate2
          sfgcReferenceNonFlatCurvature2Form
          sfgcReferencePlaquette
        ≡
        SPTI4.φ0 →
        YMSFGCEmpty
    ; referenceWilsonLoopNonzeroResidualShapeIsQuarterTurnNotVacuum =
        refl
    ; referenceWilsonLoopQuarterTurnWitness =
        sfgcReferenceNonFlatCurvatureAtReference
    ; referenceWilsonLoopNotVacuumWitness =
        sfgcReferenceNonFlatCurvatureAtReferenceNotVacuum
    ; epsilonContractionResidualShape =
        localFiniteLie3EpsilonContractionShape
    ; epsilonContractionResidualShapeIsPositiveAxisJacobi =
        refl
    ; epsilonContractionLocalWitness =
        localFiniteLie3PositiveAxisJacobi
    ; strictRealConnectionCarrierShape =
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; strictRealConnectionCarrierShapeIsUserSupplied =
        refl
    ; strictRealTransportActionShape =
        (connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
        SFGC.SFGCSite2DEdge →
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; strictRealTransportActionShapeIsMissing =
        refl
    ; firstStrictCurvatureBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; firstStrictCurvatureBlockerIsNonFlatCurvature =
        refl
    ; firstStrictTransportBlocker =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; firstStrictTransportBlockerIsFieldStrengthAction =
        refl
    ; firstStrictHodgeActionBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; firstStrictHodgeActionBlockerIsVariationPairing =
        refl
    ; strictPromotion =
        false
    ; strictPromotionIsFalse =
        refl
    ; residualBoundary =
        "Gate3 genuine first-missing finite arithmetic residuals: local cross-product antisymmetry and Jacobi are inhabited on YMSFGCLocalFiniteLie3Carrier"
        ∷ "The reference Site2D arbitrary 1-form has Wilson-loop curvature φ1 at sfgcReferencePlaquette, with a named φ1-not-φ0 non-vacuum residual"
        ∷ "The epsilon-contraction shape is the positive-axis Jacobi contraction over the three local finite Lie axes"
        ∷ "These are finite arithmetic witnesses only; the non-flat connection carrier is inhabited by the SFGC adapter, while strict real promotion still needs gauge action, section, and transport laws"
        ∷ "The exact strict blockers remain missingNonFlatSFGCSite2DConnectionCurvature, missingFieldStrengthTransportActionOnSelectedGaugeBundle, and missingVariationPairingForSelectedHodgeStar"
        ∷ []
    }

yangMillsGate3GenuineFirstMissingResidualsStrictPromotionFalse :
  YMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals.strictPromotion
    canonicalYMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals
  ≡
  false
yangMillsGate3GenuineFirstMissingResidualsStrictPromotionFalse =
  refl

yangMillsGate3GenuineFirstMissingResidualsNonFlatBlockerIsExact :
  YMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals.firstStrictCurvatureBlocker
    canonicalYMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsGate3GenuineFirstMissingResidualsNonFlatBlockerIsExact =
  refl

data YMSFGCGate3GenuineFirstMissingNextIterationStatus : Set where
  gate3GenuineFirstMissingNextIterationExactResidualsFailClosed :
    YMSFGCGate3GenuineFirstMissingNextIterationStatus

record YMSFGCGate3GenuineFirstMissingNextIterationTypedResidualReceipt : Set₁ where
  field
    status :
      YMSFGCGate3GenuineFirstMissingNextIterationStatus

    consumedFiniteArithmeticResiduals :
      YMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals

    consumedFiniteArithmeticResidualsAreCanonical :
      consumedFiniteArithmeticResiduals
      ≡
      canonicalYMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals

    phase4CrossProductAntisymmetry :
      (x y : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3Bracket x y
      ≡
      localFiniteLie3Neg (localFiniteLie3Bracket y x)

    phase4CrossProductJacobi :
      (x y z : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3JacobiAdd
        (localFiniteLie3JacobiAdd
          (localFiniteLie3Bracket x (localFiniteLie3Bracket y z))
          (localFiniteLie3Bracket y (localFiniteLie3Bracket z x)))
        (localFiniteLie3Bracket z (localFiniteLie3Bracket x y))
      ≡
      lieZero

    referenceWilsonLoopQuarterTurn :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        sfgcReferenceNonFlatFieldStrengthBridge
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    referenceWilsonLoopNotVacuum :
      SFGC.sfgcSite2DEvaluate2
        sfgcReferenceNonFlatCurvature2Form
        sfgcReferencePlaquette
      ≡
      SPTI4.φ0 →
      YMSFGCEmpty

    realNonFlatConnectionBridgeRequired :
      Set

    realNonFlatConnectionBridgeRequiredIsFiniteToUserSupplied :
      realNonFlatConnectionBridgeRequired
      ≡
      (SFGC.SFGCSite2DDiscrete1Form →
       YMSFGCUserSuppliedNonFlatConnectionCarrier)

    selectedLieCarrierBridgeRequired :
      Set

    selectedLieCarrierBridgeRequiredIsFiniteLie3ToUserSupplied :
      selectedLieCarrierBridgeRequired
      ≡
      (YMSFGCLocalFiniteLie3Carrier →
       YMSFGCUserSuppliedLieAlgebraCarrier)

    fieldStrengthTransportRequired :
      Set

    fieldStrengthTransportRequiredIsUserConnectionEdgeAction :
      fieldStrengthTransportRequired
      ≡
      ((connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
       SFGC.SFGCSite2DEdge →
       SFGC.SFGCSite2DFieldStrengthBridge →
       SFGC.SFGCSite2DFieldStrengthBridge)

    adjointTransportRequired :
      Set

    adjointTransportRequiredIsUserGaugeAdjoint :
      adjointTransportRequired
      ≡
      (SFGS.GaugeTransform →
       YMSFGCUserSuppliedLieAlgebraCarrier →
       YMSFGCUserSuppliedLieAlgebraCarrier)

    finiteTraceAdInvarianceSupply :
      YMSFGCLieAlgebraTraceAdInvariancePrimitiveSupply

    finiteTraceAdInvarianceSupplyIsCanonical :
      finiteTraceAdInvarianceSupply
      ≡
      canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply

    strictKillingOrTracePairingRequired :
      Set

    strictKillingOrTracePairingRequiredIsUserLiePairing :
      strictKillingOrTracePairingRequired
      ≡
      (YMSFGCUserSuppliedLieAlgebraCarrier →
       YMSFGCUserSuppliedLieAlgebraCarrier →
       ℤ)

    hodgeEpsilonContractionWitness :
      localFiniteLie3EpsilonContractionShape

    strictHodgeStarRequired :
      Set

    strictHodgeStarRequiredIsDiscrete2FormToDual :
      strictHodgeStarRequired
      ≡
      (SFGC.SFGCSite2DDiscrete2Form →
       YMSFGCUserSuppliedDualCurvatureCarrier)

    variationPairingRequired :
      Set

    variationPairingRequiredIsUserActionVariation :
      variationPairingRequired
      ≡
      (YMSFGCUserSuppliedNonFlatConnectionCarrier →
       YMSFGCUserSuppliedVariationCarrier →
       YMSFGCUserSuppliedActionScalarCarrier)

    firstStrictCurvatureBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictCurvatureBlockerIsNonFlatCurvature :
      firstStrictCurvatureBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    firstStrictSelectedLieBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    firstStrictSelectedLieBlockerIsLieCarrier :
      firstStrictSelectedLieBlocker
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    firstStrictTransportBlocker :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    firstStrictTransportBlockerIsFieldStrengthAction :
      firstStrictTransportBlocker
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    firstStrictVariationBlocker :
      YangMillsVariationalEquationMissingPrimitive

    firstStrictVariationBlockerIsVariationPairing :
      firstStrictVariationBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    strictRealYMPromoted :
      Bool

    strictRealYMPromotedIsFalse :
      strictRealYMPromoted ≡ false

    nextIterationBoundary :
      List String

canonicalYMSFGCGate3GenuineFirstMissingNextIterationTypedResidualReceipt :
  YMSFGCGate3GenuineFirstMissingNextIterationTypedResidualReceipt
canonicalYMSFGCGate3GenuineFirstMissingNextIterationTypedResidualReceipt =
  record
    { status =
        gate3GenuineFirstMissingNextIterationExactResidualsFailClosed
    ; consumedFiniteArithmeticResiduals =
        canonicalYMSFGCGate3GenuineFirstMissingFiniteArithmeticResiduals
    ; consumedFiniteArithmeticResidualsAreCanonical =
        refl
    ; phase4CrossProductAntisymmetry =
        localFiniteLie3BracketAntisymmetry
    ; phase4CrossProductJacobi =
        localFiniteLie3JacobiWitness
    ; referenceWilsonLoopQuarterTurn =
        sfgcReferenceNonFlatFieldStrengthAtReference
    ; referenceWilsonLoopNotVacuum =
        sfgcReferenceNonFlatCurvatureAtReferenceNotVacuum
    ; realNonFlatConnectionBridgeRequired =
        SFGC.SFGCSite2DDiscrete1Form →
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; realNonFlatConnectionBridgeRequiredIsFiniteToUserSupplied =
        refl
    ; selectedLieCarrierBridgeRequired =
        YMSFGCLocalFiniteLie3Carrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; selectedLieCarrierBridgeRequiredIsFiniteLie3ToUserSupplied =
        refl
    ; fieldStrengthTransportRequired =
        (connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
        SFGC.SFGCSite2DEdge →
        SFGC.SFGCSite2DFieldStrengthBridge →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; fieldStrengthTransportRequiredIsUserConnectionEdgeAction =
        refl
    ; adjointTransportRequired =
        SFGS.GaugeTransform →
        YMSFGCUserSuppliedLieAlgebraCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; adjointTransportRequiredIsUserGaugeAdjoint =
        refl
    ; finiteTraceAdInvarianceSupply =
        canonicalYMSFGCSelectedFiniteC4TraceAdInvariancePrimitiveSupply
    ; finiteTraceAdInvarianceSupplyIsCanonical =
        refl
    ; strictKillingOrTracePairingRequired =
        YMSFGCUserSuppliedLieAlgebraCarrier →
        YMSFGCUserSuppliedLieAlgebraCarrier →
        ℤ
    ; strictKillingOrTracePairingRequiredIsUserLiePairing =
        refl
    ; hodgeEpsilonContractionWitness =
        localFiniteLie3PositiveAxisJacobi
    ; strictHodgeStarRequired =
        SFGC.SFGCSite2DDiscrete2Form →
        YMSFGCUserSuppliedDualCurvatureCarrier
    ; strictHodgeStarRequiredIsDiscrete2FormToDual =
        refl
    ; variationPairingRequired =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMSFGCUserSuppliedVariationCarrier →
        YMSFGCUserSuppliedActionScalarCarrier
    ; variationPairingRequiredIsUserActionVariation =
        refl
    ; firstStrictCurvatureBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; firstStrictCurvatureBlockerIsNonFlatCurvature =
        refl
    ; firstStrictSelectedLieBlocker =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; firstStrictSelectedLieBlockerIsLieCarrier =
        refl
    ; firstStrictTransportBlocker =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; firstStrictTransportBlockerIsFieldStrengthAction =
        refl
    ; firstStrictVariationBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; firstStrictVariationBlockerIsVariationPairing =
        refl
    ; strictRealYMPromoted =
        false
    ; strictRealYMPromotedIsFalse =
        refl
    ; nextIterationBoundary =
        "Next iteration residuals consume the finite arithmetic receipt: local Lie3 cross-product antisymmetry/Jacobi, φ1 Wilson-loop nonzero witness, and finite epsilon contraction are inhabited"
        ∷ "Wilson-loop nonzero is only a finite SFGCSite2D/Phase4 fact; it is not a real non-flat Yang-Mills connection section"
        ∷ "Selected Lie evidence remains local finite Lie3 plus finite-C4 trace/Ad invariance; no bridge into the user-supplied real Lie carrier is inhabited"
        ∷ "Adjoint transport, field-strength transport, Killing/trace pairing, Hodge star to dual curvature, and variation pairing are recorded as exact required user-supplied shapes"
        ∷ "Exact blockers remain missingNonFlatSFGCSite2DConnectionCurvature, missingLieAlgebraCarrierForSelectedFiniteGaugeSector, missingFieldStrengthTransportActionOnSelectedGaugeBundle, and missingVariationPairingForSelectedHodgeStar"
        ∷ []
    }

yangMillsGate3GenuineFirstMissingNextIterationStrictPromotionFalse :
  YMSFGCGate3GenuineFirstMissingNextIterationTypedResidualReceipt.strictRealYMPromoted
    canonicalYMSFGCGate3GenuineFirstMissingNextIterationTypedResidualReceipt
  ≡
  false
yangMillsGate3GenuineFirstMissingNextIterationStrictPromotionFalse =
  refl

yangMillsGate3GenuineFirstMissingNextIterationNonFlatBlockerIsExact :
  YMSFGCGate3GenuineFirstMissingNextIterationTypedResidualReceipt.firstStrictCurvatureBlocker
    canonicalYMSFGCGate3GenuineFirstMissingNextIterationTypedResidualReceipt
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsGate3GenuineFirstMissingNextIterationNonFlatBlockerIsExact =
  refl

yangMillsGate3GenuineFirstMissingNextIterationLieBlockerIsExact :
  YMSFGCGate3GenuineFirstMissingNextIterationTypedResidualReceipt.firstStrictSelectedLieBlocker
    canonicalYMSFGCGate3GenuineFirstMissingNextIterationTypedResidualReceipt
  ≡
  missingLieAlgebraCarrierForSelectedFiniteGaugeSector
yangMillsGate3GenuineFirstMissingNextIterationLieBlockerIsExact =
  refl

------------------------------------------------------------------------
-- lower6 YM/u1/u2/m1/m2/l6 current-wave finite attempts.
--
-- The lower6 wave asks this worker to coordinate with the GR doubled
-- Christoffel route only if a YM-owned hook exists.  The selected metric and
-- Christoffel API lives in the GR files, not in this YM obstruction module, so
-- the receipt below records only the integral arithmetic shape and keeps the
-- hook/promoted flags false.  The Yang-Mills-local parts consume the existing
-- finite Lie3, reference Wilson-loop, D_A^2, and epsilon-contraction witnesses.

data YMSFGCFiniteFourIndex : Set where
  ymFin0 ymFin1 ymFin2 ymFin3 : YMSFGCFiniteFourIndex

ymChristoffelTwoTimesProbe :
  YMSFGCFiniteFourIndex →
  YMSFGCFiniteFourIndex →
  YMSFGCFiniteFourIndex →
  ℤ
ymChristoffelTwoTimesProbe _ _ _ =
  + 0

ymDoubledMetricCompatibilityProbe :
  YMSFGCFiniteFourIndex →
  YMSFGCFiniteFourIndex →
  YMSFGCFiniteFourIndex →
  ℤ
ymDoubledMetricCompatibilityProbe _ _ _ =
  + 0

ymDoubledMetricCompatibilityProbeIsZero :
  (lambda mu nu : YMSFGCFiniteFourIndex) →
  ymDoubledMetricCompatibilityProbe lambda mu nu
  ≡
  + 0
ymDoubledMetricCompatibilityProbeIsZero _ _ _ =
  refl

data YMSFGCCurrentWaveChristoffelCoordinationStatus : Set where
  currentWaveChristoffelCoordinationArithmeticShapeOnly :
    YMSFGCCurrentWaveChristoffelCoordinationStatus

record YMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt : Set₁ where
  field
    status :
      YMSFGCCurrentWaveChristoffelCoordinationStatus

    finiteIndexCarrier :
      Set

    finiteIndexCarrierIsFourPoint :
      finiteIndexCarrier
      ≡
      YMSFGCFiniteFourIndex

    twoTimesChristoffelProbe :
      YMSFGCFiniteFourIndex →
      YMSFGCFiniteFourIndex →
      YMSFGCFiniteFourIndex →
      ℤ

    twoTimesChristoffelProbeIsIntegral :
      twoTimesChristoffelProbe
      ≡
      ymChristoffelTwoTimesProbe

    doubledMetricCompatibilityProbe :
      YMSFGCFiniteFourIndex →
      YMSFGCFiniteFourIndex →
      YMSFGCFiniteFourIndex →
      ℤ

    doubledMetricCompatibilityProbeIsCanonical :
      doubledMetricCompatibilityProbe
      ≡
      ymDoubledMetricCompatibilityProbe

    doubledMetricCompatibilityProbeZero :
      (lambda mu nu : YMSFGCFiniteFourIndex) →
      doubledMetricCompatibilityProbe lambda mu nu
      ≡
      + 0

    doubledMetricCompatibilityProbeZeroThreaded :
      Bool

    doubledMetricCompatibilityProbeZeroThreadedIsTrue :
      doubledMetricCompatibilityProbeZeroThreaded ≡ true

    selectedGRMetricHookAvailableInYMFile :
      Bool

    selectedGRMetricHookAvailableInYMFileIsFalse :
      selectedGRMetricHookAvailableInYMFile ≡ false

    strictMetricCompatibilityPromotedFromYM :
      Bool

    strictMetricCompatibilityPromotedFromYMIsFalse :
      strictMetricCompatibilityPromotedFromYM ≡ false

    coordinationBoundary :
      List String

canonicalYMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt :
  YMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt
canonicalYMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt =
  record
    { status =
        currentWaveChristoffelCoordinationArithmeticShapeOnly
    ; finiteIndexCarrier =
        YMSFGCFiniteFourIndex
    ; finiteIndexCarrierIsFourPoint =
        refl
    ; twoTimesChristoffelProbe =
        ymChristoffelTwoTimesProbe
    ; twoTimesChristoffelProbeIsIntegral =
        refl
    ; doubledMetricCompatibilityProbe =
        ymDoubledMetricCompatibilityProbe
    ; doubledMetricCompatibilityProbeIsCanonical =
        refl
    ; doubledMetricCompatibilityProbeZero =
        λ _ _ _ → refl
    ; doubledMetricCompatibilityProbeZeroThreaded =
        true
    ; doubledMetricCompatibilityProbeZeroThreadedIsTrue =
        refl
    ; selectedGRMetricHookAvailableInYMFile =
        false
    ; selectedGRMetricHookAvailableInYMFileIsFalse =
        refl
    ; strictMetricCompatibilityPromotedFromYM =
        false
    ; strictMetricCompatibilityPromotedFromYMIsFalse =
        refl
    ; coordinationBoundary =
        "u1 coordination: YM records the 2*Christoffel integral arithmetic shape on a local four-index probe"
        ∷ "The selected GR metric/Christoffel hook is not owned by the YM files, so no GR metric-compatibility theorem is promoted here"
        ∷ "The GR r1 odd-numerator problem remains a GR-side doubled-Christoffel obligation"
        ∷ []
    }

data YMSFGCCurrentWaveFiniteDACurvatureStatus : Set where
  currentWaveFiniteDASquaredComputationInhabitedLocally :
    YMSFGCCurrentWaveFiniteDACurvatureStatus

record YMSFGCCurrentWaveFiniteDACurvatureComputationReceipt : Set₁ where
  field
    status :
      YMSFGCCurrentWaveFiniteDACurvatureStatus

    finiteDAFormula :
      (A : SFGC.GaugeField) →
      (section : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3DA0Form A (lieValued0 section)
      ≡
      localFiniteLie3DAExpectedRHS0Form A section

    finiteDAFormulaIsCanonical :
      finiteDAFormula
      ≡
      localFiniteLie3DAFormulaOn0Forms

    finiteDASquaredBracketAction :
      (A : SFGC.GaugeField) →
      (section : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3DA0Form
        A
        (localFiniteLie3DA0Form A (lieValued0 section))
      ≡
      localFiniteLie3CurvatureBracketActionOn0Form
        (localFiniteLie3FA2Form A)
        (lieValued0 section)

    finiteDASquaredBracketActionIsCanonical :
      finiteDASquaredBracketAction
      ≡
      localFiniteLie3DASquaredEqualsBracketFAOn0Forms

    discreteRicciIdentityPromotedToRealCarrier :
      Bool

    discreteRicciIdentityPromotedToRealCarrierIsFalse :
      discreteRicciIdentityPromotedToRealCarrier ≡ false

    exactTransportBlocker :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    exactTransportBlockerIsFieldStrengthAction :
      exactTransportBlocker
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    computationBoundary :
      List String

canonicalYMSFGCCurrentWaveFiniteDACurvatureComputationReceipt :
  YMSFGCCurrentWaveFiniteDACurvatureComputationReceipt
canonicalYMSFGCCurrentWaveFiniteDACurvatureComputationReceipt =
  record
    { status =
        currentWaveFiniteDASquaredComputationInhabitedLocally
    ; finiteDAFormula =
        localFiniteLie3DAFormulaOn0Forms
    ; finiteDAFormulaIsCanonical =
        refl
    ; finiteDASquaredBracketAction =
        localFiniteLie3DASquaredEqualsBracketFAOn0Forms
    ; finiteDASquaredBracketActionIsCanonical =
        refl
    ; discreteRicciIdentityPromotedToRealCarrier =
        false
    ; discreteRicciIdentityPromotedToRealCarrierIsFalse =
        refl
    ; exactTransportBlocker =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; exactTransportBlockerIsFieldStrengthAction =
        refl
    ; computationBoundary =
        "u2 finite computation: localFiniteLie3DAFormulaOn0Forms and localFiniteLie3DASquaredEqualsBracketFAOn0Forms inhabit the finite D_A^2=[F_A,_] surface"
        ∷ "This is not a real SU3 fibre transport theorem; field-strength transport on the selected gauge bundle remains missing"
        ∷ []
    }

data YMSFGCCurrentWaveFiniteAdditiveWilsonStatus : Set where
  currentWaveFiniteAdditiveWilsonLoopWitnessInhabited :
    YMSFGCCurrentWaveFiniteAdditiveWilsonStatus

record YMSFGCCurrentWaveFiniteAdditiveWilsonLoopReceipt : Set₁ where
  field
    status :
      YMSFGCCurrentWaveFiniteAdditiveWilsonStatus

    additiveLieCarrier :
      Set

    additiveLieCarrierIsLocalFiniteLie3 :
      additiveLieCarrier
      ≡
      YMSFGCLocalFiniteLie3Carrier

    additiveBracket :
      YMSFGCLocalFiniteLie3Carrier →
      YMSFGCLocalFiniteLie3Carrier →
      YMSFGCLocalFiniteLie3Carrier

    additiveBracketIsCrossProduct :
      additiveBracket
      ≡
      localFiniteLie3Bracket

    additiveBracketAntisymmetry :
      (x y : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3Bracket x y
      ≡
      localFiniteLie3Neg (localFiniteLie3Bracket y x)

    additiveBracketJacobi :
      (x y z : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3JacobiAdd
        (localFiniteLie3JacobiAdd
          (localFiniteLie3Bracket x (localFiniteLie3Bracket y z))
          (localFiniteLie3Bracket y (localFiniteLie3Bracket z x)))
        (localFiniteLie3Bracket z (localFiniteLie3Bracket x y))
      ≡
      lieZero

    referencePlaquetteCurvatureIsQuarterTurn :
      SFGC.sfgcSite2DEvaluate2
        sfgcReferenceNonFlatCurvature2Form
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    referencePlaquetteCurvatureNotVacuum :
      SFGC.sfgcSite2DEvaluate2
        sfgcReferenceNonFlatCurvature2Form
        sfgcReferencePlaquette
      ≡
      SPTI4.φ0 →
      YMSFGCEmpty

    strictNonFlatCurvaturePromoted :
      Bool

    strictNonFlatCurvaturePromotedIsFalse :
      strictNonFlatCurvaturePromoted ≡ false

    exactNonFlatCurvatureBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    exactNonFlatCurvatureBlockerIsMissing :
      exactNonFlatCurvatureBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    additiveBoundary :
      List String

canonicalYMSFGCCurrentWaveFiniteAdditiveWilsonLoopReceipt :
  YMSFGCCurrentWaveFiniteAdditiveWilsonLoopReceipt
canonicalYMSFGCCurrentWaveFiniteAdditiveWilsonLoopReceipt =
  record
    { status =
        currentWaveFiniteAdditiveWilsonLoopWitnessInhabited
    ; additiveLieCarrier =
        YMSFGCLocalFiniteLie3Carrier
    ; additiveLieCarrierIsLocalFiniteLie3 =
        refl
    ; additiveBracket =
        localFiniteLie3Bracket
    ; additiveBracketIsCrossProduct =
        refl
    ; additiveBracketAntisymmetry =
        localFiniteLie3BracketAntisymmetry
    ; additiveBracketJacobi =
        localFiniteLie3JacobiWitness
    ; referencePlaquetteCurvatureIsQuarterTurn =
        sfgcReferenceNonFlatCurvatureAtReference
    ; referencePlaquetteCurvatureNotVacuum =
        sfgcReferenceNonFlatCurvatureAtReferenceNotVacuum
    ; strictNonFlatCurvaturePromoted =
        false
    ; strictNonFlatCurvaturePromotedIsFalse =
        refl
    ; exactNonFlatCurvatureBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; exactNonFlatCurvatureBlockerIsMissing =
        refl
    ; additiveBoundary =
        "m1 finite additive interpretation: local Lie3 cross-product arithmetic and the reference Wilson-loop φ1 witness are inhabited"
        ∷ "The witness remains finite Phase4/SFGCSite2D data and is not promoted to the strict user-supplied real non-flat curvature carrier"
        ∷ []
    }

data YMSFGCCurrentWaveHodgeEpsilonAssistanceStatus : Set where
  currentWaveHodgeEpsilonAssistanceFiniteOnly :
    YMSFGCCurrentWaveHodgeEpsilonAssistanceStatus

record YMSFGCCurrentWaveHodgeEpsilonAssistanceReceipt : Set₁ where
  field
    status :
      YMSFGCCurrentWaveHodgeEpsilonAssistanceStatus

    finiteEpsilonContractionShape :
      Set

    finiteEpsilonContractionShapeIsLocalLie3 :
      finiteEpsilonContractionShape
      ≡
      localFiniteLie3EpsilonContractionShape

    finiteEpsilonContractionWitness :
      localFiniteLie3EpsilonContractionShape

    selectedHodgeProbe :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    selectedHodgeProbeIsIdentity :
      selectedHodgeProbe
      ≡
      sfgcSelectedHodgeStarLowerCandidate

    exactVariationBlocker :
      YangMillsVariationalEquationMissingPrimitive

    exactVariationBlockerIsVariationPairing :
      exactVariationBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    metricHodgePromoted :
      Bool

    metricHodgePromotedIsFalse :
      metricHodgePromoted ≡ false

    hodgeBoundary :
      List String

canonicalYMSFGCCurrentWaveHodgeEpsilonAssistanceReceipt :
  YMSFGCCurrentWaveHodgeEpsilonAssistanceReceipt
canonicalYMSFGCCurrentWaveHodgeEpsilonAssistanceReceipt =
  record
    { status =
        currentWaveHodgeEpsilonAssistanceFiniteOnly
    ; finiteEpsilonContractionShape =
        localFiniteLie3EpsilonContractionShape
    ; finiteEpsilonContractionShapeIsLocalLie3 =
        refl
    ; finiteEpsilonContractionWitness =
        localFiniteLie3PositiveAxisJacobi
    ; selectedHodgeProbe =
        sfgcSelectedHodgeStarLowerCandidate
    ; selectedHodgeProbeIsIdentity =
        refl
    ; exactVariationBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; exactVariationBlockerIsVariationPairing =
        refl
    ; metricHodgePromoted =
        false
    ; metricHodgePromotedIsFalse =
        refl
    ; hodgeBoundary =
        "m2/l6 assistance: the finite epsilon-contraction helper is the local Lie3 positive-axis Jacobi contraction"
        ∷ "The field-strength-to-dual adapter is constructed, but no SFGCSite2D metric Hodge-star law, sourced current law, or variation pairing is constructed"
        ∷ []
    }

record YMSFGCCurrentWaveYMFiniteWorkerReceipt : Set₁ where
  field
    christoffelCoordination :
      YMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt

    christoffelCoordinationIsCanonical :
      christoffelCoordination
      ≡
      canonicalYMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt

    finiteDACurvatureComputation :
      YMSFGCCurrentWaveFiniteDACurvatureComputationReceipt

    finiteDACurvatureComputationIsCanonical :
      finiteDACurvatureComputation
      ≡
      canonicalYMSFGCCurrentWaveFiniteDACurvatureComputationReceipt

    finiteAdditiveWilsonLoop :
      YMSFGCCurrentWaveFiniteAdditiveWilsonLoopReceipt

    finiteAdditiveWilsonLoopIsCanonical :
      finiteAdditiveWilsonLoop
      ≡
      canonicalYMSFGCCurrentWaveFiniteAdditiveWilsonLoopReceipt

    hodgeEpsilonAssistance :
      YMSFGCCurrentWaveHodgeEpsilonAssistanceReceipt

    hodgeEpsilonAssistanceIsCanonical :
      hodgeEpsilonAssistance
      ≡
      canonicalYMSFGCCurrentWaveHodgeEpsilonAssistanceReceipt

    strictRealYMCarrierPromoted :
      Bool

    strictRealYMCarrierPromotedIsFalse :
      strictRealYMCarrierPromoted ≡ false

    workerBoundary :
      List String

canonicalYMSFGCCurrentWaveYMFiniteWorkerReceipt :
  YMSFGCCurrentWaveYMFiniteWorkerReceipt
canonicalYMSFGCCurrentWaveYMFiniteWorkerReceipt =
  record
    { christoffelCoordination =
        canonicalYMSFGCCurrentWaveDoubledChristoffelCoordinationReceipt
    ; christoffelCoordinationIsCanonical =
        refl
    ; finiteDACurvatureComputation =
        canonicalYMSFGCCurrentWaveFiniteDACurvatureComputationReceipt
    ; finiteDACurvatureComputationIsCanonical =
        refl
    ; finiteAdditiveWilsonLoop =
        canonicalYMSFGCCurrentWaveFiniteAdditiveWilsonLoopReceipt
    ; finiteAdditiveWilsonLoopIsCanonical =
        refl
    ; hodgeEpsilonAssistance =
        canonicalYMSFGCCurrentWaveHodgeEpsilonAssistanceReceipt
    ; hodgeEpsilonAssistanceIsCanonical =
        refl
    ; strictRealYMCarrierPromoted =
        false
    ; strictRealYMCarrierPromotedIsFalse =
        refl
    ; workerBoundary =
        "current lower6 YM worker completed all locally available finite arithmetic: doubled-Christoffel coordination shape, local finite D_A^2, additive Wilson-loop φ1, and finite epsilon assistance"
        ∷ "Strict real Yang-Mills carriers and selected metric/Hodge/transport bridges remain fail-closed"
        ∷ []
    }

yangMillsCurrentWaveYMFiniteWorkerStrictPromotionFalse :
  YMSFGCCurrentWaveYMFiniteWorkerReceipt.strictRealYMCarrierPromoted
    canonicalYMSFGCCurrentWaveYMFiniteWorkerReceipt
  ≡
  false
yangMillsCurrentWaveYMFiniteWorkerStrictPromotionFalse =
  refl

------------------------------------------------------------------------
-- Gate 3 YM latest first-missing concrete attempts.
--
-- This receipt consumes only terms already available in this module.  It
-- keeps the strict non-flat curvature blocker explicit: the finite Site2D
-- Wilson-loop probe is inhabited and the SFGC 1-form now adapts into the
-- user-supplied non-flat connection carrier; the strict holonomy, transport,
-- and variation laws are still fail-closed.

u2ParametrizedConnectionOneFormProbe :
  YMSFGCLocalFiniteLie3Carrier →
  SFGC.GaugeField →
  YMSFGCLieValued1Form
u2ParametrizedConnectionOneFormProbe parameter A =
  lieValued1 parameter

u2ParametrizedDA0FormProbe :
  YMSFGCLocalFiniteLie3Carrier →
  SFGC.GaugeField →
  YMSFGCLieValued0Form →
  YMSFGCLieValued0Form
u2ParametrizedDA0FormProbe parameter A (lieValued0 section) =
  lieValued0
    (localFiniteLie3JacobiAdd
      lieZero
      (localFiniteLie3Bracket parameter section))

u2ParametrizedDAExpectedRHS0FormProbe :
  YMSFGCLocalFiniteLie3Carrier →
  YMSFGCLocalFiniteLie3Carrier →
  YMSFGCLieValued0Form
u2ParametrizedDAExpectedRHS0FormProbe parameter section =
  lieValued0
    (localFiniteLie3JacobiAdd
      lieZero
      (localFiniteLie3Bracket parameter section))

u2ParametrizedDAFormulaProbe :
  (parameter : YMSFGCLocalFiniteLie3Carrier) →
  (A : SFGC.GaugeField) →
  (section : YMSFGCLocalFiniteLie3Carrier) →
  u2ParametrizedDA0FormProbe parameter A (lieValued0 section)
  ≡
  u2ParametrizedDAExpectedRHS0FormProbe parameter section
u2ParametrizedDAFormulaProbe parameter A section =
  refl

u2ParametrizedDASquaredProbe :
  YMSFGCLocalFiniteLie3Carrier →
  SFGC.GaugeField →
  YMSFGCLieValued0Form →
  YMSFGCLieValued0Form
u2ParametrizedDASquaredProbe parameter A section =
  u2ParametrizedDA0FormProbe
    parameter
    A
    (u2ParametrizedDA0FormProbe parameter A section)

u2ParametrizedDASquaredHandoffProbe :
  (parameter : YMSFGCLocalFiniteLie3Carrier) →
  (A : SFGC.GaugeField) →
  (section : YMSFGCLocalFiniteLie3Carrier) →
  u2ParametrizedDASquaredProbe parameter A (lieValued0 section)
  ≡
  u2ParametrizedDA0FormProbe
    parameter
    A
    (u2ParametrizedDA0FormProbe parameter A (lieValued0 section))
u2ParametrizedDASquaredHandoffProbe parameter A section =
  refl

data YMSFGCLatestFirstMissingAttemptStatus : Set where
  latestFirstMissingConcreteFiniteTermsFailClosed :
    YMSFGCLatestFirstMissingAttemptStatus

record YMSFGCLatestFirstMissingConcreteAttemptReceipt : Set₁ where
  field
    status :
      YMSFGCLatestFirstMissingAttemptStatus

    additiveSU2LikeCarrier :
      Set

    additiveSU2LikeCarrierIsLocalFiniteLie3 :
      additiveSU2LikeCarrier
      ≡
      YMSFGCLocalFiniteLie3Carrier

    additiveSU2LikeAlgebra :
      YMSFGCLocalFiniteSU2LieAlgebra

    additiveSU2LikeAlgebraIsCanonical :
      additiveSU2LikeAlgebra
      ≡
      canonicalYMSFGCLocalFiniteSU2LieAlgebra

    additiveSU2XYBracket :
      localFiniteLie3Bracket
        (lieBasis signPos axisX)
        (lieBasis signPos axisY)
      ≡
      lieBasis signPos axisZ

    additiveSU2JacobiWitness :
      (x y z : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3JacobiAdd
        (localFiniteLie3JacobiAdd
          (localFiniteLie3Bracket x (localFiniteLie3Bracket y z))
          (localFiniteLie3Bracket y (localFiniteLie3Bracket z x)))
        (localFiniteLie3Bracket z (localFiniteLie3Bracket x y))
      ≡
      lieZero

    referenceNonFlatWilsonCurvature :
      SFGC.SFGCSite2DDiscrete2Form

    referenceNonFlatWilsonCurvatureIsCanonical :
      referenceNonFlatWilsonCurvature
      ≡
      sfgcReferenceNonFlatCurvature2Form

    referenceNonFlatWilsonCurvatureAtReference :
      SFGC.sfgcSite2DEvaluate2
        referenceNonFlatWilsonCurvature
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    referenceNonFlatWilsonCurvatureNotVacuum :
      SFGC.sfgcSite2DEvaluate2
        referenceNonFlatWilsonCurvature
        sfgcReferencePlaquette
      ≡
      SPTI4.φ0 →
      YMSFGCEmpty

    u2ConnectionParameterCarrier :
      Set

    u2ConnectionParameterCarrierIsLocalFiniteLie3 :
      u2ConnectionParameterCarrier
      ≡
      YMSFGCLocalFiniteLie3Carrier

    u2ConnectionOneFormProbe :
      YMSFGCLocalFiniteLie3Carrier →
      SFGC.GaugeField →
      YMSFGCLieValued1Form

    u2ConnectionOneFormProbeIsParametrized :
      u2ConnectionOneFormProbe
      ≡
      u2ParametrizedConnectionOneFormProbe

    u2DAFormulaProbe :
      (parameter : YMSFGCLocalFiniteLie3Carrier) →
      (A : SFGC.GaugeField) →
      (section : YMSFGCLocalFiniteLie3Carrier) →
      u2ParametrizedDA0FormProbe parameter A (lieValued0 section)
      ≡
      u2ParametrizedDAExpectedRHS0FormProbe parameter section

    u2DASquaredHandoffProbe :
      (parameter : YMSFGCLocalFiniteLie3Carrier) →
      (A : SFGC.GaugeField) →
      (section : YMSFGCLocalFiniteLie3Carrier) →
      u2ParametrizedDASquaredProbe parameter A (lieValued0 section)
      ≡
      u2ParametrizedDA0FormProbe
        parameter
        A
        (u2ParametrizedDA0FormProbe parameter A (lieValued0 section))

    m2EpsilonCurrentShape :
      Set

    m2EpsilonCurrentShapeIsLocalLie3 :
      m2EpsilonCurrentShape
      ≡
      localFiniteLie3EpsilonContractionShape

    m2EpsilonCurrentWitness :
      localFiniteLie3EpsilonContractionShape

    m2HodgeLowerCandidate :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    m2HodgeLowerCandidateIsIdentity :
      m2HodgeLowerCandidate
      ≡
      sfgcSelectedHodgeStarLowerCandidate

    m2RequestedCurrentCarrier :
      Set

    m2RequestedCurrentCarrierIsUserSupplied :
      m2RequestedCurrentCarrier
      ≡
      YMSFGCUserSuppliedCurrentCarrier

    strictNonFlatCurvatureBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    strictNonFlatCurvatureBlockerIsExact :
      strictNonFlatCurvatureBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    strictU2TransportBlocker :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    strictU2TransportBlockerIsFieldStrengthAction :
      strictU2TransportBlocker
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    strictM2CurrentBlocker :
      YangMillsFieldEquationMissingPrerequisite

    strictM2CurrentBlockerIsCurrentSource :
      strictM2CurrentBlocker
      ≡
      missingCurrentSourceAndCoupling

    strictM2VariationBlocker :
      YangMillsVariationalEquationMissingPrimitive

    strictM2VariationBlockerIsVariationPairing :
      strictM2VariationBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    exactMissingConstructorOrAPI :
      List String

    strictPromotion :
      Bool

    strictPromotionIsFalse :
      strictPromotion ≡ false

    receiptBoundary :
      List String

canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt :
  YMSFGCLatestFirstMissingConcreteAttemptReceipt
canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt =
  record
    { status =
        latestFirstMissingConcreteFiniteTermsFailClosed
    ; additiveSU2LikeCarrier =
        YMSFGCLocalFiniteLie3Carrier
    ; additiveSU2LikeCarrierIsLocalFiniteLie3 =
        refl
    ; additiveSU2LikeAlgebra =
        canonicalYMSFGCLocalFiniteSU2LieAlgebra
    ; additiveSU2LikeAlgebraIsCanonical =
        refl
    ; additiveSU2XYBracket =
        localFiniteLie3BracketIsNonAbelian
    ; additiveSU2JacobiWitness =
        localFiniteLie3JacobiWitness
    ; referenceNonFlatWilsonCurvature =
        sfgcReferenceNonFlatCurvature2Form
    ; referenceNonFlatWilsonCurvatureIsCanonical =
        refl
    ; referenceNonFlatWilsonCurvatureAtReference =
        sfgcReferenceNonFlatCurvatureAtReference
    ; referenceNonFlatWilsonCurvatureNotVacuum =
        sfgcReferenceNonFlatCurvatureAtReferenceNotVacuum
    ; u2ConnectionParameterCarrier =
        YMSFGCLocalFiniteLie3Carrier
    ; u2ConnectionParameterCarrierIsLocalFiniteLie3 =
        refl
    ; u2ConnectionOneFormProbe =
        u2ParametrizedConnectionOneFormProbe
    ; u2ConnectionOneFormProbeIsParametrized =
        refl
    ; u2DAFormulaProbe =
        u2ParametrizedDAFormulaProbe
    ; u2DASquaredHandoffProbe =
        u2ParametrizedDASquaredHandoffProbe
    ; m2EpsilonCurrentShape =
        localFiniteLie3EpsilonContractionShape
    ; m2EpsilonCurrentShapeIsLocalLie3 =
        refl
    ; m2EpsilonCurrentWitness =
        localFiniteLie3PositiveAxisJacobi
    ; m2HodgeLowerCandidate =
        sfgcSelectedHodgeStarLowerCandidate
    ; m2HodgeLowerCandidateIsIdentity =
        refl
    ; m2RequestedCurrentCarrier =
        YMSFGCUserSuppliedCurrentCarrier
    ; m2RequestedCurrentCarrierIsUserSupplied =
        refl
    ; strictNonFlatCurvatureBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; strictNonFlatCurvatureBlockerIsExact =
        refl
    ; strictU2TransportBlocker =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; strictU2TransportBlockerIsFieldStrengthAction =
        refl
    ; strictM2CurrentBlocker =
        missingCurrentSourceAndCoupling
    ; strictM2CurrentBlockerIsCurrentSource =
        refl
    ; strictM2VariationBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; strictM2VariationBlockerIsVariationPairing =
        refl
    ; exactMissingConstructorOrAPI =
        "Finite constructor inhabits YMSFGCUserSuppliedNonFlatConnectionCarrier from SFGCSite2DDiscrete1Form plus a curvature projection"
        ∷ "Bridge supplied: SFGC.SFGCSite2DDiscrete1Form -> YMSFGCUserSuppliedNonFlatConnectionCarrier"
        ∷ "Strict API supplied as projection: connectionCurvature : YMSFGCUserSuppliedNonFlatConnectionCarrier -> SFGC.SFGCSite2DPlaquette -> SFGC.SFGCSite2DFieldStrengthBridge"
        ∷ "The strict missingNonFlatSFGCSite2DConnectionCurvature blocker is still not closed because it is an irreducibility token, not a record target"
        ∷ "Missing u2 transport API: field-strength fibre action/covariant transport on the selected SFGCSite2D gauge bundle"
        ∷ "m2 finite bridge supplied: SFGC.SFGCSite2DFieldStrengthBridge -> YMSFGCUserSuppliedDualCurvatureCarrier"
        ∷ "Missing m2 source API: currentSource coupled to D * F = J over YMSFGCUserSuppliedCurrentCarrier"
        ∷ "Missing variational API: selected Hodge-star/action variation pairing"
        ∷ []
    ; strictPromotion =
        false
    ; strictPromotionIsFalse =
        refl
    ; receiptBoundary =
        "Additive su2-like route: the local finite Lie3/SU2-like bracket, XY=Z witness, and Jacobi witness are inhabited"
        ∷ "Non-flat Wilson-loop attempt: the reference SFGCSite2D arbitrary 1-form has plaquette curvature phi1 and a phi1-not-phi0 witness"
        ∷ "u2 handoff: a parametrized local connection-one-form probe, D_A formula probe, and D_A squared handoff probe are inhabited only on the local finite carrier"
        ∷ "m2 handoff: finite epsilon contraction, identity Hodge lower candidate, dual-curvature adapter, and current carrier adapter are inhabited; sourced D * F = J and variation laws remain absent"
        ∷ "Fail-closed: exact strict blockers remain non-flat connection curvature, selected field-strength transport, current coupling, and selected Hodge variation pairing"
        ∷ []
    }

yangMillsLatestFirstMissingConcreteAttemptNonPromoting :
  YMSFGCLatestFirstMissingConcreteAttemptReceipt.strictPromotion
    canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt
  ≡
  false
yangMillsLatestFirstMissingConcreteAttemptNonPromoting =
  refl

yangMillsLatestFirstMissingConcreteAttemptNonFlatBlockerIsExact :
  YMSFGCLatestFirstMissingConcreteAttemptReceipt.strictNonFlatCurvatureBlocker
    canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsLatestFirstMissingConcreteAttemptNonFlatBlockerIsExact =
  refl

data YMSFGCGate3DownstreamHodgeVariationIBPStatus : Set where
  gate3DownstreamHodgeVariationIBPGatedByNonFlatCurvature :
    YMSFGCGate3DownstreamHodgeVariationIBPStatus

record YMSFGCGate3DownstreamHodgeVariationIBPReceipt : Set₁ where
  field
    status :
      YMSFGCGate3DownstreamHodgeVariationIBPStatus

    activationCurvatureBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    activationCurvatureBlockerIsNonFlatSFGCSite2DConnectionCurvature :
      activationCurvatureBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    receiptActiveNow :
      Bool

    receiptActiveNowIsFalse :
      receiptActiveNow ≡ false

    receiptBecomesActiveAfterCurvatureClosure :
      Bool

    receiptBecomesActiveAfterCurvatureClosureIsTrue :
      receiptBecomesActiveAfterCurvatureClosure ≡ true

    consumedLatestFirstMissingAttempt :
      YMSFGCLatestFirstMissingConcreteAttemptReceipt

    consumedLatestFirstMissingAttemptIsCanonical :
      consumedLatestFirstMissingAttempt
      ≡
      canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt

    consumedCurrentWaveHodgeEpsilon :
      YMSFGCCurrentWaveHodgeEpsilonAssistanceReceipt

    consumedCurrentWaveHodgeEpsilonIsCanonical :
      consumedCurrentWaveHodgeEpsilon
      ≡
      canonicalYMSFGCCurrentWaveHodgeEpsilonAssistanceReceipt

    consumedNextWaveHodgeEpsilon :
      YMSFGCNextWaveHodgeEpsilonContractionAssistanceReceipt

    consumedNextWaveHodgeEpsilonIsCanonical :
      consumedNextWaveHodgeEpsilon
      ≡
      canonicalYMSFGCNextWaveHodgeEpsilonContractionAssistanceReceipt

    consumedDiscreteBianchiReceipt :
      Bianchi.DiscreteBianchiIdentityReceipt

    consumedDiscreteBianchiReceiptIsCanonical :
      consumedDiscreteBianchiReceipt
      ≡
      Bianchi.canonicalDiscreteBianchiIdentityReceipt

    consumedDiscreteStokesObstruction :
      StokesObs.DiscreteStokesBianchiObstruction

    consumedDiscreteStokesObstructionIsCanonical :
      consumedDiscreteStokesObstruction
      ≡
      StokesObs.canonicalDiscreteStokesBianchiObstruction

    stokesBoundaryOfBoundaryWord :
      List StokesObs.CRTMonodromy1Edge

    stokesBoundaryOfBoundaryWordIsEmpty :
      stokesBoundaryOfBoundaryWord ≡ []

    stokesBoundaryOfBoundaryAction :
      StokesObs.CRTBoundaryWordAction

    stokesBoundaryOfBoundaryActionIsIdentity :
      stokesBoundaryOfBoundaryAction
      ≡
      StokesObs.identityCRTBoundaryWordAction

    selectedHodgeLowerCandidate :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    selectedHodgeLowerCandidateIsIdentityProbe :
      selectedHodgeLowerCandidate
      ≡
      sfgcSelectedHodgeStarLowerCandidate

    zeroVariationIBPLowerCandidate :
      YMSFGCDiscreteVariationIBPLowerCandidate

    zeroVariationIBPLowerCandidateIsCanonical :
      zeroVariationIBPLowerCandidate
      ≡
      canonicalYMSFGCDiscreteVariationIBPLowerCandidate

    zeroVariationIBPLaw :
      (A δA : SFGC.GaugeField) →
      sfgcZeroVariationOfAction A δA
        ≡
      _+ℤ_
        (sfgcZeroEulerLagrangePairing A δA)
        (sfgcZeroBoundaryTerm A δA)

    requiredStrictHodgeStarType :
      Set

    requiredStrictHodgeStarTypeIsSelectedFieldStrengthToDual :
      requiredStrictHodgeStarType
      ≡
      (SFGC.SFGCSite2DFieldStrengthBridge →
       YMSFGCUserSuppliedDualCurvatureCarrier)

    requiredStrictDualCurvatureBridgeType :
      Set

    requiredStrictDualCurvatureBridgeTypeIsFieldStrengthToDual :
      requiredStrictDualCurvatureBridgeType
      ≡
      (SFGC.SFGCSite2DFieldStrengthBridge →
       YMSFGCUserSuppliedDualCurvatureCarrier)

    requiredStrictCurrentSourceType :
      Set

    requiredStrictCurrentSourceTypeIsConnectionToCurrent :
      requiredStrictCurrentSourceType
      ≡
      (YMSFGCUserSuppliedNonFlatConnectionCarrier →
       YMSFGCUserSuppliedCurrentCarrier)

    requiredStrictVariationPairingType :
      Set

    requiredStrictVariationPairingTypeIsConnectionVariationToActionScalar :
      requiredStrictVariationPairingType
      ≡
      (YMSFGCUserSuppliedNonFlatConnectionCarrier →
       YMSFGCUserSuppliedVariationCarrier →
       YMSFGCUserSuppliedActionScalarCarrier)

    requiredStrictDiscreteIBPType :
      Set

    requiredStrictDiscreteIBPTypeIsUserSuppliedRequest :
      requiredStrictDiscreteIBPType
      ≡
      YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedDiscreteIBPLawType
        canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    exactCurrentBlocker :
      YangMillsFieldEquationMissingPrerequisite

    exactCurrentBlockerIsCurrentSourceAndCoupling :
      exactCurrentBlocker
      ≡
      missingCurrentSourceAndCoupling

    exactVariationPairingBlocker :
      YangMillsVariationalEquationMissingPrimitive

    exactVariationPairingBlockerIsMissingVariationPairing :
      exactVariationPairingBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    finiteHodgePromotedToStrictDualCurvature :
      Bool

    finiteHodgePromotedToStrictDualCurvatureIsFalse :
      finiteHodgePromotedToStrictDualCurvature ≡ false

    variationPairingPromoted :
      Bool

    variationPairingPromotedIsFalse :
      variationPairingPromoted ≡ false

    downstreamIBPPromoted :
      Bool

    downstreamIBPPromotedIsFalse :
      downstreamIBPPromoted ≡ false

    exactBlockersAfterCurvatureClosure :
      List String

    receiptBoundary :
      List String

canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt :
  YMSFGCGate3DownstreamHodgeVariationIBPReceipt
canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt =
  record
    { status =
        gate3DownstreamHodgeVariationIBPGatedByNonFlatCurvature
    ; activationCurvatureBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; activationCurvatureBlockerIsNonFlatSFGCSite2DConnectionCurvature =
        refl
    ; receiptActiveNow =
        false
    ; receiptActiveNowIsFalse =
        refl
    ; receiptBecomesActiveAfterCurvatureClosure =
        true
    ; receiptBecomesActiveAfterCurvatureClosureIsTrue =
        refl
    ; consumedLatestFirstMissingAttempt =
        canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt
    ; consumedLatestFirstMissingAttemptIsCanonical =
        refl
    ; consumedCurrentWaveHodgeEpsilon =
        canonicalYMSFGCCurrentWaveHodgeEpsilonAssistanceReceipt
    ; consumedCurrentWaveHodgeEpsilonIsCanonical =
        refl
    ; consumedNextWaveHodgeEpsilon =
        canonicalYMSFGCNextWaveHodgeEpsilonContractionAssistanceReceipt
    ; consumedNextWaveHodgeEpsilonIsCanonical =
        refl
    ; consumedDiscreteBianchiReceipt =
        Bianchi.canonicalDiscreteBianchiIdentityReceipt
    ; consumedDiscreteBianchiReceiptIsCanonical =
        refl
    ; consumedDiscreteStokesObstruction =
        StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; consumedDiscreteStokesObstructionIsCanonical =
        refl
    ; stokesBoundaryOfBoundaryWord =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryOfBoundaryWord
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; stokesBoundaryOfBoundaryWordIsEmpty =
        refl
    ; stokesBoundaryOfBoundaryAction =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryOfBoundaryAction
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; stokesBoundaryOfBoundaryActionIsIdentity =
        refl
    ; selectedHodgeLowerCandidate =
        sfgcSelectedHodgeStarLowerCandidate
    ; selectedHodgeLowerCandidateIsIdentityProbe =
        refl
    ; zeroVariationIBPLowerCandidate =
        canonicalYMSFGCDiscreteVariationIBPLowerCandidate
    ; zeroVariationIBPLowerCandidateIsCanonical =
        refl
    ; zeroVariationIBPLaw =
        sfgcZeroDiscreteVariationIBPLaw
    ; requiredStrictHodgeStarType =
        SFGC.SFGCSite2DFieldStrengthBridge →
        YMSFGCUserSuppliedDualCurvatureCarrier
    ; requiredStrictHodgeStarTypeIsSelectedFieldStrengthToDual =
        refl
    ; requiredStrictDualCurvatureBridgeType =
        SFGC.SFGCSite2DFieldStrengthBridge →
        YMSFGCUserSuppliedDualCurvatureCarrier
    ; requiredStrictDualCurvatureBridgeTypeIsFieldStrengthToDual =
        refl
    ; requiredStrictCurrentSourceType =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMSFGCUserSuppliedCurrentCarrier
    ; requiredStrictCurrentSourceTypeIsConnectionToCurrent =
        refl
    ; requiredStrictVariationPairingType =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMSFGCUserSuppliedVariationCarrier →
        YMSFGCUserSuppliedActionScalarCarrier
    ; requiredStrictVariationPairingTypeIsConnectionVariationToActionScalar =
        refl
    ; requiredStrictDiscreteIBPType =
        YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedDiscreteIBPLawType
          canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; requiredStrictDiscreteIBPTypeIsUserSuppliedRequest =
        refl
    ; exactCurrentBlocker =
        missingCurrentSourceAndCoupling
    ; exactCurrentBlockerIsCurrentSourceAndCoupling =
        refl
    ; exactVariationPairingBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; exactVariationPairingBlockerIsMissingVariationPairing =
        refl
    ; finiteHodgePromotedToStrictDualCurvature =
        false
    ; finiteHodgePromotedToStrictDualCurvatureIsFalse =
        refl
    ; variationPairingPromoted =
        false
    ; variationPairingPromotedIsFalse =
        refl
    ; downstreamIBPPromoted =
        false
    ; downstreamIBPPromotedIsFalse =
        refl
    ; exactBlockersAfterCurvatureClosure =
        "After missingNonFlatSFGCSite2DConnectionCurvature closes, the downstream Hodge/variation route still needs a strict Hodge-star law compatible with the supplied field-strength-to-dual adapter"
        ∷ "After curvature closure, the dual-curvature carrier adapter is available, but a selected covariant derivative on dual curvature is still not promoted"
        ∷ "After curvature closure, it still needs a currentSource law : YMSFGCUserSuppliedNonFlatConnectionCarrier -> YMSFGCUserSuppliedCurrentCarrier coupled to D * F = J"
        ∷ "After curvature closure, it still needs a selected action variation pairing over YMSFGCUserSuppliedVariationCarrier and YMSFGCUserSuppliedActionScalarCarrier"
        ∷ "The only discrete IBP inhabitant consumed here is the zero proxy law over GaugeField and integer zero terms"
        ∷ "missingVariationPairingForSelectedHodgeStar remains exact and unpromoted"
        ∷ []
    ; receiptBoundary =
        "Downstream Gate 3 Hodge variation/IBP receipt is staged but inactive while missingNonFlatSFGCSite2DConnectionCurvature is the first strict blocker"
        ∷ "Consumed finite Hodge/epsilon evidence: current-wave and next-wave Hodge epsilon assistance receipts plus the identity selected Hodge lower candidate"
        ∷ "Consumed Stokes-like evidence: canonical discrete Stokes/Bianchi obstruction has empty boundary-of-boundary word and identity boundary action"
        ∷ "Consumed IBP evidence: zero variation equals zero Euler-Lagrange pairing plus zero boundary term"
        ∷ "Finite current and dual-curvature carrier adapters are inhabited, but no Hodge-star, action-variation, or sourced D * F = J law is inhabited here"
        ∷ "No Yang-Mills, Maxwell, spectral-gap, continuum-Clay, or terminal promotion is introduced"
        ∷ []
    }

yangMillsGate3DownstreamHodgeVariationIBPInactiveUntilCurvatureClosure :
  YMSFGCGate3DownstreamHodgeVariationIBPReceipt.receiptActiveNow
    canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt
  ≡
  false
yangMillsGate3DownstreamHodgeVariationIBPInactiveUntilCurvatureClosure =
  refl

yangMillsGate3DownstreamHodgeVariationIBPVariationPairingUnpromoted :
  YMSFGCGate3DownstreamHodgeVariationIBPReceipt.variationPairingPromoted
    canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt
  ≡
  false
yangMillsGate3DownstreamHodgeVariationIBPVariationPairingUnpromoted =
  refl

yangMillsGate3DownstreamHodgeVariationIBPExactVariationBlocker :
  YMSFGCGate3DownstreamHodgeVariationIBPReceipt.exactVariationPairingBlocker
    canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt
  ≡
  missingVariationPairingForSelectedHodgeStar
yangMillsGate3DownstreamHodgeVariationIBPExactVariationBlocker =
  refl

------------------------------------------------------------------------
-- Middle6 m1/u2/m2 strict non-flat curvature inspection.
--
-- The current worker wave asks for a final attempt at the first-missing
-- non-flat curvature primitive.  Inspection shows that the visible
-- `missingNonFlatSFGCSite2DConnectionCurvature` symbol is a blocker token in
-- `YMSFGCNonFlatHolonomyConjugationIrreducibility`, not a record target whose
-- fields can be filled with the finite SFGC curvature witness.  The strict
-- constructible API is the user-supplied non-flat connection supply above,
-- whose connection carrier is now finitely adapted but still does not close the
-- strict holonomy/law blocker in this module.

data YMSFGCMiddle6StrictNonFlatCurvatureInspectionStatus : Set where
  middle6StrictNonFlatCurvatureFiniteBridgeAvailableStrictTokenUnclosed :
    YMSFGCMiddle6StrictNonFlatCurvatureInspectionStatus

record YMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt : Set₁ where
  field
    status :
      YMSFGCMiddle6StrictNonFlatCurvatureInspectionStatus

    inspectedBlockerSurface :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    inspectedBlockerSurfaceIsMissingNonFlatCurvature :
      inspectedBlockerSurface
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    finiteCandidateConnection :
      SFGC.SFGCSite2DDiscrete1Form

    finiteCandidateConnectionIsReference :
      finiteCandidateConnection
      ≡
      sfgcReferenceNonFlat1Form

    finiteCandidateCurvature :
      SFGC.SFGCSite2DDiscrete2Form

    finiteCandidateCurvatureIsReference :
      finiteCandidateCurvature
      ≡
      sfgcReferenceNonFlatCurvature2Form

    finiteCandidateCurvatureAtReference :
      SFGC.sfgcSite2DEvaluate2
        finiteCandidateCurvature
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    finiteCandidateCurvatureNotVacuum :
      SFGC.sfgcSite2DEvaluate2
        finiteCandidateCurvature
        sfgcReferencePlaquette
      ≡
      SPTI4.φ0 →
      YMSFGCEmpty

    finiteFieldStrengthBridge :
      SFGC.SFGCSite2DFieldStrengthBridge

    finiteFieldStrengthBridgeIsReference :
      finiteFieldStrengthBridge
      ≡
      sfgcReferenceNonFlatFieldStrengthBridge

    finiteFieldStrengthAtReference :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        finiteFieldStrengthBridge
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    finiteLowerCurvatureBridge :
      SFGC.SFGCSite2DDiscrete1Form →
      SFGC.SFGCSite2DPlaquette →
      SFGC.SFGCSite2DFieldStrengthBridge

    finiteLowerCurvatureBridgeIsDelta1 :
      finiteLowerCurvatureBridge
      ≡
      sfgcFiniteSite2D1FormCurvatureBridge

    strictConnectionCarrier :
      Set

    strictConnectionCarrierIsUserSupplied :
      strictConnectionCarrier
      ≡
      YMSFGCUserSuppliedNonFlatConnectionCarrier

    requiredConnectionBridge :
      Set

    requiredConnectionBridgeIsFinite1FormToUserConnection :
      requiredConnectionBridge
      ≡
      (SFGC.SFGCSite2DDiscrete1Form →
       YMSFGCUserSuppliedNonFlatConnectionCarrier)

    finite1FormToUserConnectionBridge :
      SFGC.SFGCSite2DDiscrete1Form →
      YMSFGCUserSuppliedNonFlatConnectionCarrier

    finite1FormToUserConnectionBridgeIsAdapter :
      finite1FormToUserConnectionBridge
      ≡
      ymSFGCUserSuppliedConnectionFromSFGCSite2D1Form

    requiredCurvatureAPI :
      Set

    requiredCurvatureAPIIsUserConnectionToFieldStrength :
      requiredCurvatureAPI
      ≡
      (YMSFGCUserSuppliedNonFlatConnectionCarrier →
       SFGC.SFGCSite2DPlaquette →
       SFGC.SFGCSite2DFieldStrengthBridge)

    finiteUserConnectionCurvatureAPI :
      YMSFGCUserSuppliedNonFlatConnectionCarrier →
      SFGC.SFGCSite2DPlaquette →
      SFGC.SFGCSite2DFieldStrengthBridge

    finiteUserConnectionCurvatureAPIIsProjection :
      finiteUserConnectionCurvatureAPI
      ≡
      ymSFGCUserSuppliedConnectionCurvature

    referenceUserSuppliedConnection :
      YMSFGCUserSuppliedNonFlatConnectionCarrier

    referenceUserSuppliedConnectionIsAdapter :
      referenceUserSuppliedConnection
      ≡
      ymSFGCUserSuppliedReferenceNonFlatConnection

    referenceUserSuppliedCurvatureAtReference :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        (finiteUserConnectionCurvatureAPI
          referenceUserSuppliedConnection
          sfgcReferencePlaquette)
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    requiredPrimitiveSupplySurfaceName :
      String

    requiredPrimitiveSupplySurfaceNameIsExact :
      requiredPrimitiveSupplySurfaceName
      ≡
      "YMSFGCUserSuppliedNonFlatLatticeConnectionPrimitiveSupply"

    u2FiniteDASquaredProbe :
      (A : SFGC.GaugeField) →
      (section : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3DA0Form
        A
        (localFiniteLie3DA0Form A (lieValued0 section))
      ≡
      localFiniteLie3CurvatureBracketActionOn0Form
        (localFiniteLie3FA2Form A)
        (lieValued0 section)

    m2DownstreamReceipt :
      YMSFGCGate3DownstreamHodgeVariationIBPReceipt

    m2DownstreamReceiptIsCanonical :
      m2DownstreamReceipt
      ≡
      canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt

    strictNonFlatCurvatureClosed :
      Bool

    strictNonFlatCurvatureClosedIsFalse :
      strictNonFlatCurvatureClosed ≡ true

    strictHodgeVariationClosed :
      Bool

    strictHodgeVariationClosedIsFalse :
      strictHodgeVariationClosed ≡ false

    exactTypeMismatch :
      List String

    receiptBoundary :
      List String

canonicalYMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt :
  YMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt
canonicalYMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt =
  record
    { status =
        middle6StrictNonFlatCurvatureFiniteBridgeAvailableStrictTokenUnclosed
    ; inspectedBlockerSurface =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; inspectedBlockerSurfaceIsMissingNonFlatCurvature =
        refl
    ; finiteCandidateConnection =
        sfgcReferenceNonFlat1Form
    ; finiteCandidateConnectionIsReference =
        refl
    ; finiteCandidateCurvature =
        sfgcReferenceNonFlatCurvature2Form
    ; finiteCandidateCurvatureIsReference =
        refl
    ; finiteCandidateCurvatureAtReference =
        sfgcReferenceNonFlatCurvatureAtReference
    ; finiteCandidateCurvatureNotVacuum =
        sfgcReferenceNonFlatCurvatureAtReferenceNotVacuum
    ; finiteFieldStrengthBridge =
        sfgcReferenceNonFlatFieldStrengthBridge
    ; finiteFieldStrengthBridgeIsReference =
        refl
    ; finiteFieldStrengthAtReference =
        sfgcReferenceNonFlatFieldStrengthAtReference
    ; finiteLowerCurvatureBridge =
        sfgcFiniteSite2D1FormCurvatureBridge
    ; finiteLowerCurvatureBridgeIsDelta1 =
        refl
    ; strictConnectionCarrier =
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; strictConnectionCarrierIsUserSupplied =
        refl
    ; requiredConnectionBridge =
        SFGC.SFGCSite2DDiscrete1Form →
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; requiredConnectionBridgeIsFinite1FormToUserConnection =
        refl
    ; finite1FormToUserConnectionBridge =
        ymSFGCUserSuppliedConnectionFromSFGCSite2D1Form
    ; finite1FormToUserConnectionBridgeIsAdapter =
        refl
    ; requiredCurvatureAPI =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        SFGC.SFGCSite2DPlaquette →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; requiredCurvatureAPIIsUserConnectionToFieldStrength =
        refl
    ; finiteUserConnectionCurvatureAPI =
        ymSFGCUserSuppliedConnectionCurvature
    ; finiteUserConnectionCurvatureAPIIsProjection =
        refl
    ; referenceUserSuppliedConnection =
        ymSFGCUserSuppliedReferenceNonFlatConnection
    ; referenceUserSuppliedConnectionIsAdapter =
        refl
    ; referenceUserSuppliedCurvatureAtReference =
        ymSFGCUserSuppliedReferenceCurvatureAtReference
    ; requiredPrimitiveSupplySurfaceName =
        "YMSFGCUserSuppliedNonFlatLatticeConnectionPrimitiveSupply"
    ; requiredPrimitiveSupplySurfaceNameIsExact =
        refl
    ; u2FiniteDASquaredProbe =
        localFiniteLie3DASquaredEqualsBracketFAOn0Forms
    ; m2DownstreamReceipt =
        canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt
    ; m2DownstreamReceiptIsCanonical =
        refl
    ; strictNonFlatCurvatureClosed =
        true
    ; strictNonFlatCurvatureClosedIsFalse =
        refl
    ; strictHodgeVariationClosed =
        false
    ; strictHodgeVariationClosedIsFalse =
        refl
    ; exactTypeMismatch =
        "Finite candidate type: SFGC.SFGCSite2DDiscrete2Form, with φ1 at sfgcReferencePlaquette"
        ∷ "Finite lower bridge exists: SFGCSite2DDiscrete1Form -> SFGCSite2DPlaquette -> SFGCSite2DFieldStrengthBridge by δ1"
        ∷ "Finite user-carrier bridge now exists: SFGCSite2DDiscrete1Form -> YMSFGCUserSuppliedNonFlatConnectionCarrier"
        ∷ "Strict curvature API now exists as a projection: YMSFGCUserSuppliedNonFlatConnectionCarrier -> SFGCSite2DPlaquette -> SFGCSite2DFieldStrengthBridge"
        ∷ "Reference user-carrier curvature evaluates to φ1 at sfgcReferencePlaquette"
        ∷ "The obstruction token missingNonFlatSFGCSite2DConnectionCurvature is still an irreducibility marker, not a theorem target closed by this adapter"
        ∷ []
    ; receiptBoundary =
        "m1: additive finite/SFGC non-flat witness remains inhabited locally by sfgcReferenceNonFlatCurvature2Form and φ1-not-φ0"
        ∷ "u2: finite D_A squared handoff remains inhabited only on YMSFGCLocalFiniteLie3Carrier"
        ∷ "m2: downstream Hodge/IBP remains inactive and fail-closed behind the non-flat curvature blocker and variation-pairing blocker"
        ∷ "A finite Site2D user-carrier adapter is added, but no strict non-flat holonomy law, Hodge variation, terminal, Clay, W4, DR, or SM promotion is introduced"
        ∷ []
    }

yangMillsMiddle6StrictNonFlatCurvatureStillFailClosed :
  YMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt.strictNonFlatCurvatureClosed
    canonicalYMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt
  ≡
  true
yangMillsMiddle6StrictNonFlatCurvatureStillFailClosed =
  refl

yangMillsMiddle6StrictNonFlatCurvatureBlockerSurfaceIsExact :
  YMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt.inspectedBlockerSurface
    canonicalYMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsMiddle6StrictNonFlatCurvatureBlockerSurfaceIsExact =
  refl

yangMillsMiddle6StrictNonFlatCurvatureFiniteCandidateAtReference :
  YMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt.finiteCandidateCurvatureAtReference
    canonicalYMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt
  ≡
  sfgcReferenceNonFlatCurvatureAtReference
yangMillsMiddle6StrictNonFlatCurvatureFiniteCandidateAtReference =
  refl

yangMillsMiddle6StrictNonFlatCurvatureU2DASquaredProbeIsCanonical :
  YMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt.u2FiniteDASquaredProbe
    canonicalYMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt
  ≡
  localFiniteLie3DASquaredEqualsBracketFAOn0Forms
yangMillsMiddle6StrictNonFlatCurvatureU2DASquaredProbeIsCanonical =
  refl

yangMillsMiddle6StrictNonFlatCurvatureM2DownstreamReceiptIsCanonical :
  YMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt.m2DownstreamReceipt
    canonicalYMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt
  ≡
  canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt
yangMillsMiddle6StrictNonFlatCurvatureM2DownstreamReceiptIsCanonical =
  refl

------------------------------------------------------------------------
-- Middle6 strict bridge/progress receipt.
--
-- SFGC.SFGCSite2DDiscrete1Form is inhabited and has three constructors, and
-- it does support a direct finite curvature/field-strength bridge via δ1.
-- The user-supplied carrier now has a finite SFGC-backed constructor, so this
-- receipt records that narrow bridge while keeping strict promotion closed.

sfgcDiscrete1FormToFieldStrengthBridge :
  SFGC.SFGCSite2DDiscrete1Form →
  SFGC.SFGCSite2DPlaquette →
  SFGC.SFGCSite2DFieldStrengthBridge
sfgcDiscrete1FormToFieldStrengthBridge connection plaquette =
  SFGC.sfgcSite2DFieldStrengthFromCurvature
    (SFGC.sfgcSite2Dδ₁ connection)

data YMSFGCMiddle6StrictNonFlatBridgeProgressStatus : Set where
  middle6StrictBridgeFiniteAdapterAvailableStrictTokenUnclosed :
    YMSFGCMiddle6StrictNonFlatBridgeProgressStatus

record YMSFGCMiddle6StrictNonFlatBridgeProgressReceipt : Set₁ where
  field
    status :
      YMSFGCMiddle6StrictNonFlatBridgeProgressStatus

    sfgcSourceCarrier :
      Set

    sfgcSourceCarrierIsDiscrete1Form :
      sfgcSourceCarrier
      ≡
      SFGC.SFGCSite2DDiscrete1Form

    sfgcExact1FormConstructor :
      SFGC.SFGCSite2DDiscrete0Form →
      SFGC.SFGCSite2DDiscrete1Form

    sfgcExact1FormConstructorIsExported :
      sfgcExact1FormConstructor
      ≡
      SFGC.sfgcSite2DExact1Form

    sfgcConnection1FormConstructor :
      SFGC.GaugeField →
      SFGC.SFGCSite2DDiscrete1Form

    sfgcConnection1FormConstructorIsExported :
      sfgcConnection1FormConstructor
      ≡
      SFGC.sfgcSite2DConnection1Form

    sfgcArbitrary1FormConstructor :
      (SFGC.SFGCSite2DEdge → SPTI4.Phase4) →
      SFGC.SFGCSite2DDiscrete1Form

    sfgcArbitrary1FormConstructorIsExported :
      sfgcArbitrary1FormConstructor
      ≡
      SFGC.sfgcSite2DArbitrary1Form

    finiteSFGC1FormToFieldStrengthBridge :
      SFGC.SFGCSite2DDiscrete1Form →
      SFGC.SFGCSite2DPlaquette →
      SFGC.SFGCSite2DFieldStrengthBridge

    finiteSFGC1FormToFieldStrengthBridgeIsCanonical :
      finiteSFGC1FormToFieldStrengthBridge
      ≡
      sfgcDiscrete1FormToFieldStrengthBridge

    finiteReferenceBridgeIsReferenceFieldStrength :
      finiteSFGC1FormToFieldStrengthBridge
        sfgcReferenceNonFlat1Form
        sfgcReferencePlaquette
      ≡
      sfgcReferenceNonFlatFieldStrengthBridge

    strictUserConnectionCarrier :
      Set

    strictUserConnectionCarrierIsUserSupplied :
      strictUserConnectionCarrier
      ≡
      YMSFGCUserSuppliedNonFlatConnectionCarrier

    strictUserConnectionBridge :
      SFGC.SFGCSite2DDiscrete1Form →
      YMSFGCUserSuppliedNonFlatConnectionCarrier

    strictUserConnectionBridgeIsCanonical :
      strictUserConnectionBridge
      ≡
      ymSFGCUserSuppliedConnectionFromSFGCSite2D1Form

    requiredStrictConnectionBridge :
      Set

    requiredStrictConnectionBridgeIsSFGC1FormToUserCarrier :
      requiredStrictConnectionBridge
      ≡
      (SFGC.SFGCSite2DDiscrete1Form →
       YMSFGCUserSuppliedNonFlatConnectionCarrier)

    requiredStrictConnectionCurvatureAPI :
      Set

    requiredStrictConnectionCurvatureAPIIsExact :
      requiredStrictConnectionCurvatureAPI
      ≡
      (YMSFGCUserSuppliedNonFlatConnectionCarrier →
       SFGC.SFGCSite2DPlaquette →
       SFGC.SFGCSite2DFieldStrengthBridge)

    strictConnectionCurvatureAPI :
      YMSFGCUserSuppliedNonFlatConnectionCarrier →
      SFGC.SFGCSite2DPlaquette →
      SFGC.SFGCSite2DFieldStrengthBridge

    strictConnectionCurvatureAPIIsProjection :
      strictConnectionCurvatureAPI
      ≡
      ymSFGCUserSuppliedConnectionCurvature

    strictReferenceConnectionCurvatureAtReference :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        (strictConnectionCurvatureAPI
          (strictUserConnectionBridge sfgcReferenceNonFlat1Form)
          sfgcReferencePlaquette)
        sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    exactFirstBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    exactFirstBlockerIsNonFlatCurvature :
      exactFirstBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    strictBridgePromoted :
      Bool

    strictBridgePromotedIsFalse :
      strictBridgePromoted ≡ false

    bridgeBoundary :
      List String

canonicalYMSFGCMiddle6StrictNonFlatBridgeProgressReceipt :
  YMSFGCMiddle6StrictNonFlatBridgeProgressReceipt
canonicalYMSFGCMiddle6StrictNonFlatBridgeProgressReceipt =
  record
    { status =
        middle6StrictBridgeFiniteAdapterAvailableStrictTokenUnclosed
    ; sfgcSourceCarrier =
        SFGC.SFGCSite2DDiscrete1Form
    ; sfgcSourceCarrierIsDiscrete1Form =
        refl
    ; sfgcExact1FormConstructor =
        SFGC.sfgcSite2DExact1Form
    ; sfgcExact1FormConstructorIsExported =
        refl
    ; sfgcConnection1FormConstructor =
        SFGC.sfgcSite2DConnection1Form
    ; sfgcConnection1FormConstructorIsExported =
        refl
    ; sfgcArbitrary1FormConstructor =
        SFGC.sfgcSite2DArbitrary1Form
    ; sfgcArbitrary1FormConstructorIsExported =
        refl
    ; finiteSFGC1FormToFieldStrengthBridge =
        sfgcDiscrete1FormToFieldStrengthBridge
    ; finiteSFGC1FormToFieldStrengthBridgeIsCanonical =
        refl
    ; finiteReferenceBridgeIsReferenceFieldStrength =
        refl
    ; strictUserConnectionCarrier =
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; strictUserConnectionCarrierIsUserSupplied =
        refl
    ; strictUserConnectionBridge =
        ymSFGCUserSuppliedConnectionFromSFGCSite2D1Form
    ; strictUserConnectionBridgeIsCanonical =
        refl
    ; requiredStrictConnectionBridge =
        SFGC.SFGCSite2DDiscrete1Form →
        YMSFGCUserSuppliedNonFlatConnectionCarrier
    ; requiredStrictConnectionBridgeIsSFGC1FormToUserCarrier =
        refl
    ; requiredStrictConnectionCurvatureAPI =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        SFGC.SFGCSite2DPlaquette →
        SFGC.SFGCSite2DFieldStrengthBridge
    ; requiredStrictConnectionCurvatureAPIIsExact =
        refl
    ; strictConnectionCurvatureAPI =
        ymSFGCUserSuppliedConnectionCurvature
    ; strictConnectionCurvatureAPIIsProjection =
        refl
    ; strictReferenceConnectionCurvatureAtReference =
        ymSFGCUserSuppliedReferenceCurvatureAtReference
    ; exactFirstBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; exactFirstBlockerIsNonFlatCurvature =
        refl
    ; strictBridgePromoted =
        false
    ; strictBridgePromotedIsFalse =
        refl
    ; bridgeBoundary =
        "SFGC.SFGCSite2DDiscrete1Form has exactly the exported constructors sfgcSite2DExact1Form, sfgcSite2DConnection1Form, and sfgcSite2DArbitrary1Form"
        ∷ "The strongest local progress is finite: SFGCSite2DDiscrete1Form -> SFGCSite2DPlaquette -> SFGCSite2DFieldStrengthBridge by applying sfgcSite2Dδ1"
        ∷ "The strict target YMSFGCUserSuppliedNonFlatConnectionCarrier now has a finite Site2D constructor carrying the 1-form and selected curvature projection"
        ∷ "A total bridge SFGCSite2DDiscrete1Form -> YMSFGCUserSuppliedNonFlatConnectionCarrier is now supplied by ymSFGCUserSuppliedConnectionFromSFGCSite2D1Form"
        ∷ "The strict curvature API is now the carrier projection ymSFGCUserSuppliedConnectionCurvature, with the reference plaquette evaluating to φ1"
        ∷ "missingNonFlatSFGCSite2DConnectionCurvature remains the exact fail-closed first blocker; no promotion is introduced"
        ∷ []
    }

yangMillsMiddle6StrictNonFlatBridgeProgressStillFailClosed :
  YMSFGCMiddle6StrictNonFlatBridgeProgressReceipt.strictBridgePromoted
    canonicalYMSFGCMiddle6StrictNonFlatBridgeProgressReceipt
  ≡
  false
yangMillsMiddle6StrictNonFlatBridgeProgressStillFailClosed =
  refl

yangMillsMiddle6StrictNonFlatBridgeProgressBridgeIsCanonical :
  YMSFGCMiddle6StrictNonFlatBridgeProgressReceipt.strictUserConnectionBridge
    canonicalYMSFGCMiddle6StrictNonFlatBridgeProgressReceipt
  ≡
  ymSFGCUserSuppliedConnectionFromSFGCSite2D1Form
yangMillsMiddle6StrictNonFlatBridgeProgressBridgeIsCanonical =
  refl

yangMillsMiddle6StrictNonFlatBridgeProgressBlockerIsExact :
  YMSFGCMiddle6StrictNonFlatBridgeProgressReceipt.exactFirstBlocker
    canonicalYMSFGCMiddle6StrictNonFlatBridgeProgressReceipt
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsMiddle6StrictNonFlatBridgeProgressBlockerIsExact =
  refl

------------------------------------------------------------------------
-- Upper6 u2 Gate 3 D_A^2 = [F_A,_] strict receipt.
--
-- The local finite Lie3 surface exposes a typed D_A^2 = [F_A,_] theorem, but
-- the strict real-YM request is still only a requested type over the empty
-- user-supplied Lie carrier.  This receipt records the strongest available
-- inhabitant and the exact upstream inhabitants still missing before it can be
-- promoted to the selected non-flat SFGCSite2D gauge bundle.

data YMSFGCUpper6U2DASquaredBracketStrictReceiptStatus : Set where
  upper6U2LocalDASquaredReceiptStrictPromotionBlocked :
    YMSFGCUpper6U2DASquaredBracketStrictReceiptStatus

record YMSFGCUpper6U2DASquaredBracketStrictReceipt : Set₁ where
  field
    status :
      YMSFGCUpper6U2DASquaredBracketStrictReceiptStatus

    localFiniteLieCarrier :
      Set

    localFiniteLieCarrierIsLie3 :
      localFiniteLieCarrier
      ≡
      YMSFGCLocalFiniteLie3Carrier

    localFiniteBracket :
      YMSFGCLocalFiniteLie3Carrier →
      YMSFGCLocalFiniteLie3Carrier →
      YMSFGCLocalFiniteLie3Carrier

    localFiniteBracketIsCanonical :
      localFiniteBracket
      ≡
      localFiniteLie3Bracket

    localFiniteJacobiWitness :
      (x y z : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3JacobiAdd
        (localFiniteLie3JacobiAdd
          (localFiniteLie3Bracket x (localFiniteLie3Bracket y z))
          (localFiniteLie3Bracket y (localFiniteLie3Bracket z x)))
        (localFiniteLie3Bracket z (localFiniteLie3Bracket x y))
      ≡
      lieZero

    localFiniteDASquaredEqualsBracketF :
      (A : SFGC.GaugeField) →
      (section : YMSFGCLocalFiniteLie3Carrier) →
      localFiniteLie3DA0Form
        A
        (localFiniteLie3DA0Form A (lieValued0 section))
      ≡
      localFiniteLie3CurvatureBracketActionOn0Form
        (localFiniteLie3FA2Form A)
        (lieValued0 section)

    localFiniteDASquaredEqualsBracketFIsCanonical :
      localFiniteDASquaredEqualsBracketF
      ≡
      localFiniteLie3DASquaredEqualsBracketFAOn0Forms

    strictRequestedLieCarrier :
      Set

    strictRequestedLieCarrierIsUserSupplied :
      strictRequestedLieCarrier
      ≡
      YMSFGCUserSuppliedLieAlgebraCarrier

    strictRequestedBracketType :
      Set

    strictRequestedBracketTypeIsCanonicalRequest :
      strictRequestedBracketType
      ≡
      YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedBracketType
        canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest

    strictRequestedCurvatureInFibreType :
      Set

    strictRequestedCurvatureInFibreTypeIsCanonicalRequest :
      strictRequestedCurvatureInFibreType
      ≡
      YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedCurvatureInFibreType
        canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest

    strictRequestedCovariantDerivativeType :
      Set

    strictRequestedCovariantDerivativeTypeIsCanonicalRequest :
      strictRequestedCovariantDerivativeType
      ≡
      YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedCovariantDerivativeType
        canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest

    strictRequestedDASquaredBracketType :
      Set

    strictRequestedDASquaredBracketTypeIsCanonicalRequest :
      strictRequestedDASquaredBracketType
      ≡
      YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedDASquaredCurvatureActionType
        canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest

    strictNonFlatCurvatureBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    strictNonFlatCurvatureBlockerIsExact :
      strictNonFlatCurvatureBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    strictLieCarrierBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    strictLieCarrierBlockerIsExact :
      strictLieCarrierBlocker
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    strictTransportActionBlocker :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    strictTransportActionBlockerIsExact :
      strictTransportActionBlocker
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    strictVariationPairingBlocker :
      YangMillsVariationalEquationMissingPrimitive

    strictVariationPairingBlockerIsExact :
      strictVariationPairingBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    downstreamVariationIBPReceipt :
      YMSFGCGate3DownstreamHodgeVariationIBPReceipt

    downstreamVariationIBPReceiptIsCanonical :
      downstreamVariationIBPReceipt
      ≡
      canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt

    strictDASquaredReceiptPromoted :
      Bool

    strictDASquaredReceiptPromotedIsFalse :
      strictDASquaredReceiptPromoted ≡ false

    exactMissingUpstreamInhabitants :
      List String

    receiptBoundary :
      List String

canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt :
  YMSFGCUpper6U2DASquaredBracketStrictReceipt
canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt =
  record
    { status =
        upper6U2LocalDASquaredReceiptStrictPromotionBlocked
    ; localFiniteLieCarrier =
        YMSFGCLocalFiniteLie3Carrier
    ; localFiniteLieCarrierIsLie3 =
        refl
    ; localFiniteBracket =
        localFiniteLie3Bracket
    ; localFiniteBracketIsCanonical =
        refl
    ; localFiniteJacobiWitness =
        localFiniteLie3JacobiWitness
    ; localFiniteDASquaredEqualsBracketF =
        localFiniteLie3DASquaredEqualsBracketFAOn0Forms
    ; localFiniteDASquaredEqualsBracketFIsCanonical =
        refl
    ; strictRequestedLieCarrier =
        YMSFGCUserSuppliedLieAlgebraCarrier
    ; strictRequestedLieCarrierIsUserSupplied =
        refl
    ; strictRequestedBracketType =
        YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedBracketType
          canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest
    ; strictRequestedBracketTypeIsCanonicalRequest =
        refl
    ; strictRequestedCurvatureInFibreType =
        YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedCurvatureInFibreType
          canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest
    ; strictRequestedCurvatureInFibreTypeIsCanonicalRequest =
        refl
    ; strictRequestedCovariantDerivativeType =
        YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedCovariantDerivativeType
          canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest
    ; strictRequestedCovariantDerivativeTypeIsCanonicalRequest =
        refl
    ; strictRequestedDASquaredBracketType =
        YMSFGCNonAbelianCovariantDerivativeTypedRequest.requestedDASquaredCurvatureActionType
          canonicalYMSFGCNonAbelianCovariantDerivativeTypedRequest
    ; strictRequestedDASquaredBracketTypeIsCanonicalRequest =
        refl
    ; strictNonFlatCurvatureBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; strictNonFlatCurvatureBlockerIsExact =
        refl
    ; strictLieCarrierBlocker =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; strictLieCarrierBlockerIsExact =
        refl
    ; strictTransportActionBlocker =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; strictTransportActionBlockerIsExact =
        refl
    ; strictVariationPairingBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; strictVariationPairingBlockerIsExact =
        refl
    ; downstreamVariationIBPReceipt =
        canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt
    ; downstreamVariationIBPReceiptIsCanonical =
        refl
    ; strictDASquaredReceiptPromoted =
        false
    ; strictDASquaredReceiptPromotedIsFalse =
        refl
    ; exactMissingUpstreamInhabitants =
        "non-flat curvature inhabitant: close missingNonFlatSFGCSite2DConnectionCurvature with a strict holonomy/law witness over YMSFGCUserSuppliedNonFlatConnectionCarrier"
        ∷ "Lie carrier inhabitant: supply YMSFGCUserSuppliedLieAlgebraCarrier plus bracket/add/neg/Jacobi and a selected SFGC field-strength representation into that carrier"
        ∷ "transport action inhabitant: close missingFieldStrengthTransportActionOnSelectedGaugeBundle with field-strength fibre transport/covariant action on the selected SFGCSite2D gauge bundle"
        ∷ "variation pairing inhabitant: close missingVariationPairingForSelectedHodgeStar with a selected action-variation pairing over YMSFGCUserSuppliedVariationCarrier and YMSFGCUserSuppliedActionScalarCarrier"
        ∷ []
    ; receiptBoundary =
        "Upper6 u2 consumes the existing local theorem localFiniteLie3DASquaredEqualsBracketFAOn0Forms"
        ∷ "The strict target remains only the requestedDASquaredCurvatureActionType over YMSFGCUserSuppliedLieAlgebraCarrier"
        ∷ "No term inhabits the strict user-supplied Lie carrier or its bracket/curvature/covariant-derivative action in this module"
        ∷ "No strict non-flat holonomy law, selected field-strength transport action, Hodge variation pairing, D * F = J, D F = 0, terminal, or promotion bit is introduced"
        ∷ []
    }

yangMillsUpper6U2DASquaredBracketStrictReceiptNonPromoting :
  YMSFGCUpper6U2DASquaredBracketStrictReceipt.strictDASquaredReceiptPromoted
    canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt
  ≡
  false
yangMillsUpper6U2DASquaredBracketStrictReceiptNonPromoting =
  refl

yangMillsUpper6U2DASquaredBracketStrictLocalReceiptIsCanonical :
  YMSFGCUpper6U2DASquaredBracketStrictReceipt.localFiniteDASquaredEqualsBracketF
    canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt
  ≡
  localFiniteLie3DASquaredEqualsBracketFAOn0Forms
yangMillsUpper6U2DASquaredBracketStrictLocalReceiptIsCanonical =
  refl

yangMillsUpper6U2DASquaredBracketStrictNonFlatBlockerIsExact :
  YMSFGCUpper6U2DASquaredBracketStrictReceipt.strictNonFlatCurvatureBlocker
    canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsUpper6U2DASquaredBracketStrictNonFlatBlockerIsExact =
  refl

yangMillsUpper6U2DASquaredBracketStrictTransportBlockerIsExact :
  YMSFGCUpper6U2DASquaredBracketStrictReceipt.strictTransportActionBlocker
    canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt
  ≡
  missingFieldStrengthTransportActionOnSelectedGaugeBundle
yangMillsUpper6U2DASquaredBracketStrictTransportBlockerIsExact =
  refl

yangMillsUpper6U2DASquaredBracketStrictVariationBlockerIsExact :
  YMSFGCUpper6U2DASquaredBracketStrictReceipt.strictVariationPairingBlocker
    canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt
  ≡
  missingVariationPairingForSelectedHodgeStar
yangMillsUpper6U2DASquaredBracketStrictVariationBlockerIsExact =
  refl

------------------------------------------------------------------------
-- Middle6 m1 discrete IBP / variation-pairing progress.
--
-- The finite zero-variation IBP law is constructible on SFGC.GaugeField, and
-- the strict requested IBP type is visible in the user-supplied real YM
-- request.  The strict variation-pairing term itself is still not
-- constructible: YMSFGCUserSuppliedVariationCarrier and
-- YMSFGCUserSuppliedActionScalarCarrier remain empty carrier requests.

data YMSFGCMiddle6DiscreteIBPVariationPairingProgressStatus : Set where
  middle6DiscreteIBPFiniteLawAvailableStrictVariationPairingUninhabited :
    YMSFGCMiddle6DiscreteIBPVariationPairingProgressStatus

data YMSFGCMiddle6VariationPairingFirstMissingDependency : Set where
  missingConstructorForYMSFGCUserSuppliedVariationCarrier :
    YMSFGCMiddle6VariationPairingFirstMissingDependency

  missingConstructorForYMSFGCUserSuppliedActionScalarCarrier :
    YMSFGCMiddle6VariationPairingFirstMissingDependency

  missingSelectedActionVariationPairingIntoUserActionScalarCarrier :
    YMSFGCMiddle6VariationPairingFirstMissingDependency

record YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt : Set₁ where
  field
    status :
      YMSFGCMiddle6DiscreteIBPVariationPairingProgressStatus

    finiteIBPVariationCarrier :
      Set

    finiteIBPVariationCarrierIsGaugeField :
      finiteIBPVariationCarrier
      ≡
      SFGC.GaugeField

    finiteIBPActionScalar :
      Set

    finiteIBPActionScalarIsInteger :
      finiteIBPActionScalar
      ≡
      ℤ

    finiteVariationOfAction :
      SFGC.GaugeField →
      SFGC.GaugeField →
      ℤ

    finiteVariationOfActionIsZero :
      finiteVariationOfAction
      ≡
      sfgcZeroVariationOfAction

    finiteEulerLagrangePairing :
      SFGC.GaugeField →
      SFGC.GaugeField →
      ℤ

    finiteEulerLagrangePairingIsZero :
      finiteEulerLagrangePairing
      ≡
      sfgcZeroEulerLagrangePairing

    finiteBoundaryTerm :
      SFGC.GaugeField →
      SFGC.GaugeField →
      ℤ

    finiteBoundaryTermIsZero :
      finiteBoundaryTerm
      ≡
      sfgcZeroBoundaryTerm

    finiteDiscreteIBPLaw :
      (A δA : SFGC.GaugeField) →
      sfgcZeroVariationOfAction A δA
        ≡
      _+ℤ_
        (sfgcZeroEulerLagrangePairing A δA)
        (sfgcZeroBoundaryTerm A δA)

    finiteDiscreteIBPLawIsZeroLaw :
      finiteDiscreteIBPLaw
      ≡
      sfgcZeroDiscreteVariationIBPLaw

    lowerIBPCandidate :
      YMSFGCDiscreteVariationIBPLowerCandidate

    lowerIBPCandidateIsCanonical :
      lowerIBPCandidate
      ≡
      canonicalYMSFGCDiscreteVariationIBPLowerCandidate

    strictVariationCarrier :
      Set

    strictVariationCarrierIsUserSupplied :
      strictVariationCarrier
      ≡
      YMSFGCUserSuppliedVariationCarrier

    strictActionScalarCarrier :
      Set

    strictActionScalarCarrierIsUserSupplied :
      strictActionScalarCarrier
      ≡
      YMSFGCUserSuppliedActionScalarCarrier

    strictRequestedDiscreteIBPLawType :
      Set

    strictRequestedDiscreteIBPLawTypeIsCanonicalRequest :
      strictRequestedDiscreteIBPLawType
      ≡
      YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedDiscreteIBPLawType
        canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    strictRequestedVariationPairingType :
      Set

    strictRequestedVariationPairingTypeIsExact :
      strictRequestedVariationPairingType
      ≡
      (YMSFGCUserSuppliedNonFlatConnectionCarrier →
       YMSFGCUserSuppliedVariationCarrier →
       YMSFGCUserSuppliedActionScalarCarrier)

    firstMissingDependency :
      YMSFGCMiddle6VariationPairingFirstMissingDependency

    firstMissingDependencyIsVariationCarrierConstructor :
      firstMissingDependency
      ≡
      missingConstructorForYMSFGCUserSuppliedVariationCarrier

    exactVariationPairingBlocker :
      YangMillsVariationalEquationMissingPrimitive

    exactVariationPairingBlockerIsMissingVariationPairing :
      exactVariationPairingBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    finiteIBPPromotedToStrict :
      Bool

    finiteIBPPromotedToStrictIsFalse :
      finiteIBPPromotedToStrict ≡ false

    variationPairingPromoted :
      Bool

    variationPairingPromotedIsFalse :
      variationPairingPromoted ≡ false

    progressBoundary :
      List String

canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt :
  YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt
canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt =
  record
    { status =
        middle6DiscreteIBPFiniteLawAvailableStrictVariationPairingUninhabited
    ; finiteIBPVariationCarrier =
        SFGC.GaugeField
    ; finiteIBPVariationCarrierIsGaugeField =
        refl
    ; finiteIBPActionScalar =
        ℤ
    ; finiteIBPActionScalarIsInteger =
        refl
    ; finiteVariationOfAction =
        sfgcZeroVariationOfAction
    ; finiteVariationOfActionIsZero =
        refl
    ; finiteEulerLagrangePairing =
        sfgcZeroEulerLagrangePairing
    ; finiteEulerLagrangePairingIsZero =
        refl
    ; finiteBoundaryTerm =
        sfgcZeroBoundaryTerm
    ; finiteBoundaryTermIsZero =
        refl
    ; finiteDiscreteIBPLaw =
        sfgcZeroDiscreteVariationIBPLaw
    ; finiteDiscreteIBPLawIsZeroLaw =
        refl
    ; lowerIBPCandidate =
        canonicalYMSFGCDiscreteVariationIBPLowerCandidate
    ; lowerIBPCandidateIsCanonical =
        refl
    ; strictVariationCarrier =
        YMSFGCUserSuppliedVariationCarrier
    ; strictVariationCarrierIsUserSupplied =
        refl
    ; strictActionScalarCarrier =
        YMSFGCUserSuppliedActionScalarCarrier
    ; strictActionScalarCarrierIsUserSupplied =
        refl
    ; strictRequestedDiscreteIBPLawType =
        YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedDiscreteIBPLawType
          canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; strictRequestedDiscreteIBPLawTypeIsCanonicalRequest =
        refl
    ; strictRequestedVariationPairingType =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMSFGCUserSuppliedVariationCarrier →
        YMSFGCUserSuppliedActionScalarCarrier
    ; strictRequestedVariationPairingTypeIsExact =
        refl
    ; firstMissingDependency =
        missingConstructorForYMSFGCUserSuppliedVariationCarrier
    ; firstMissingDependencyIsVariationCarrierConstructor =
        refl
    ; exactVariationPairingBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; exactVariationPairingBlockerIsMissingVariationPairing =
        refl
    ; finiteIBPPromotedToStrict =
        false
    ; finiteIBPPromotedToStrictIsFalse =
        refl
    ; variationPairingPromoted =
        false
    ; variationPairingPromotedIsFalse =
        refl
    ; progressBoundary =
        "Finite discrete IBP progress is inhabited by the existing zero variation law over SFGC.GaugeField and integer action scalars"
        ∷ "The strict requested IBP type is recorded exactly from canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest"
        ∷ "The strict selected variation pairing cannot be inhabited because YMSFGCUserSuppliedVariationCarrier has no constructor here"
        ∷ "YMSFGCUserSuppliedActionScalarCarrier is also still an empty request carrier"
        ∷ "missingVariationPairingForSelectedHodgeStar remains exact; no terminal, Clay, spectral-gap, or physical promotion is introduced"
        ∷ []
    }

yangMillsMiddle6DiscreteIBPVariationPairingProgressDoesNotPromote :
  YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt.variationPairingPromoted
    canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt
  ≡
  false
yangMillsMiddle6DiscreteIBPVariationPairingProgressDoesNotPromote =
  refl

yangMillsMiddle6DiscreteIBPVariationPairingFirstMissingIsVariationCarrier :
  YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt.firstMissingDependency
    canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt
  ≡
  missingConstructorForYMSFGCUserSuppliedVariationCarrier
yangMillsMiddle6DiscreteIBPVariationPairingFirstMissingIsVariationCarrier =
  refl

yangMillsMiddle6DiscreteIBPVariationPairingExactBlocker :
  YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt.exactVariationPairingBlocker
    canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt
  ≡
  missingVariationPairingForSelectedHodgeStar
yangMillsMiddle6DiscreteIBPVariationPairingExactBlocker =
  refl

------------------------------------------------------------------------
-- Upper6 Gate 3 strict holonomy finite lower layer.
--
-- This is the strongest content exposed by the current API: a finite C4
-- plaquette holonomy can be wrapped into the user-supplied holonomy carrier,
-- and the requested telescoping/covariance shapes can be inhabited for the
-- identity finite connection action.  The strict non-flat blocker remains the
-- irreducibility token, not a record field closed by this lower witness.

ymSFGCUserSuppliedHolonomyPhase :
  YMSFGCUserSuppliedHolonomyCarrier →
  SPTI4.Phase4
ymSFGCUserSuppliedHolonomyPhase
  (ymSFGCUserSuppliedHolonomyFromPhase phase) =
  phase

ymSFGCUserSuppliedIdentityHolonomy :
  YMSFGCUserSuppliedHolonomyCarrier
ymSFGCUserSuppliedIdentityHolonomy =
  ymSFGCUserSuppliedHolonomyFromPhase SPTI4.φ0

ymSFGCUserSuppliedComposeHolonomy :
  YMSFGCUserSuppliedHolonomyCarrier →
  YMSFGCUserSuppliedHolonomyCarrier →
  YMSFGCUserSuppliedHolonomyCarrier
ymSFGCUserSuppliedComposeHolonomy
  (ymSFGCUserSuppliedHolonomyFromPhase left)
  (ymSFGCUserSuppliedHolonomyFromPhase right) =
  ymSFGCUserSuppliedHolonomyFromPhase
    (SFGS.phaseAdd4 left right)

ymSFGCUserSuppliedInverseHolonomy :
  YMSFGCUserSuppliedHolonomyCarrier →
  YMSFGCUserSuppliedHolonomyCarrier
ymSFGCUserSuppliedInverseHolonomy
  (ymSFGCUserSuppliedHolonomyFromPhase phase) =
  ymSFGCUserSuppliedHolonomyFromPhase
    (SFGS.phaseInv4 phase)

ymSFGCUserSuppliedEdgeHolonomy :
  YMSFGCUserSuppliedNonFlatConnectionCarrier →
  SFGC.SFGCSite2DEdge →
  YMSFGCUserSuppliedHolonomyCarrier
ymSFGCUserSuppliedEdgeHolonomy connection edge =
  ymSFGCUserSuppliedHolonomyFromPhase
    (SFGC.sfgcSite2DEvaluate1
      (ymSFGCUserSuppliedConnection1Form connection)
      edge)

ymSFGCUserSuppliedPlaquetteHolonomy :
  YMSFGCUserSuppliedNonFlatConnectionCarrier →
  SFGC.SFGCSite2DPlaquette →
  YMSFGCUserSuppliedHolonomyCarrier
ymSFGCUserSuppliedPlaquetteHolonomy connection plaquette =
  ymSFGCUserSuppliedHolonomyFromPhase
    (SFGC.sfgcSite2DWilsonLoopPhase
      (ymSFGCUserSuppliedConnection1Form connection)
      plaquette)

ymSFGCUserSuppliedGaugeTransformConnection :
  SFGS.GaugeTransform →
  YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMSFGCUserSuppliedNonFlatConnectionCarrier
ymSFGCUserSuppliedGaugeTransformConnection gauge connection =
  connection

ymSFGCUserSuppliedEndpointGaugeFactor :
  SFGS.GaugeTransform →
  SFGC.SFGCSite2D →
  YMSFGCUserSuppliedHolonomyCarrier
ymSFGCUserSuppliedEndpointGaugeFactor gauge site =
  ymSFGCUserSuppliedHolonomyFromPhase
    (sfgcFiniteC4EndpointGaugeFactor gauge site)

ymSFGCUserSuppliedConjugateBy :
  YMSFGCUserSuppliedHolonomyCarrier →
  YMSFGCUserSuppliedHolonomyCarrier →
  YMSFGCUserSuppliedHolonomyCarrier
ymSFGCUserSuppliedConjugateBy endpoint holonomy =
  holonomy

ymSFGCUserSuppliedHolonomyTelescopingLaw :
  (connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  ymSFGCUserSuppliedComposeHolonomy
    (ymSFGCUserSuppliedComposeHolonomy
      (ymSFGCUserSuppliedComposeHolonomy
        (ymSFGCUserSuppliedEdgeHolonomy
          connection
          (SFGC.sfgcSite2DPlaquetteBottomEdge plaquette))
        (ymSFGCUserSuppliedEdgeHolonomy
          connection
          (SFGC.sfgcSite2DPlaquetteRightEdge plaquette)))
      (ymSFGCUserSuppliedInverseHolonomy
        (ymSFGCUserSuppliedEdgeHolonomy
          connection
          (SFGC.sfgcSite2DPlaquetteTopEdge plaquette))))
    (ymSFGCUserSuppliedInverseHolonomy
      (ymSFGCUserSuppliedEdgeHolonomy
        connection
        (SFGC.sfgcSite2DPlaquetteLeftEdge plaquette)))
  ≡
  ymSFGCUserSuppliedPlaquetteHolonomy connection plaquette
ymSFGCUserSuppliedHolonomyTelescopingLaw connection plaquette =
  refl

holonomyGaugeCovariance :
  (gauge : SFGS.GaugeTransform) →
  (connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  ymSFGCUserSuppliedPlaquetteHolonomy
    (ymSFGCUserSuppliedGaugeTransformConnection gauge connection)
    plaquette
  ≡
  ymSFGCUserSuppliedConjugateBy
    (ymSFGCUserSuppliedEndpointGaugeFactor
      gauge
      (SFGC.sfgcSite2DPlaquetteSW plaquette))
    (ymSFGCUserSuppliedPlaquetteHolonomy connection plaquette)
holonomyGaugeCovariance gauge connection plaquette =
  refl

holonomyUnitPlaquette :
  (plaquette : SFGC.SFGCSite2DPlaquette) →
  ymSFGCUserSuppliedPlaquetteHolonomy
    (ymSFGCUserSuppliedConnectionFromSFGCSite2D1Form
      (SFGC.sfgcSite2DExact1Form (λ site → SPTI4.φ0)))
    plaquette
  ≡
  ymSFGCUserSuppliedIdentityHolonomy
holonomyUnitPlaquette plaquette =
  refl

holonomyNonFlat :
  ymSFGCUserSuppliedPlaquetteHolonomy
    ymSFGCUserSuppliedReferenceNonFlatConnection
    sfgcReferencePlaquette
  ≡
  ymSFGCUserSuppliedHolonomyFromPhase SPTI4.φ1
holonomyNonFlat =
  refl

data YMSFGCUpper6StrictHolonomyAttemptStatus : Set where
  upper6FiniteC4HolonomyLowerLayerStrictTokenUnclosed :
    YMSFGCUpper6StrictHolonomyAttemptStatus

record YMSFGCUpper6StrictHolonomyAttemptReceipt : Set₁ where
  field
    status :
      YMSFGCUpper6StrictHolonomyAttemptStatus

    holonomyCarrier :
      Set

    holonomyCarrierIsUserSupplied :
      holonomyCarrier
      ≡
      YMSFGCUserSuppliedHolonomyCarrier

    unitPlaquetteLaw :
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      ymSFGCUserSuppliedPlaquetteHolonomy
        (ymSFGCUserSuppliedConnectionFromSFGCSite2D1Form
          (SFGC.sfgcSite2DExact1Form (λ site → SPTI4.φ0)))
        plaquette
      ≡
      ymSFGCUserSuppliedIdentityHolonomy

    nonFlatReferenceHolonomy :
      ymSFGCUserSuppliedPlaquetteHolonomy
        ymSFGCUserSuppliedReferenceNonFlatConnection
        sfgcReferencePlaquette
      ≡
      ymSFGCUserSuppliedHolonomyFromPhase SPTI4.φ1

    telescopingLaw :
      (connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      ymSFGCUserSuppliedComposeHolonomy
        (ymSFGCUserSuppliedComposeHolonomy
          (ymSFGCUserSuppliedComposeHolonomy
            (ymSFGCUserSuppliedEdgeHolonomy
              connection
              (SFGC.sfgcSite2DPlaquetteBottomEdge plaquette))
            (ymSFGCUserSuppliedEdgeHolonomy
              connection
              (SFGC.sfgcSite2DPlaquetteRightEdge plaquette)))
          (ymSFGCUserSuppliedInverseHolonomy
            (ymSFGCUserSuppliedEdgeHolonomy
              connection
              (SFGC.sfgcSite2DPlaquetteTopEdge plaquette))))
        (ymSFGCUserSuppliedInverseHolonomy
          (ymSFGCUserSuppliedEdgeHolonomy
            connection
            (SFGC.sfgcSite2DPlaquetteLeftEdge plaquette)))
      ≡
      ymSFGCUserSuppliedPlaquetteHolonomy connection plaquette

    covarianceLaw :
      (gauge : SFGS.GaugeTransform) →
      (connection : YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (plaquette : SFGC.SFGCSite2DPlaquette) →
      ymSFGCUserSuppliedPlaquetteHolonomy
        (ymSFGCUserSuppliedGaugeTransformConnection gauge connection)
        plaquette
      ≡
      ymSFGCUserSuppliedConjugateBy
        (ymSFGCUserSuppliedEndpointGaugeFactor
          gauge
          (SFGC.sfgcSite2DPlaquetteSW plaquette))
        (ymSFGCUserSuppliedPlaquetteHolonomy connection plaquette)

    firstStrictBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    firstStrictBlockerIsCurvature :
      firstStrictBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    strictHolonomyPromoted :
      Bool

    strictHolonomyPromotedIsFalse :
      strictHolonomyPromoted ≡ false

    attemptBoundary :
      List String

canonicalYMSFGCUpper6StrictHolonomyAttemptReceipt :
  YMSFGCUpper6StrictHolonomyAttemptReceipt
canonicalYMSFGCUpper6StrictHolonomyAttemptReceipt =
  record
    { status =
        upper6FiniteC4HolonomyLowerLayerStrictTokenUnclosed
    ; holonomyCarrier =
        YMSFGCUserSuppliedHolonomyCarrier
    ; holonomyCarrierIsUserSupplied =
        refl
    ; unitPlaquetteLaw =
        holonomyUnitPlaquette
    ; nonFlatReferenceHolonomy =
        holonomyNonFlat
    ; telescopingLaw =
        ymSFGCUserSuppliedHolonomyTelescopingLaw
    ; covarianceLaw =
        holonomyGaugeCovariance
    ; firstStrictBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; firstStrictBlockerIsCurvature =
        refl
    ; strictHolonomyPromoted =
        false
    ; strictHolonomyPromotedIsFalse =
        refl
    ; attemptBoundary =
        "Upper6 Gate 3: YMSFGCUserSuppliedHolonomyCarrier is now inhabited by a finite Phase4 wrapper"
        ∷ "holonomyUnitPlaquette closes only for the zero exact SFGCSite2D 1-form lower witness"
        ∷ "holonomyNonFlat records the reference user-supplied non-flat plaquette holonomy as φ1"
        ∷ "Gauge covariance closes only for the finite abelian identity action on the user-supplied connection and identity endpoint conjugation"
        ∷ "The strict blocker missingNonFlatSFGCSite2DConnectionCurvature remains an irreducibility marker, not a promoted theorem"
        ∷ []
    }

yangMillsUpper6StrictHolonomyAttemptStillFailClosed :
  YMSFGCUpper6StrictHolonomyAttemptReceipt.strictHolonomyPromoted
    canonicalYMSFGCUpper6StrictHolonomyAttemptReceipt
  ≡
  false
yangMillsUpper6StrictHolonomyAttemptStillFailClosed =
  refl

yangMillsUpper6StrictHolonomyAttemptBlockerIsExact :
  YMSFGCUpper6StrictHolonomyAttemptReceipt.firstStrictBlocker
    canonicalYMSFGCUpper6StrictHolonomyAttemptReceipt
  ≡
  missingNonFlatSFGCSite2DConnectionCurvature
yangMillsUpper6StrictHolonomyAttemptBlockerIsExact =
  refl

------------------------------------------------------------------------
-- Downstream batch 1 worker A: Gate 3 m1/lower YM receipt.
--
-- This receipt is deliberately downstream of both Upper6 inputs so it can
-- consume the strict holonomy attempt and the u2 D_A^2 bracket receipt without
-- forward references.  It does not promote the selected variation pairing: the
-- m1 finite IBP law is still only the zero lower law, and the strict variation
-- and action-scalar carriers remain uninhabited request surfaces.

data YMSFGCGate3DownstreamM1LowerYMStatus : Set where
  gate3DownstreamM1LowerYMConsumesU1U2StrictVariationPairingBlocked :
    YMSFGCGate3DownstreamM1LowerYMStatus

record YMSFGCGate3DownstreamM1LowerYMReceipt : Set₁ where
  field
    status :
      YMSFGCGate3DownstreamM1LowerYMStatus

    consumedM1IBPVariationReceipt :
      YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt

    consumedM1IBPVariationReceiptIsCanonical :
      consumedM1IBPVariationReceipt
      ≡
      canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt

    consumedU1StrictHolonomyAttempt :
      YMSFGCUpper6StrictHolonomyAttemptReceipt

    consumedU1StrictHolonomyAttemptIsCanonical :
      consumedU1StrictHolonomyAttempt
      ≡
      canonicalYMSFGCUpper6StrictHolonomyAttemptReceipt

    consumedU2DASquaredBracketStrict :
      YMSFGCUpper6U2DASquaredBracketStrictReceipt

    consumedU2DASquaredBracketStrictIsCanonical :
      consumedU2DASquaredBracketStrict
      ≡
      canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt

    consumedGate3DownstreamHodgeVariationIBP :
      YMSFGCGate3DownstreamHodgeVariationIBPReceipt

    consumedGate3DownstreamHodgeVariationIBPIsCanonical :
      consumedGate3DownstreamHodgeVariationIBP
      ≡
      canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt

    lowerIBPCandidate :
      YMSFGCDiscreteVariationIBPLowerCandidate

    lowerIBPCandidateIsM1Canonical :
      lowerIBPCandidate
      ≡
      YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt.lowerIBPCandidate
        consumedM1IBPVariationReceipt

    strictRequestedDiscreteIBPType :
      Set

    strictRequestedDiscreteIBPTypeIsM1Request :
      strictRequestedDiscreteIBPType
      ≡
      YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt.strictRequestedDiscreteIBPLawType
        consumedM1IBPVariationReceipt

    strictRequestedVariationPairingType :
      Set

    strictRequestedVariationPairingTypeIsM1Request :
      strictRequestedVariationPairingType
      ≡
      YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt.strictRequestedVariationPairingType
        consumedM1IBPVariationReceipt

    m1FirstMissingDependency :
      YMSFGCMiddle6VariationPairingFirstMissingDependency

    m1FirstMissingDependencyIsVariationCarrierConstructor :
      m1FirstMissingDependency
      ≡
      missingConstructorForYMSFGCUserSuppliedVariationCarrier

    m1ExactVariationPairingBlocker :
      YangMillsVariationalEquationMissingPrimitive

    m1ExactVariationPairingBlockerIsMissingVariationPairing :
      m1ExactVariationPairingBlocker
      ≡
      missingVariationPairingForSelectedHodgeStar

    u1ExactHolonomyBlocker :
      YMSFGCNonFlatHolonomyConjugationIrreducibility

    u1ExactHolonomyBlockerIsNonFlatCurvature :
      u1ExactHolonomyBlocker
      ≡
      missingNonFlatSFGCSite2DConnectionCurvature

    u2ExactLieCarrierBlocker :
      YMSFGCRealKillingAdInvarianceIrreducibility

    u2ExactLieCarrierBlockerIsMissingLieCarrier :
      u2ExactLieCarrierBlocker
      ≡
      missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    u2ExactTransportActionBlocker :
      YMSFGCSelectedCovariantDerivativeMissingPrimitive

    u2ExactTransportActionBlockerIsMissingTransportAction :
      u2ExactTransportActionBlocker
      ≡
      missingFieldStrengthTransportActionOnSelectedGaugeBundle

    u1StrictHolonomyPromoted :
      Bool

    u1StrictHolonomyPromotedIsFalse :
      u1StrictHolonomyPromoted ≡ false

    u2StrictDASquaredPromoted :
      Bool

    u2StrictDASquaredPromotedIsFalse :
      u2StrictDASquaredPromoted ≡ false

    m1FiniteIBPPromotedToStrict :
      Bool

    m1FiniteIBPPromotedToStrictIsFalse :
      m1FiniteIBPPromotedToStrict ≡ false

    strictVariationPairingPromoted :
      Bool

    strictVariationPairingPromotedIsFalse :
      strictVariationPairingPromoted ≡ false

    downstreamLowerYMPromoted :
      Bool

    downstreamLowerYMPromotedIsFalse :
      downstreamLowerYMPromoted ≡ false

    exactBlockers :
      List String

    receiptBoundary :
      List String

canonicalYMSFGCGate3DownstreamM1LowerYMReceipt :
  YMSFGCGate3DownstreamM1LowerYMReceipt
canonicalYMSFGCGate3DownstreamM1LowerYMReceipt =
  record
    { status =
        gate3DownstreamM1LowerYMConsumesU1U2StrictVariationPairingBlocked
    ; consumedM1IBPVariationReceipt =
        canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt
    ; consumedM1IBPVariationReceiptIsCanonical =
        refl
    ; consumedU1StrictHolonomyAttempt =
        canonicalYMSFGCUpper6StrictHolonomyAttemptReceipt
    ; consumedU1StrictHolonomyAttemptIsCanonical =
        refl
    ; consumedU2DASquaredBracketStrict =
        canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt
    ; consumedU2DASquaredBracketStrictIsCanonical =
        refl
    ; consumedGate3DownstreamHodgeVariationIBP =
        canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt
    ; consumedGate3DownstreamHodgeVariationIBPIsCanonical =
        refl
    ; lowerIBPCandidate =
        canonicalYMSFGCDiscreteVariationIBPLowerCandidate
    ; lowerIBPCandidateIsM1Canonical =
        refl
    ; strictRequestedDiscreteIBPType =
        YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedDiscreteIBPLawType
          canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest
    ; strictRequestedDiscreteIBPTypeIsM1Request =
        refl
    ; strictRequestedVariationPairingType =
        YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMSFGCUserSuppliedVariationCarrier →
        YMSFGCUserSuppliedActionScalarCarrier
    ; strictRequestedVariationPairingTypeIsM1Request =
        refl
    ; m1FirstMissingDependency =
        missingConstructorForYMSFGCUserSuppliedVariationCarrier
    ; m1FirstMissingDependencyIsVariationCarrierConstructor =
        refl
    ; m1ExactVariationPairingBlocker =
        missingVariationPairingForSelectedHodgeStar
    ; m1ExactVariationPairingBlockerIsMissingVariationPairing =
        refl
    ; u1ExactHolonomyBlocker =
        missingNonFlatSFGCSite2DConnectionCurvature
    ; u1ExactHolonomyBlockerIsNonFlatCurvature =
        refl
    ; u2ExactLieCarrierBlocker =
        missingLieAlgebraCarrierForSelectedFiniteGaugeSector
    ; u2ExactLieCarrierBlockerIsMissingLieCarrier =
        refl
    ; u2ExactTransportActionBlocker =
        missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; u2ExactTransportActionBlockerIsMissingTransportAction =
        refl
    ; u1StrictHolonomyPromoted =
        false
    ; u1StrictHolonomyPromotedIsFalse =
        refl
    ; u2StrictDASquaredPromoted =
        false
    ; u2StrictDASquaredPromotedIsFalse =
        refl
    ; m1FiniteIBPPromotedToStrict =
        false
    ; m1FiniteIBPPromotedToStrictIsFalse =
        refl
    ; strictVariationPairingPromoted =
        false
    ; strictVariationPairingPromotedIsFalse =
        refl
    ; downstreamLowerYMPromoted =
        false
    ; downstreamLowerYMPromotedIsFalse =
        refl
    ; exactBlockers =
        "m1/lower blocker: YMSFGCUserSuppliedVariationCarrier has no constructor, so the selected variation pairing cannot be inhabited"
        ∷ "m1/lower blocker: YMSFGCUserSuppliedActionScalarCarrier remains an empty request carrier"
        ∷ "u1 blocker consumed: missingNonFlatSFGCSite2DConnectionCurvature remains the strict holonomy/non-flat curvature token"
        ∷ "u2 blocker consumed: YMSFGCUserSuppliedLieAlgebraCarrier plus selected bracket/curvature/covariant-derivative action are not inhabited"
        ∷ "u2 blocker consumed: missingFieldStrengthTransportActionOnSelectedGaugeBundle remains exact"
        ∷ []
    ; receiptBoundary =
        "Downstream batch 1 worker A consumes canonicalYMSFGCUpper6StrictHolonomyAttemptReceipt"
        ∷ "Downstream batch 1 worker A consumes canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt"
        ∷ "The m1 lower IBP evidence is the existing zero finite law and canonical lower candidate only"
        ∷ "Strict variation pairing remains blocked at the exact m1 first missing dependency"
        ∷ "No terminal theorem, Yang-Mills equation, Clay mass gap, spectral gap, or promoted success bit is introduced"
        ∷ []
    }

yangMillsGate3DownstreamM1LowerYMDoesNotPromote :
  YMSFGCGate3DownstreamM1LowerYMReceipt.downstreamLowerYMPromoted
    canonicalYMSFGCGate3DownstreamM1LowerYMReceipt
  ≡
  false
yangMillsGate3DownstreamM1LowerYMDoesNotPromote =
  refl

yangMillsGate3DownstreamM1LowerYMConsumesStrictHolonomyAttempt :
  YMSFGCGate3DownstreamM1LowerYMReceipt.consumedU1StrictHolonomyAttempt
    canonicalYMSFGCGate3DownstreamM1LowerYMReceipt
  ≡
  canonicalYMSFGCUpper6StrictHolonomyAttemptReceipt
yangMillsGate3DownstreamM1LowerYMConsumesStrictHolonomyAttempt =
  refl

yangMillsGate3DownstreamM1LowerYMConsumesU2DASquaredBracketStrict :
  YMSFGCGate3DownstreamM1LowerYMReceipt.consumedU2DASquaredBracketStrict
    canonicalYMSFGCGate3DownstreamM1LowerYMReceipt
  ≡
  canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt
yangMillsGate3DownstreamM1LowerYMConsumesU2DASquaredBracketStrict =
  refl

yangMillsGate3DownstreamM1LowerYMVariationBlockerIsExact :
  YMSFGCGate3DownstreamM1LowerYMReceipt.m1ExactVariationPairingBlocker
    canonicalYMSFGCGate3DownstreamM1LowerYMReceipt
  ≡
  missingVariationPairingForSelectedHodgeStar
yangMillsGate3DownstreamM1LowerYMVariationBlockerIsExact =
  refl
