module DASHI.Physics.Closure.DiscreteToSmoothEinsteinLimitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ContinuumLimitTheorem as CL
import DASHI.Physics.Closure.DiscreteBianchiIdentityReceipt as Bianchi
import DASHI.Physics.Closure.DiscreteBianchiIdentitySurface as DBIS
import DASHI.Physics.Closure.DiscreteStokesBianchiObstruction as StokesObs
import DASHI.Physics.Closure.GRDiscreteRicciCandidateFromCurvature as Ricci
import DASHI.Physics.Closure.W4MatterStressEnergyInterfaceReceipt as W4Stress

------------------------------------------------------------------------
-- Discrete-to-smooth Einstein limit receipt obligation.
--
-- This module is deliberately non-promoting.  It records the typed sockets
-- needed to compare a discrete curvature/Ricci candidate against a smooth
-- Sobolev-style convergence target and an independently supplied stress-energy
-- convergence target.  It does not construct continuum GR, an Einstein
-- equation, a Clay bridge, a GR/QFT bridge, or a source-coupled theorem.

data DiscreteToSmoothEinsteinLimitStatus : Set where
  obligationSurfaceOnlyNoPromotion :
    DiscreteToSmoothEinsteinLimitStatus

data DiscreteToSmoothEinsteinLimitFirstMissing : Set where
  missingDiscreteToSmoothCurvatureConvergence :
    DiscreteToSmoothEinsteinLimitFirstMissing

  missingDiscreteRicciToSmoothRicciIdentification :
    DiscreteToSmoothEinsteinLimitFirstMissing

  missingStressEnergyConvergenceAuthority :
    DiscreteToSmoothEinsteinLimitFirstMissing

  missingSmoothEinsteinContinuityLaw :
    DiscreteToSmoothEinsteinLimitFirstMissing

data DiscreteToSmoothEinsteinLimitUnsupportedClaim : Set where
  unsupportedContinuumGRClaim :
    DiscreteToSmoothEinsteinLimitUnsupportedClaim

  unsupportedEinsteinEquationClaim :
    DiscreteToSmoothEinsteinLimitUnsupportedClaim

  unsupportedClayBridgeClaim :
    DiscreteToSmoothEinsteinLimitUnsupportedClaim

  unsupportedGRQFTPromotionClaim :
    DiscreteToSmoothEinsteinLimitUnsupportedClaim

canonicalDiscreteToSmoothEinsteinLimitUnsupportedClaims :
  List DiscreteToSmoothEinsteinLimitUnsupportedClaim
canonicalDiscreteToSmoothEinsteinLimitUnsupportedClaims =
  unsupportedContinuumGRClaim
  ∷ unsupportedEinsteinEquationClaim
  ∷ unsupportedClayBridgeClaim
  ∷ unsupportedGRQFTPromotionClaim
  ∷ []

data HolonomyTaylorRicciConvergenceMissingField : Set where
  missingUltrametricLatticeSpacingDefinition :
    HolonomyTaylorRicciConvergenceMissingField

  missingLieGroupExponentialTaylorRemainder :
    HolonomyTaylorRicciConvergenceMissingField

  missingPlaquetteHolonomyCurvatureExtraction :
    HolonomyTaylorRicciConvergenceMissingField

  missingRicciContractionCommutesWithDepthLimit :
    HolonomyTaylorRicciConvergenceMissingField

  missingUniformCurvatureDerivativeBound :
    HolonomyTaylorRicciConvergenceMissingField

  missingDiscreteRicciC0ConvergenceRate :
    HolonomyTaylorRicciConvergenceMissingField

canonicalHolonomyTaylorRicciConvergenceMissingFields :
  List HolonomyTaylorRicciConvergenceMissingField
canonicalHolonomyTaylorRicciConvergenceMissingFields =
  missingUltrametricLatticeSpacingDefinition
  ∷ missingLieGroupExponentialTaylorRemainder
  ∷ missingPlaquetteHolonomyCurvatureExtraction
  ∷ missingRicciContractionCommutesWithDepthLimit
  ∷ missingUniformCurvatureDerivativeBound
  ∷ missingDiscreteRicciC0ConvergenceRate
  ∷ []

record HolonomyTaylorRicciConvergenceSupplyInterface : Setω where
  field
    Depth :
      Set

    LatticeSpacing :
      Depth →
      Set

    SmoothConnection :
      Set

    PlaquetteHolonomy :
      Depth →
      SmoothConnection →
      Set

    SmoothCurvature :
      SmoothConnection →
      Set

    DiscreteCurvatureExtraction :
      (depth : Depth) →
      (conn : SmoothConnection) →
      PlaquetteHolonomy depth conn →
      Set

    SmoothRicci :
      SmoothConnection →
      Set

    DiscreteRicci :
      Depth →
      Set

    depthPlaceholder :
      Depth

    smoothConnectionPlaceholder :
      SmoothConnection

    holonomyTaylorExpansion :
      (depth : Depth) →
      (conn : SmoothConnection) →
      Set

    curvatureExtractionErrorBound :
      (depth : Depth) →
      (conn : SmoothConnection) →
      Set

    ricciContractionLimitCompatibility :
      (depth : Depth) →
      (conn : SmoothConnection) →
      Set

    uniformCurvatureDerivativeBound :
      Set

    discreteRicciC0ConvergenceRate :
      (depth : Depth) →
      (conn : SmoothConnection) →
      Set

    supplyBoundary :
      List String

open HolonomyTaylorRicciConvergenceSupplyInterface public

record HolonomyTaylorRicciConvergencePrimitiveRequest : Set where
  field
    targetName :
      String

    exactMissingFields :
      List HolonomyTaylorRicciConvergenceMissingField

    exactMissingFieldsAreCanonical :
      exactMissingFields
      ≡
      canonicalHolonomyTaylorRicciConvergenceMissingFields

    firstMissingField :
      HolonomyTaylorRicciConvergenceMissingField

    firstMissingFieldIsLatticeSpacing :
      firstMissingField
      ≡
      missingUltrametricLatticeSpacingDefinition

    requestedHolonomyTaylorForm :
      String

    requestedRicciConvergenceForm :
      String

    constructedFromCurrentReceipt :
      Bool

    constructedFromCurrentReceiptIsFalse :
      constructedFromCurrentReceipt ≡ false

    requestBoundary :
      List String

open HolonomyTaylorRicciConvergencePrimitiveRequest public

canonicalHolonomyTaylorRicciConvergencePrimitiveRequest :
  HolonomyTaylorRicciConvergencePrimitiveRequest
canonicalHolonomyTaylorRicciConvergencePrimitiveRequest =
  record
    { targetName =
        "HolonomyTaylorRicciConvergenceSupplyInterface"
    ; exactMissingFields =
        canonicalHolonomyTaylorRicciConvergenceMissingFields
    ; exactMissingFieldsAreCanonical =
        refl
    ; firstMissingField =
        missingUltrametricLatticeSpacingDefinition
    ; firstMissingFieldIsLatticeSpacing =
        refl
    ; requestedHolonomyTaylorForm =
        "Hol(plaquette at depth d) = exp(F * a_d^2) plus controlled Taylor remainder"
    ; requestedRicciConvergenceForm =
        "norm (Ricci_discrete d - Ricci_smooth) <= C * a_d, or stronger C * a_d^2, with uniform curvature derivative bound"
    ; constructedFromCurrentReceipt =
        false
    ; constructedFromCurrentReceiptIsFalse =
        refl
    ; requestBoundary =
        "The current receipt has Nat-indexed target sockets but no Lie group exp/log or analytic Taylor remainder theorem"
        ∷ "Supplying this interface is enough to name the discrete-to-smooth Ricci convergence route without claiming continuum GR"
        ∷ []
    }

data BCHHolonomyTaylorAuthorityBoundaryMissingField : Set where
  missingBCHSeriesConvergenceAuthority :
    BCHHolonomyTaylorAuthorityBoundaryMissingField

  missingLieAlgebraBracketNormAuthority :
    BCHHolonomyTaylorAuthorityBoundaryMissingField

  missingPlaquetteLogBranchAuthority :
    BCHHolonomyTaylorAuthorityBoundaryMissingField

  missingUniformTaylorRemainderAuthority :
    BCHHolonomyTaylorAuthorityBoundaryMissingField

canonicalBCHHolonomyTaylorAuthorityBoundaryMissingFields :
  List BCHHolonomyTaylorAuthorityBoundaryMissingField
canonicalBCHHolonomyTaylorAuthorityBoundaryMissingFields =
  missingBCHSeriesConvergenceAuthority
  ∷ missingLieAlgebraBracketNormAuthority
  ∷ missingPlaquetteLogBranchAuthority
  ∷ missingUniformTaylorRemainderAuthority
  ∷ []

record BCHHolonomyTaylorAuthorityBoundaryLedger : Set where
  field
    ledgerName :
      String

    holonomyTaylorRequest :
      HolonomyTaylorRicciConvergencePrimitiveRequest

    holonomyTaylorRequestIsCanonical :
      holonomyTaylorRequest
      ≡
      canonicalHolonomyTaylorRicciConvergencePrimitiveRequest

    missingAuthorityFields :
      List BCHHolonomyTaylorAuthorityBoundaryMissingField

    missingAuthorityFieldsAreCanonical :
      missingAuthorityFields
      ≡
      canonicalBCHHolonomyTaylorAuthorityBoundaryMissingFields

    firstMissingAuthorityField :
      BCHHolonomyTaylorAuthorityBoundaryMissingField

    firstMissingAuthorityFieldIsBCHSeriesConvergence :
      firstMissingAuthorityField
      ≡
      missingBCHSeriesConvergenceAuthority

    internallyProvedFromCurrentReceipt :
      Bool

    internallyProvedFromCurrentReceiptIsFalse :
      internallyProvedFromCurrentReceipt ≡ false

    acceptedAsContinuumPromotion :
      Bool

    acceptedAsContinuumPromotionIsFalse :
      acceptedAsContinuumPromotion ≡ false

    exactAuthorityBoundary :
      List String

canonicalBCHHolonomyTaylorAuthorityBoundaryLedger :
  BCHHolonomyTaylorAuthorityBoundaryLedger
canonicalBCHHolonomyTaylorAuthorityBoundaryLedger =
  record
    { ledgerName =
        "BCHHolonomyTaylorAuthorityBoundaryLedger"
    ; holonomyTaylorRequest =
        canonicalHolonomyTaylorRicciConvergencePrimitiveRequest
    ; holonomyTaylorRequestIsCanonical =
        refl
    ; missingAuthorityFields =
        canonicalBCHHolonomyTaylorAuthorityBoundaryMissingFields
    ; missingAuthorityFieldsAreCanonical =
        refl
    ; firstMissingAuthorityField =
        missingBCHSeriesConvergenceAuthority
    ; firstMissingAuthorityFieldIsBCHSeriesConvergence =
        refl
    ; internallyProvedFromCurrentReceipt =
        false
    ; internallyProvedFromCurrentReceiptIsFalse =
        refl
    ; acceptedAsContinuumPromotion =
        false
    ; acceptedAsContinuumPromotionIsFalse =
        refl
    ; exactAuthorityBoundary =
        "The current receipt does not contain a Lie group exponential/logarithm implementation"
        ∷ "The current receipt does not contain a BCH convergence theorem or bracket-norm authority"
        ∷ "The current receipt does not choose a plaquette logarithm branch"
        ∷ "The current receipt does not prove a uniform Taylor remainder bound for holonomy curvature extraction"
        ∷ "This ledger records the authority boundary only and is not a continuum GR or Clay promotion"
        ∷ []
    }

record DiscreteToSmoothEinsteinLimitReceipt : Setω where
  field
    status :
      DiscreteToSmoothEinsteinLimitStatus

    discreteRicciCandidate :
      Ricci.GRDiscreteRicciCandidateFromCurvature

    discreteRicciCandidateIsCanonical :
      discreteRicciCandidate
      ≡
      Ricci.canonicalGRDiscreteRicciCandidateFromCurvature

    continuumLimitCandidate :
      CL.ContinuumLimitTheoremCandidate

    stressEnergyRequest :
      W4Stress.W4StressEnergyMatterComponentRequest

    discreteBianchiReceipt :
      Bianchi.DiscreteBianchiIdentityReceipt

    discreteBianchiReceiptIsCanonical :
      discreteBianchiReceipt
      ≡
      Bianchi.canonicalDiscreteBianchiIdentityReceipt

    discreteStokesBianchiObstruction :
      StokesObs.DiscreteStokesBianchiObstruction

    discreteStokesBianchiObstructionIsCanonical :
      discreteStokesBianchiObstruction
      ≡
      StokesObs.canonicalDiscreteStokesBianchiObstruction

    inheritedCRTDiscreteStokesSpecialisationFirstMissingField :
      StokesObs.CRTDiscreteStokesSpecialisationMissingField

    inheritedCRTDiscreteStokesSpecialisationFirstMissingFieldIsBoundaryWordInterpreter :
      inheritedCRTDiscreteStokesSpecialisationFirstMissingField
      ≡
      StokesObs.missingStokesBoundaryWordInterpreterToCRTBoundaryWord

    inheritedErasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation :
      Bool

    inheritedErasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisationIsFalse :
      inheritedErasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation
      ≡
      false

    inheritedFirstMissingSemanticLawAfterTypedInterpreter :
      StokesObs.CRTDiscreteStokesSpecialisationMissingField

    inheritedFirstMissingSemanticLawAfterTypedInterpreterIsBoundaryInterpreterLaw :
      inheritedFirstMissingSemanticLawAfterTypedInterpreter
      ≡
      StokesObs.missingStokesBoundaryWordInterpreterLawForCRTBoundary

    contractedBianchiSurface :
      DBIS.DiscreteBianchiIdentitySurface

    inheritedPrimeAdapterRemainingPrimitive :
      DBIS.PrimeDifferenceToRiemannConnectionAdapterMissingPrimitive

    inheritedPrimeAdapterRemainingPrimitiveIsNonFlatWitness :
      inheritedPrimeAdapterRemainingPrimitive
      ≡
      DBIS.missingAdapterNonFlatWitnessForAlignedRequest

    inheritedCRTBoundaryOfBoundaryCarrier :
      StokesObs.CRTMonodromyBoundaryOfBoundaryCarrier

    inheritedCRTBoundaryOfBoundaryCarrierIsCanonical :
      inheritedCRTBoundaryOfBoundaryCarrier
      ≡
      StokesObs.canonicalCRTMonodromyBoundaryOfBoundaryCarrier

    inheritedCRTBoundaryOfBoundaryWord :
      List StokesObs.CRTMonodromy1Edge

    inheritedCRTBoundaryOfBoundaryWordIsEmpty :
      inheritedCRTBoundaryOfBoundaryWord ≡ []

    inheritedCRTBoundaryWordToHolonomyTransport :
      StokesObs.CRTBoundaryWordToHolonomyTransport

    inheritedCRTBoundaryWordToHolonomyTransportIsCanonical :
      inheritedCRTBoundaryWordToHolonomyTransport
      ≡
      StokesObs.canonicalCRTBoundaryWordToHolonomyTransport

    inheritedCRTBoundaryWordHolonomyTraceHomomorphism :
      StokesObs.CRTBoundaryWordHolonomyTraceHomomorphism

    inheritedCRTBoundaryWordHolonomyTraceHomomorphismIsCanonical :
      inheritedCRTBoundaryWordHolonomyTraceHomomorphism
      ≡
      StokesObs.canonicalCRTBoundaryWordHolonomyTraceHomomorphism

    inheritedNonErasingStokesBoundaryWordInterpreterPrimitiveRequestName :
      String

    inheritedLocalBoundaryWordAtDepthOpaquePrimitiveRequestTypeName :
      String

    inheritedCRTBoundaryOfBoundaryAction :
      StokesObs.CRTBoundaryWordAction

    inheritedCRTBoundaryOfBoundaryActionIsIdentity :
      inheritedCRTBoundaryOfBoundaryAction
      ≡
      StokesObs.identityCRTBoundaryWordAction

    holonomyTaylorRicciConvergencePrimitiveRequest :
      HolonomyTaylorRicciConvergencePrimitiveRequest

    holonomyTaylorRicciConvergencePrimitiveRequestIsCanonical :
      holonomyTaylorRicciConvergencePrimitiveRequest
      ≡
      canonicalHolonomyTaylorRicciConvergencePrimitiveRequest

    bchHolonomyTaylorAuthorityBoundaryLedger :
      BCHHolonomyTaylorAuthorityBoundaryLedger

    bchHolonomyTaylorAuthorityBoundaryLedgerIsCanonical :
      bchHolonomyTaylorAuthorityBoundaryLedger
      ≡
      canonicalBCHHolonomyTaylorAuthorityBoundaryLedger

    bchHolonomyTaylorAuthorityInternallyProved :
      Bool

    bchHolonomyTaylorAuthorityInternallyProvedIsFalse :
      bchHolonomyTaylorAuthorityInternallyProved ≡ false

    DiscreteCurvatureCandidate :
      Set

    DiscreteRicciCandidate :
      Set

    LatticeDepthParameter :
      Set

    SmoothSobolevConvergenceTarget :
      Set

    SmoothRicciConvergenceTarget :
      Set

    StressEnergyConvergenceTarget :
      Set

    discreteCurvatureAtDepth :
      LatticeDepthParameter →
      DiscreteCurvatureCandidate

    discreteRicciAtDepth :
      LatticeDepthParameter →
      DiscreteRicciCandidate

    curvatureConvergenceTarget :
      LatticeDepthParameter →
      DiscreteCurvatureCandidate →
      SmoothSobolevConvergenceTarget →
      Set

    ricciConvergenceTarget :
      LatticeDepthParameter →
      DiscreteRicciCandidate →
      SmoothRicciConvergenceTarget →
      Set

    stressEnergyConvergenceTarget :
      LatticeDepthParameter →
      StressEnergyConvergenceTarget →
      Set

    firstMissing :
      DiscreteToSmoothEinsteinLimitFirstMissing

    firstMissingIsCurvatureConvergence :
      firstMissing
      ≡
      missingDiscreteToSmoothCurvatureConvergence

    suppliedSurface :
      List String

    missingSurface :
      List String

    unsupportedClaims :
      List DiscreteToSmoothEinsteinLimitUnsupportedClaim

    unsupportedClaimsAreCanonical :
      unsupportedClaims
      ≡
      canonicalDiscreteToSmoothEinsteinLimitUnsupportedClaims

    nonPromotionBoundary :
      List String

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

private
  depthCurvatureCandidate :
    Nat →
    Nat
  depthCurvatureCandidate depth = depth

  depthRicciCandidate :
    Nat →
    Nat
  depthRicciCandidate depth = depth

  natIndexedTarget :
    Nat →
    Nat →
    Nat →
    Set
  natIndexedTarget _ _ _ = Nat

  natStressEnergyTarget :
    Nat →
    Nat →
    Set
  natStressEnergyTarget _ _ = Nat

canonicalDiscreteToSmoothEinsteinLimitReceipt :
  DiscreteToSmoothEinsteinLimitReceipt
canonicalDiscreteToSmoothEinsteinLimitReceipt =
  record
    { status =
        obligationSurfaceOnlyNoPromotion
    ; discreteRicciCandidate =
        Ricci.canonicalGRDiscreteRicciCandidateFromCurvature
    ; discreteRicciCandidateIsCanonical =
        refl
    ; continuumLimitCandidate =
        CL.canonicalContinuumLimitTheoremCandidate
    ; stressEnergyRequest =
        W4Stress.canonicalW4StressEnergyMatterComponentRequest
    ; discreteBianchiReceipt =
        Bianchi.canonicalDiscreteBianchiIdentityReceipt
    ; discreteBianchiReceiptIsCanonical =
        refl
    ; discreteStokesBianchiObstruction =
        StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; discreteStokesBianchiObstructionIsCanonical =
        refl
    ; inheritedCRTDiscreteStokesSpecialisationFirstMissingField =
        StokesObs.DiscreteStokesBianchiObstruction.crtDiscreteStokesSpecialisationFirstMissingField
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; inheritedCRTDiscreteStokesSpecialisationFirstMissingFieldIsBoundaryWordInterpreter =
        refl
    ; inheritedErasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation =
        StokesObs.DiscreteStokesBianchiObstruction.erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; inheritedErasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisationIsFalse =
        refl
    ; inheritedFirstMissingSemanticLawAfterTypedInterpreter =
        StokesObs.DiscreteStokesBianchiObstruction.firstMissingSemanticLawAfterTypedInterpreter
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; inheritedFirstMissingSemanticLawAfterTypedInterpreterIsBoundaryInterpreterLaw =
        refl
    ; contractedBianchiSurface =
        DBIS.canonicalDiscreteBianchiIdentitySurface
    ; inheritedPrimeAdapterRemainingPrimitive =
        DBIS.PrimeDifferenceToRiemannConnectionAdapterReceipt.firstMissingAdapterPrimitive
          DBIS.canonicalPrimeDifferenceToRiemannConnectionAdapterReceipt
    ; inheritedPrimeAdapterRemainingPrimitiveIsNonFlatWitness =
        refl
    ; inheritedCRTBoundaryOfBoundaryCarrier =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryOfBoundaryCarrier
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; inheritedCRTBoundaryOfBoundaryCarrierIsCanonical =
        refl
    ; inheritedCRTBoundaryOfBoundaryWord =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryOfBoundaryWord
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; inheritedCRTBoundaryOfBoundaryWordIsEmpty =
        refl
    ; inheritedCRTBoundaryWordToHolonomyTransport =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryWordToHolonomyTransport
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; inheritedCRTBoundaryWordToHolonomyTransportIsCanonical =
        refl
    ; inheritedCRTBoundaryWordHolonomyTraceHomomorphism =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryWordHolonomyTraceHomomorphism
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; inheritedCRTBoundaryWordHolonomyTraceHomomorphismIsCanonical =
        refl
    ; inheritedNonErasingStokesBoundaryWordInterpreterPrimitiveRequestName =
        StokesObs.DiscreteStokesBianchiObstruction.nonErasingStokesBoundaryWordInterpreterPrimitiveRequestName
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; inheritedLocalBoundaryWordAtDepthOpaquePrimitiveRequestTypeName =
        StokesObs.DiscreteStokesBianchiObstruction.localBoundaryWordAtDepthOpaquePrimitiveRequestTypeName
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; inheritedCRTBoundaryOfBoundaryAction =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryOfBoundaryAction
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; inheritedCRTBoundaryOfBoundaryActionIsIdentity =
        refl
    ; holonomyTaylorRicciConvergencePrimitiveRequest =
        canonicalHolonomyTaylorRicciConvergencePrimitiveRequest
    ; holonomyTaylorRicciConvergencePrimitiveRequestIsCanonical =
        refl
    ; bchHolonomyTaylorAuthorityBoundaryLedger =
        canonicalBCHHolonomyTaylorAuthorityBoundaryLedger
    ; bchHolonomyTaylorAuthorityBoundaryLedgerIsCanonical =
        refl
    ; bchHolonomyTaylorAuthorityInternallyProved =
        false
    ; bchHolonomyTaylorAuthorityInternallyProvedIsFalse =
        refl
    ; DiscreteCurvatureCandidate =
        Nat
    ; DiscreteRicciCandidate =
        Nat
    ; LatticeDepthParameter =
        Nat
    ; SmoothSobolevConvergenceTarget =
        Nat
    ; SmoothRicciConvergenceTarget =
        Nat
    ; StressEnergyConvergenceTarget =
        Nat
    ; discreteCurvatureAtDepth =
        depthCurvatureCandidate
    ; discreteRicciAtDepth =
        depthRicciCandidate
    ; curvatureConvergenceTarget =
        natIndexedTarget
    ; ricciConvergenceTarget =
        natIndexedTarget
    ; stressEnergyConvergenceTarget =
        natStressEnergyTarget
    ; firstMissing =
        missingDiscreteToSmoothCurvatureConvergence
    ; firstMissingIsCurvatureConvergence =
        refl
    ; suppliedSurface =
        "GRDiscreteRicciCandidateFromCurvature supplies the current discrete curvature/Ricci candidate shape"
        ∷ "DiscreteBianchiIdentityReceipt supplies the current non-promoting discrete Bianchi obligation receipt"
        ∷ "DiscreteStokesBianchiObstruction supplies a formal CRT boundary-of-boundary carrier with empty boundary word and identity holonomy action"
        ∷ "DiscreteStokesBianchiObstruction supplies a CRT-side shell-word holonomy trace homomorphism"
        ∷ "DiscreteStokesBianchiObstruction now exposes a typed erasing boundary-word interpreter that is not accepted as CRT Stokes specialisation"
        ∷ "NonErasingStokesBoundaryWordInterpreterPrimitiveRequest is inherited as the exact opaque BoundaryWordAtDepth request"
        ∷ "The first semantic law after that typed fallback is missingStokesBoundaryWordInterpreterLawForCRTBoundary"
        ∷ "DiscreteBianchiIdentitySurface supplies prime finite-difference commutation and the aligned adapter-law receipt"
        ∷ "ContinuumLimitTheorem supplies the current lattice-to-continuum theorem-request boundary"
        ∷ "W4MatterStressEnergyInterfaceReceipt supplies the current stress-energy request boundary"
        ∷ "This receipt records lattice/depth, Sobolev convergence, Ricci convergence, and stress-energy convergence target sockets"
        ∷ "HolonomyTaylorRicciConvergencePrimitiveRequest names the exact holonomy Taylor/Ricci convergence supply interface"
        ∷ "BCHHolonomyTaylorAuthorityBoundaryLedger records the BCH/Taylor authority boundary as unproved internally"
        ∷ []
    ; missingSurface =
        "No discrete-to-smooth curvature convergence proof is supplied"
        ∷ "No non-flat FactorVec/SSP connection witness is supplied for the aligned prime-difference adapter"
        ∷ "No discrete Stokes specialization for the CRT connection is supplied"
        ∷ "No non-erasing boundary-word interpreter law from the opaque local Stokes BoundaryWordAtDepth surface to the CRT boundary shell is supplied"
        ∷ "No boundary holonomy to cyclic covariant derivative bridge is supplied"
        ∷ "No contracted Bianchi primitive bundle is supplied"
        ∷ "No identification of the discrete Ricci candidate with smooth Ricci curvature is supplied"
        ∷ "No stress-energy convergence authority is supplied"
        ∷ "No smooth Einstein continuity law is supplied"
        ∷ "No BCH convergence theorem, plaquette log branch authority, or uniform holonomy Taylor remainder authority is supplied"
        ∷ []
    ; unsupportedClaims =
        canonicalDiscreteToSmoothEinsteinLimitUnsupportedClaims
    ; unsupportedClaimsAreCanonical =
        refl
    ; nonPromotionBoundary =
        "This receipt is an obligation surface, not a continuum GR theorem"
        ∷ "The exact first missing proof is missingDiscreteToSmoothCurvatureConvergence"
        ∷ "The inherited discrete Bianchi blocker remains missingAdapterNonFlatWitnessForAlignedRequest"
        ∷ "The BCH/holonomy Taylor boundary is ledgered fail-closed and internallyProvedFromCurrentReceipt is false"
        ∷ "No Einstein equation, source-coupled theorem, Clay bridge, or GR/QFT promotion is constructed"
        ∷ []
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    }

discreteToSmoothEinsteinLimitExactFirstMissing :
  DiscreteToSmoothEinsteinLimitReceipt.firstMissing
    canonicalDiscreteToSmoothEinsteinLimitReceipt
  ≡
  missingDiscreteToSmoothCurvatureConvergence
discreteToSmoothEinsteinLimitExactFirstMissing = refl

discreteToSmoothEinsteinLimitStatusIsNonPromoting :
  DiscreteToSmoothEinsteinLimitReceipt.status
    canonicalDiscreteToSmoothEinsteinLimitReceipt
  ≡
  obligationSurfaceOnlyNoPromotion
discreteToSmoothEinsteinLimitStatusIsNonPromoting = refl

discreteToSmoothEinsteinLimitTerminalClaimPromotedFalse :
  DiscreteToSmoothEinsteinLimitReceipt.terminalClaimPromoted
    canonicalDiscreteToSmoothEinsteinLimitReceipt
  ≡
  false
discreteToSmoothEinsteinLimitTerminalClaimPromotedFalse = refl

discreteToSmoothEinsteinLimitInheritedCRTBoundaryOfBoundaryWordIsEmpty :
  DiscreteToSmoothEinsteinLimitReceipt.inheritedCRTBoundaryOfBoundaryWord
    canonicalDiscreteToSmoothEinsteinLimitReceipt
  ≡
  []
discreteToSmoothEinsteinLimitInheritedCRTBoundaryOfBoundaryWordIsEmpty = refl

discreteToSmoothEinsteinLimitInheritedCRTBoundaryOfBoundaryActionIsIdentity :
  DiscreteToSmoothEinsteinLimitReceipt.inheritedCRTBoundaryOfBoundaryAction
    canonicalDiscreteToSmoothEinsteinLimitReceipt
  ≡
  StokesObs.identityCRTBoundaryWordAction
discreteToSmoothEinsteinLimitInheritedCRTBoundaryOfBoundaryActionIsIdentity = refl

discreteToSmoothEinsteinLimitInheritedCRTStokesFirstMissingField :
  DiscreteToSmoothEinsteinLimitReceipt.inheritedCRTDiscreteStokesSpecialisationFirstMissingField
    canonicalDiscreteToSmoothEinsteinLimitReceipt
  ≡
  StokesObs.missingStokesBoundaryWordInterpreterToCRTBoundaryWord
discreteToSmoothEinsteinLimitInheritedCRTStokesFirstMissingField = refl

discreteToSmoothEinsteinLimitInheritedErasingInterpreterNotAccepted :
  DiscreteToSmoothEinsteinLimitReceipt.inheritedErasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation
    canonicalDiscreteToSmoothEinsteinLimitReceipt
  ≡
  false
discreteToSmoothEinsteinLimitInheritedErasingInterpreterNotAccepted = refl

discreteToSmoothEinsteinLimitInheritedFirstSemanticLawAfterTypedInterpreter :
  DiscreteToSmoothEinsteinLimitReceipt.inheritedFirstMissingSemanticLawAfterTypedInterpreter
    canonicalDiscreteToSmoothEinsteinLimitReceipt
  ≡
  StokesObs.missingStokesBoundaryWordInterpreterLawForCRTBoundary
discreteToSmoothEinsteinLimitInheritedFirstSemanticLawAfterTypedInterpreter = refl

discreteToSmoothEinsteinLimitHolonomyTaylorRequestIsCanonical :
  DiscreteToSmoothEinsteinLimitReceipt.holonomyTaylorRicciConvergencePrimitiveRequest
    canonicalDiscreteToSmoothEinsteinLimitReceipt
  ≡
  canonicalHolonomyTaylorRicciConvergencePrimitiveRequest
discreteToSmoothEinsteinLimitHolonomyTaylorRequestIsCanonical = refl

discreteToSmoothEinsteinLimitBCHHolonomyTaylorAuthorityNotInternallyProved :
  DiscreteToSmoothEinsteinLimitReceipt.bchHolonomyTaylorAuthorityInternallyProved
    canonicalDiscreteToSmoothEinsteinLimitReceipt
  ≡
  false
discreteToSmoothEinsteinLimitBCHHolonomyTaylorAuthorityNotInternallyProved =
  refl
