module DASHI.Physics.Closure.DiscreteBianchiIdentityReceipt where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT as DCRT
import DASHI.Physics.Closure.DiscreteBianchiIdentitySurface as DBIS
import DASHI.Physics.Closure.GRDiscreteBianchiFiniteR as GRBianchi
import DASHI.Physics.Closure.GRDiscreteRicciCandidateFromCurvature as Ricci
import DASHI.Physics.Closure.DiscreteStokesBianchiObstruction as StokesObs

------------------------------------------------------------------------
-- Discrete Bianchi identity receipt candidate.
--
-- This is the first surface after the GR discrete Ricci candidate.  It
-- consumes the landed connection/Ricci candidate shapes and records that the
-- Bianchi identity proof itself is still the first missing field.  It is not a
-- Bianchi proof, an Einstein-equation proof, source coupling, or continuum GR
-- closure receipt.

data DiscreteBianchiIdentityReceiptStatus : Set where
  candidateObligationOnly :
    DiscreteBianchiIdentityReceiptStatus

data DiscreteBianchiIdentityReceiptUnsupportedClaim : Set where
  unsupportedBianchiIdentityProofClaim :
    DiscreteBianchiIdentityReceiptUnsupportedClaim
  unsupportedEinsteinEquationClaim :
    DiscreteBianchiIdentityReceiptUnsupportedClaim
  unsupportedStressEnergySourceCouplingClaim :
    DiscreteBianchiIdentityReceiptUnsupportedClaim
  unsupportedContinuumGRClosureClaim :
    DiscreteBianchiIdentityReceiptUnsupportedClaim

canonicalDiscreteBianchiIdentityReceiptUnsupportedClaims :
  List DiscreteBianchiIdentityReceiptUnsupportedClaim
canonicalDiscreteBianchiIdentityReceiptUnsupportedClaims =
  unsupportedBianchiIdentityProofClaim
  ∷ unsupportedEinsteinEquationClaim
  ∷ unsupportedStressEnergySourceCouplingClaim
  ∷ unsupportedContinuumGRClosureClaim
  ∷ []

record DiscreteBianchiIdentityReceipt : Set₁ where
  field
    status :
      DiscreteBianchiIdentityReceiptStatus

    discreteConnectionCandidate :
      DCRT.DiscreteConnectionCandidateFromCRT

    discreteConnectionCandidateIsCanonical :
      discreteConnectionCandidate
      ≡
      DCRT.canonicalDiscreteConnectionCandidateFromCRT

    discreteConnectionDiagnostic :
      DCRT.DiscreteConnectionCandidateFromCRTDiagnostic

    discreteConnectionDiagnosticIsCanonical :
      discreteConnectionDiagnostic
      ≡
      DCRT.canonicalDiscreteConnectionCandidateFromCRTDiagnostic

    discreteRicciCandidate :
      Ricci.GRDiscreteRicciCandidateFromCurvature

    discreteRicciCandidateIsCanonical :
      discreteRicciCandidate
      ≡
      Ricci.canonicalGRDiscreteRicciCandidateFromCurvature

    discreteStokesBianchiObstruction :
      StokesObs.DiscreteStokesBianchiObstruction

    discreteStokesBianchiObstructionIsCanonical :
      discreteStokesBianchiObstruction
      ≡
      StokesObs.canonicalDiscreteStokesBianchiObstruction

    discreteStokesBianchiFirstMissing :
      StokesObs.DiscreteStokesBianchiMissingPrimitive

    discreteStokesBianchiFirstMissingIsBoundaryWordToHolonomyAction :
      discreteStokesBianchiFirstMissing
      ≡
      StokesObs.missingDiscreteStokesSpecialisationToCRTConnection

    crtDiscreteStokesSpecialisationFirstMissingField :
      StokesObs.CRTDiscreteStokesSpecialisationMissingField

    crtDiscreteStokesSpecialisationFirstMissingFieldIsBoundaryWordInterpreter :
      crtDiscreteStokesSpecialisationFirstMissingField
      ≡
      StokesObs.missingStokesBoundaryWordInterpreterToCRTBoundaryWord

    erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation :
      Bool

    erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisationIsFalse :
      erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation
      ≡
      false

    firstMissingSemanticLawAfterTypedInterpreter :
      StokesObs.CRTDiscreteStokesSpecialisationMissingField

    firstMissingSemanticLawAfterTypedInterpreterIsBoundaryInterpreterLaw :
      firstMissingSemanticLawAfterTypedInterpreter
      ≡
      StokesObs.missingStokesBoundaryWordInterpreterLawForCRTBoundary

    exactCRTDiscreteStokesSpecialisationMissingFields :
      List StokesObs.CRTDiscreteStokesSpecialisationMissingField

    exactCRTDiscreteStokesSpecialisationMissingFieldsAreCanonical :
      exactCRTDiscreteStokesSpecialisationMissingFields
      ≡
      StokesObs.canonicalCRTDiscreteStokesSpecialisationMissingFields

    crtBoundaryOfBoundaryCarrier :
      StokesObs.CRTMonodromyBoundaryOfBoundaryCarrier

    crtBoundaryOfBoundaryCarrierIsCanonical :
      crtBoundaryOfBoundaryCarrier
      ≡
      StokesObs.canonicalCRTMonodromyBoundaryOfBoundaryCarrier

    crtBoundaryOfBoundaryWord :
      List StokesObs.CRTMonodromy1Edge

    crtBoundaryOfBoundaryWordIsEmpty :
      crtBoundaryOfBoundaryWord ≡ []

    crtBoundaryWordToHolonomyTransport :
      StokesObs.CRTBoundaryWordToHolonomyTransport

    crtBoundaryWordToHolonomyTransportIsCanonical :
      crtBoundaryWordToHolonomyTransport
      ≡
      StokesObs.canonicalCRTBoundaryWordToHolonomyTransport

    crtBoundaryWordHolonomyTraceHomomorphism :
      StokesObs.CRTBoundaryWordHolonomyTraceHomomorphism

    crtBoundaryWordHolonomyTraceHomomorphismIsCanonical :
      crtBoundaryWordHolonomyTraceHomomorphism
      ≡
      StokesObs.canonicalCRTBoundaryWordHolonomyTraceHomomorphism

    nativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism :
      StokesObs.NativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism

    nativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphismIsCanonical :
      nativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism
      ≡
      StokesObs.canonicalNativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism

    localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingRequestName :
      String

    localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingDerivesNativeRealization :
      Bool

    localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingDerivesNativeRealizationIsTrue :
      localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingDerivesNativeRealization
      ≡
      true

    genericBoundaryEdgeLocalRealizationInhabitedFromArbitraryInterface :
      Bool

    genericBoundaryEdgeLocalRealizationInhabitedFromArbitraryInterfaceIsFalse :
      genericBoundaryEdgeLocalRealizationInhabitedFromArbitraryInterface
      ≡
      false

    nonErasingStokesBoundaryWordInterpreterPrimitiveRequestName :
      String

    localBoundaryWordAtDepthOpaquePrimitiveRequestTypeName :
      String

    crtBoundaryOfBoundaryAction :
      StokesObs.CRTBoundaryWordAction

    crtBoundaryOfBoundaryActionIsIdentity :
      crtBoundaryOfBoundaryAction
      ≡
      StokesObs.identityCRTBoundaryWordAction

    primeFiniteDifferenceBianchiSurface :
      DBIS.PrimeCarrierFiniteDifferenceBianchiSurface

    primeFiniteDifferenceBianchiSurfaceIsCanonical :
      primeFiniteDifferenceBianchiSurface
      ≡
      DBIS.canonicalPrimeCarrierFiniteDifferenceBianchiSurface

    primeDifferenceAdapterStatus :
      DBIS.PrimeDifferenceToRiemannConnectionAdapterStatus

    primeDifferenceAdapterStatusIsNonFlatWitnessMissing :
      primeDifferenceAdapterStatus
      ≡
      DBIS.alignedRequestAndAdapterLawsAvailableNonFlatWitnessMissing

    exactPrimeDifferenceAdapterRemainingPrimitive :
      DBIS.PrimeDifferenceToRiemannConnectionAdapterMissingPrimitive

    exactPrimeDifferenceAdapterRemainingPrimitiveIsNonFlatWitness :
      exactPrimeDifferenceAdapterRemainingPrimitive
      ≡
      DBIS.missingAdapterNonFlatWitnessForAlignedRequest

    contractedBianchiSurfaceStatus :
      DBIS.DiscreteBianchiIdentitySurfaceStatus

    contractedBianchiSurfaceStatusIsBlocked :
      contractedBianchiSurfaceStatus
      ≡
      DBIS.blockedMissingContractedBianchiPrimitives

    contractedBianchiFirstMissingPrimitive :
      DBIS.DiscreteBianchiIdentityMissingPrimitive

    contractedBianchiFirstMissingPrimitiveIsAdapterBundle :
      contractedBianchiFirstMissingPrimitive
      ≡
      DBIS.missingPrimeDifferenceToRiemannConnectionAdapter

    inheritedRicciFirstMissing :
      Ricci.GRDiscreteRicciCandidateFirstMissing

    inheritedRicciFirstMissingIsBianchiIdentityProof :
      inheritedRicciFirstMissing
      ≡
      Ricci.missingBianchiIdentityProof

    firstMissing :
      Ricci.GRDiscreteRicciCandidateFirstMissing

    firstMissingIsBianchiIdentityProof :
      firstMissing
      ≡
      Ricci.missingBianchiIdentityProof

    finiteRBianchiMissingIngredients :
      List GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    finiteRBianchiMissingIngredientsAreCanonical :
      finiteRBianchiMissingIngredients
      ≡
      GRBianchi.canonicalGRDiscreteBianchiFiniteRMissingIngredients

    receiptScope :
      List String

    missingSurface :
      List String

    unsupportedClaims :
      List DiscreteBianchiIdentityReceiptUnsupportedClaim

    unsupportedClaimsAreCanonical :
      unsupportedClaims
      ≡
      canonicalDiscreteBianchiIdentityReceiptUnsupportedClaims

    nonPromotionBoundary :
      List String

canonicalDiscreteBianchiIdentityReceipt :
  DiscreteBianchiIdentityReceipt
canonicalDiscreteBianchiIdentityReceipt =
  record
    { status =
        candidateObligationOnly
    ; discreteConnectionCandidate =
        DCRT.canonicalDiscreteConnectionCandidateFromCRT
    ; discreteConnectionCandidateIsCanonical =
        refl
    ; discreteConnectionDiagnostic =
        DCRT.canonicalDiscreteConnectionCandidateFromCRTDiagnostic
    ; discreteConnectionDiagnosticIsCanonical =
        refl
    ; discreteRicciCandidate =
        Ricci.canonicalGRDiscreteRicciCandidateFromCurvature
    ; discreteRicciCandidateIsCanonical =
        refl
    ; discreteStokesBianchiObstruction =
        StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; discreteStokesBianchiObstructionIsCanonical =
        refl
    ; discreteStokesBianchiFirstMissing =
        StokesObs.DiscreteStokesBianchiObstruction.firstMissingPrimitive
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; discreteStokesBianchiFirstMissingIsBoundaryWordToHolonomyAction =
        refl
    ; crtDiscreteStokesSpecialisationFirstMissingField =
        StokesObs.DiscreteStokesBianchiObstruction.crtDiscreteStokesSpecialisationFirstMissingField
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; crtDiscreteStokesSpecialisationFirstMissingFieldIsBoundaryWordInterpreter =
        refl
    ; erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation =
        StokesObs.DiscreteStokesBianchiObstruction.erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisationIsFalse =
        refl
    ; firstMissingSemanticLawAfterTypedInterpreter =
        StokesObs.DiscreteStokesBianchiObstruction.firstMissingSemanticLawAfterTypedInterpreter
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; firstMissingSemanticLawAfterTypedInterpreterIsBoundaryInterpreterLaw =
        refl
    ; exactCRTDiscreteStokesSpecialisationMissingFields =
        StokesObs.DiscreteStokesBianchiObstruction.exactCRTDiscreteStokesSpecialisationMissingFields
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; exactCRTDiscreteStokesSpecialisationMissingFieldsAreCanonical =
        refl
    ; crtBoundaryOfBoundaryCarrier =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryOfBoundaryCarrier
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; crtBoundaryOfBoundaryCarrierIsCanonical =
        refl
    ; crtBoundaryOfBoundaryWord =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryOfBoundaryWord
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; crtBoundaryOfBoundaryWordIsEmpty =
        refl
    ; crtBoundaryWordToHolonomyTransport =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryWordToHolonomyTransport
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; crtBoundaryWordToHolonomyTransportIsCanonical =
        refl
    ; crtBoundaryWordHolonomyTraceHomomorphism =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryWordHolonomyTraceHomomorphism
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; crtBoundaryWordHolonomyTraceHomomorphismIsCanonical =
        refl
    ; nativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism =
        StokesObs.DiscreteStokesBianchiObstruction.nativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; nativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphismIsCanonical =
        refl
    ; localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingRequestName =
        StokesObs.DiscreteStokesBianchiObstruction.localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingRequestName
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingDerivesNativeRealization =
        StokesObs.DiscreteStokesBianchiObstruction.localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingDerivesNativeRealization
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingDerivesNativeRealizationIsTrue =
        refl
    ; genericBoundaryEdgeLocalRealizationInhabitedFromArbitraryInterface =
        StokesObs.DiscreteStokesBianchiObstruction.genericBoundaryEdgeLocalRealizationInhabitedFromArbitraryInterface
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; genericBoundaryEdgeLocalRealizationInhabitedFromArbitraryInterfaceIsFalse =
        refl
    ; nonErasingStokesBoundaryWordInterpreterPrimitiveRequestName =
        StokesObs.DiscreteStokesBianchiObstruction.nonErasingStokesBoundaryWordInterpreterPrimitiveRequestName
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; localBoundaryWordAtDepthOpaquePrimitiveRequestTypeName =
        StokesObs.DiscreteStokesBianchiObstruction.localBoundaryWordAtDepthOpaquePrimitiveRequestTypeName
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; crtBoundaryOfBoundaryAction =
        StokesObs.DiscreteStokesBianchiObstruction.crtBoundaryOfBoundaryAction
          StokesObs.canonicalDiscreteStokesBianchiObstruction
    ; crtBoundaryOfBoundaryActionIsIdentity =
        refl
    ; primeFiniteDifferenceBianchiSurface =
        DBIS.canonicalPrimeCarrierFiniteDifferenceBianchiSurface
    ; primeFiniteDifferenceBianchiSurfaceIsCanonical =
        refl
    ; primeDifferenceAdapterStatus =
        DBIS.alignedRequestAndAdapterLawsAvailableNonFlatWitnessMissing
    ; primeDifferenceAdapterStatusIsNonFlatWitnessMissing =
        refl
    ; exactPrimeDifferenceAdapterRemainingPrimitive =
        DBIS.PrimeDifferenceToRiemannConnectionAdapterReceipt.firstMissingAdapterPrimitive
          DBIS.canonicalPrimeDifferenceToRiemannConnectionAdapterReceipt
    ; exactPrimeDifferenceAdapterRemainingPrimitiveIsNonFlatWitness =
        refl
    ; contractedBianchiSurfaceStatus =
        DBIS.blockedMissingContractedBianchiPrimitives
    ; contractedBianchiSurfaceStatusIsBlocked =
        refl
    ; contractedBianchiFirstMissingPrimitive =
        DBIS.DiscreteBianchiIdentitySurface.firstMissingPrimitive
          DBIS.canonicalDiscreteBianchiIdentitySurface
    ; contractedBianchiFirstMissingPrimitiveIsAdapterBundle =
        refl
    ; inheritedRicciFirstMissing =
        Ricci.GRDiscreteRicciCandidateFromCurvature.firstMissing
          Ricci.canonicalGRDiscreteRicciCandidateFromCurvature
    ; inheritedRicciFirstMissingIsBianchiIdentityProof =
        refl
    ; firstMissing =
        Ricci.missingBianchiIdentityProof
    ; firstMissingIsBianchiIdentityProof =
        refl
    ; finiteRBianchiMissingIngredients =
        GRBianchi.canonicalGRDiscreteBianchiFiniteRMissingIngredients
    ; finiteRBianchiMissingIngredientsAreCanonical =
        refl
    ; receiptScope =
        "Consumes DiscreteConnectionCandidateFromCRT as a typed CRT-monodromy connection candidate"
        ∷ "Consumes DiscreteConnectionCandidateFromCRTDiagnostic as the inherited diagnostic boundary"
        ∷ "Consumes GRDiscreteRicciCandidateFromCurvature as the typed Ricci candidate shape"
        ∷ "Consumes DiscreteStokesBianchiObstruction as the exact GR Stokes-to-Bianchi missing-primitive surface"
        ∷ "Consumes DiscreteBianchiIdentitySurface prime finite-difference commutation and aligned adapter-law receipt"
        ∷ "Records the next obligation surface as a discrete Bianchi identity proof"
        ∷ []
    ; missingSurface =
        "missingBianchiIdentityProof is the first missing field"
        ∷ "BoundaryOfBoundaryZeroForCRTMonodromy is inhabited as a formal CRT carrier word in the Stokes route"
        ∷ "BoundaryWordToCRTHolonomyAction is inhabited as a formal CRT edge/action/empty-word transport"
        ∷ "The CRT-side shell word has a canonical holonomy trace homomorphism preserving list concatenation"
        ∷ "NativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism is inhabited for P2/P3/J shell labels"
        ∷ "LocalBoundaryEdgeLabelGenericBoundaryEdgeEmbedding is the exact request that would realize generic shell labels inside arbitrary local BoundaryWordAtDepth labels"
        ∷ "DiscreteStokesSpecialisationToCRTConnection is now the sharpened first missing theorem for the Stokes route"
        ∷ "A typed erasing boundary-word interpreter exists, but it is not accepted as a CRT Stokes specialisation"
        ∷ "NonErasingStokesBoundaryWordInterpreterPrimitiveRequest is the exact typed request because local BoundaryWordAtDepth is opaque"
        ∷ "The exact first semantic law after that typed fallback is missingStokesBoundaryWordInterpreterLawForCRTBoundary"
        ∷ "missingAdapterNonFlatWitnessForAlignedRequest is the sharpened remaining primitive after the FactorVec/SSP prime-difference adapter laws"
        ∷ "missingPrimeDifferenceToRiemannConnectionAdapter remains the contracted-Bianchi surface first missing primitive"
        ∷ "No covariant cyclic-sum or exterior-derivative expression is supplied for the candidate curvature"
        ∷ "No Jacobi-to-Bianchi bridge is supplied for the candidate connection"
        ∷ "No contracted Bianchi identity, Einstein tensor law, source coupling, or continuum limit is supplied"
        ∷ []
    ; unsupportedClaims =
        canonicalDiscreteBianchiIdentityReceiptUnsupportedClaims
    ; unsupportedClaimsAreCanonical =
        refl
    ; nonPromotionBoundary =
        "This receipt is candidate-shape only"
        ∷ "It does not prove the discrete Bianchi identity"
        ∷ "It does not claim Einstein equations, Bianchi closure, source coupling, or continuum GR closure"
        ∷ []
    }

discreteBianchiIdentityReceiptStatusIsCandidateOnly :
  DiscreteBianchiIdentityReceipt.status
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  candidateObligationOnly
discreteBianchiIdentityReceiptStatusIsCandidateOnly = refl

discreteBianchiIdentityReceiptFirstMissing :
  DiscreteBianchiIdentityReceipt.firstMissing
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  Ricci.missingBianchiIdentityProof
discreteBianchiIdentityReceiptFirstMissing = refl

discreteBianchiIdentityReceiptConsumesRicciCandidate :
  DiscreteBianchiIdentityReceipt.discreteRicciCandidate
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  Ricci.canonicalGRDiscreteRicciCandidateFromCurvature
discreteBianchiIdentityReceiptConsumesRicciCandidate = refl

discreteBianchiIdentityReceiptConsumesStokesObstruction :
  DiscreteBianchiIdentityReceipt.discreteStokesBianchiObstruction
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  StokesObs.canonicalDiscreteStokesBianchiObstruction
discreteBianchiIdentityReceiptConsumesStokesObstruction = refl

discreteBianchiIdentityReceiptStokesFirstMissing :
  DiscreteBianchiIdentityReceipt.discreteStokesBianchiFirstMissing
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  StokesObs.missingDiscreteStokesSpecialisationToCRTConnection
discreteBianchiIdentityReceiptStokesFirstMissing = refl

discreteBianchiIdentityReceiptCRTStokesFirstMissingField :
  DiscreteBianchiIdentityReceipt.crtDiscreteStokesSpecialisationFirstMissingField
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  StokesObs.missingStokesBoundaryWordInterpreterToCRTBoundaryWord
discreteBianchiIdentityReceiptCRTStokesFirstMissingField = refl

discreteBianchiIdentityReceiptErasingInterpreterNotAccepted :
  DiscreteBianchiIdentityReceipt.erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  false
discreteBianchiIdentityReceiptErasingInterpreterNotAccepted = refl

discreteBianchiIdentityReceiptFirstSemanticLawAfterTypedInterpreter :
  DiscreteBianchiIdentityReceipt.firstMissingSemanticLawAfterTypedInterpreter
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  StokesObs.missingStokesBoundaryWordInterpreterLawForCRTBoundary
discreteBianchiIdentityReceiptFirstSemanticLawAfterTypedInterpreter = refl

discreteBianchiIdentityReceiptCRTBoundaryOfBoundaryWordIsEmpty :
  DiscreteBianchiIdentityReceipt.crtBoundaryOfBoundaryWord
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  []
discreteBianchiIdentityReceiptCRTBoundaryOfBoundaryWordIsEmpty = refl

discreteBianchiIdentityReceiptCRTBoundaryOfBoundaryActionIsIdentity :
  DiscreteBianchiIdentityReceipt.crtBoundaryOfBoundaryAction
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  StokesObs.identityCRTBoundaryWordAction
discreteBianchiIdentityReceiptCRTBoundaryOfBoundaryActionIsIdentity = refl

discreteBianchiIdentityReceiptNativeGenericBoundaryEdgeIsomorphismIsCanonical :
  DiscreteBianchiIdentityReceipt.nativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  StokesObs.canonicalNativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism
discreteBianchiIdentityReceiptNativeGenericBoundaryEdgeIsomorphismIsCanonical =
  refl

discreteBianchiIdentityReceiptGenericBoundaryEdgeLocalRealizationStillBlocked :
  DiscreteBianchiIdentityReceipt.genericBoundaryEdgeLocalRealizationInhabitedFromArbitraryInterface
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  false
discreteBianchiIdentityReceiptGenericBoundaryEdgeLocalRealizationStillBlocked =
  refl

discreteBianchiIdentityReceiptPrimeAdapterRemainingPrimitive :
  DiscreteBianchiIdentityReceipt.exactPrimeDifferenceAdapterRemainingPrimitive
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  DBIS.missingAdapterNonFlatWitnessForAlignedRequest
discreteBianchiIdentityReceiptPrimeAdapterRemainingPrimitive = refl

discreteBianchiIdentityReceiptContractedFirstMissing :
  DiscreteBianchiIdentityReceipt.contractedBianchiFirstMissingPrimitive
    canonicalDiscreteBianchiIdentityReceipt
  ≡
  DBIS.missingPrimeDifferenceToRiemannConnectionAdapter
discreteBianchiIdentityReceiptContractedFirstMissing = refl
