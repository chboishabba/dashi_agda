module DASHI.Physics.Closure.DiscreteBianchiIdentitySurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (cong; sym)

import DASHI.Physics.BianchiEinsteinAssumptions as BEA
import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.Closure.GRDiscreteBianchiFiniteR as GRB
open import MonsterOntos using (SSP)
import Ontology.GodelLattice as GL
import Ontology.Hecke.FactorVecInstances as FVI

------------------------------------------------------------------------
-- Prime-carrier finite-difference Bianchi surface.
--
-- This is the first inhabited GR non-flat sidecar: finite differences are
-- prime-bump pullbacks on the canonical FactorVec carrier.  The double
-- differences commute because the underlying prime-bump updates commute.
-- The "zero" below is the antisymmetrized double-difference equality, not a
-- promoted covariant contracted Bianchi theorem.

finiteDifferenceΔ :
  {Observable : Set} →
  SSP →
  (GL.FactorVec → Observable) →
  GL.FactorVec →
  Observable
finiteDifferenceΔ p observable carrier =
  observable (FVI.primeBump p carrier)

doubleFiniteDifferenceΔ :
  {Observable : Set} →
  SSP →
  SSP →
  (GL.FactorVec → Observable) →
  GL.FactorVec →
  Observable
doubleFiniteDifferenceΔ p q observable carrier =
  finiteDifferenceΔ p (finiteDifferenceΔ q observable) carrier

finiteDifferencesCommute :
  {Observable : Set} →
  (p q : SSP) →
  (observable : GL.FactorVec → Observable) →
  (carrier : GL.FactorVec) →
  doubleFiniteDifferenceΔ p q observable carrier
  ≡
  doubleFiniteDifferenceΔ q p observable carrier
finiteDifferencesCommute p q observable carrier =
  sym (cong observable (FVI.primeBumpCommutes p q carrier))

AntisymmetrizedDoubleDifferenceZero :
  {Observable : Set} →
  (p q : SSP) →
  (observable : GL.FactorVec → Observable) →
  GL.FactorVec →
  Set
AntisymmetrizedDoubleDifferenceZero p q observable carrier =
  doubleFiniteDifferenceΔ p q observable carrier
  ≡
  doubleFiniteDifferenceΔ q p observable carrier

antisymmetrizedDoubleDifferenceZero :
  {Observable : Set} →
  (p q : SSP) →
  (observable : GL.FactorVec → Observable) →
  (carrier : GL.FactorVec) →
  AntisymmetrizedDoubleDifferenceZero p q observable carrier
antisymmetrizedDoubleDifferenceZero =
  finiteDifferencesCommute

data PrimeCarrierFiniteDifferenceBianchiStatus : Set where
  primeCarrierFiniteDifferenceCommutationProved :
    PrimeCarrierFiniteDifferenceBianchiStatus

record PrimeCarrierFiniteDifferenceBianchiSurface : Set₁ where
  field
    status :
      PrimeCarrierFiniteDifferenceBianchiStatus

    Carrier :
      Set

    Direction :
      Set

    carrierIsFactorVec :
      Carrier
      ≡
      GL.FactorVec

    directionIsSSP :
      Direction
      ≡
      SSP

    finiteDifference :
      {Observable : Set} →
      SSP →
      (GL.FactorVec → Observable) →
      GL.FactorVec →
      Observable

    finiteDifferenceIsPrimeBumpPullback :
      {Observable : Set} →
      (p : SSP) →
      (observable : GL.FactorVec → Observable) →
      (carrier : GL.FactorVec) →
      finiteDifference p observable carrier
      ≡
      observable (FVI.primeBump p carrier)

    doubleDifference :
      {Observable : Set} →
      SSP →
      SSP →
      (GL.FactorVec → Observable) →
      GL.FactorVec →
      Observable

    doubleDifferenceCommutes :
      {Observable : Set} →
      (p q : SSP) →
      (observable : GL.FactorVec → Observable) →
      (carrier : GL.FactorVec) →
      doubleDifference p q observable carrier
      ≡
      doubleDifference q p observable carrier

    antisymmetrizedDoubleDifferenceZeroLaw :
      {Observable : Set} →
      (p q : SSP) →
      (observable : GL.FactorVec → Observable) →
      (carrier : GL.FactorVec) →
      AntisymmetrizedDoubleDifferenceZero p q observable carrier

    proofBoundary :
      List String

canonicalPrimeCarrierFiniteDifferenceBianchiSurface :
  PrimeCarrierFiniteDifferenceBianchiSurface
canonicalPrimeCarrierFiniteDifferenceBianchiSurface =
  record
    { status =
        primeCarrierFiniteDifferenceCommutationProved
    ; Carrier =
        GL.FactorVec
    ; Direction =
        SSP
    ; carrierIsFactorVec =
        refl
    ; directionIsSSP =
        refl
    ; finiteDifference =
        finiteDifferenceΔ
    ; finiteDifferenceIsPrimeBumpPullback =
        λ _ _ _ → refl
    ; doubleDifference =
        doubleFiniteDifferenceΔ
    ; doubleDifferenceCommutes =
        finiteDifferencesCommute
    ; antisymmetrizedDoubleDifferenceZeroLaw =
        antisymmetrizedDoubleDifferenceZero
    ; proofBoundary =
        "Carrier is Ontology.GodelLattice.FactorVec"
        ∷ "Directions are MonsterOntos.SSP prime lanes"
        ∷ "Finite difference is pullback along FVI.primeBump"
        ∷ "Double finite differences commute by FVI.primeBumpCommutes"
        ∷ "Antisymmetrized double-difference zero is an equality of the two double differences"
        ∷ []
    }

primeCarrierFiniteDifferenceSurfaceExactStatus :
  PrimeCarrierFiniteDifferenceBianchiSurface.status
    canonicalPrimeCarrierFiniteDifferenceBianchiSurface
  ≡
  primeCarrierFiniteDifferenceCommutationProved
primeCarrierFiniteDifferenceSurfaceExactStatus = refl

primeCarrierAntisymmetrizedDoubleDifferenceZero :
  {Observable : Set} →
  (p q : SSP) →
  (observable : GL.FactorVec → Observable) →
  (carrier : GL.FactorVec) →
  AntisymmetrizedDoubleDifferenceZero p q observable carrier
primeCarrierAntisymmetrizedDoubleDifferenceZero =
  PrimeCarrierFiniteDifferenceBianchiSurface.antisymmetrizedDoubleDifferenceZeroLaw
    canonicalPrimeCarrierFiniteDifferenceBianchiSurface

------------------------------------------------------------------------
-- Discrete contracted Bianchi request surface.
--
-- The available GR lane exposes a flat Einstein-tensor candidate and several
-- request surfaces.  It does not expose a carrier-internal non-flat Riemann
-- tensor with antisymmetry, a covariant divergence over tensor components, the
-- contraction law needed to descend Bianchi to Ricci/Einstein form, or an
-- inhabited Einstein tensor construction over that same tensor.  This module
-- records that exact boundary without promoting a GR theorem.

data DiscreteBianchiIdentitySurfaceStatus : Set where
  blockedMissingContractedBianchiPrimitives :
    DiscreteBianchiIdentitySurfaceStatus

data DiscreteBianchiIdentityMissingPrimitive : Set where
  missingPrimeDifferenceToRiemannConnectionAdapter :
    DiscreteBianchiIdentityMissingPrimitive
  missingDiscreteRiemannAntisymmetry :
    DiscreteBianchiIdentityMissingPrimitive
  missingCovariantDivergence :
    DiscreteBianchiIdentityMissingPrimitive
  missingBianchiContractionLaw :
    DiscreteBianchiIdentityMissingPrimitive
  missingEinsteinTensorConstruction :
    DiscreteBianchiIdentityMissingPrimitive

canonicalDiscreteBianchiIdentityMissingPrimitives :
  List DiscreteBianchiIdentityMissingPrimitive
canonicalDiscreteBianchiIdentityMissingPrimitives =
  missingPrimeDifferenceToRiemannConnectionAdapter
  ∷ missingDiscreteRiemannAntisymmetry
  ∷ missingCovariantDivergence
  ∷ missingBianchiContractionLaw
  ∷ missingEinsteinTensorConstruction
  ∷ []

data DiscreteBianchiIdentityUnsupportedClaim : Set where
  unsupportedContractedBianchiPromotion :
    DiscreteBianchiIdentityUnsupportedClaim
  unsupportedDivergenceFreeEinsteinTensorClaim :
    DiscreteBianchiIdentityUnsupportedClaim
  unsupportedCurvatureRicciContractionClaim :
    DiscreteBianchiIdentityUnsupportedClaim
  unsupportedDiscreteEinsteinEquationClosureClaim :
    DiscreteBianchiIdentityUnsupportedClaim
  unsupportedGRPromotionClaim :
    DiscreteBianchiIdentityUnsupportedClaim

canonicalDiscreteBianchiIdentityUnsupportedClaims :
  List DiscreteBianchiIdentityUnsupportedClaim
canonicalDiscreteBianchiIdentityUnsupportedClaims =
  unsupportedContractedBianchiPromotion
  ∷ unsupportedDivergenceFreeEinsteinTensorClaim
  ∷ unsupportedCurvatureRicciContractionClaim
  ∷ unsupportedDiscreteEinsteinEquationClosureClaim
  ∷ unsupportedGRPromotionClaim
  ∷ []

------------------------------------------------------------------------
-- Prime finite-difference to Riemann / connection adapter request.
--
-- This is the typed bridge requested by the contracted-Bianchi lane.  The
-- bundle is intentionally conditional on a concrete Einstein-tensor
-- construction request: the current module can supply prime-bump commutation,
-- but it cannot manufacture the target BasePoint / CoordinateIndex alignment,
-- non-flat Γ coefficients, or a Riemann-from-ΔΓ interpretation.

record PrimeDifferenceToRiemannConnectionAdapterBundle
  (target : DET.DiscreteEinsteinTensorConstructionRequestSurface) :
  Setω where
  open DET.DiscreteEinsteinTensorConstructionRequestSurface target
  field
    basePointToFactorVec :
      BasePoint →
      GL.FactorVec

    factorVecToBasePoint :
      GL.FactorVec →
      BasePoint

    coordinateIndexToSSP :
      CoordinateIndex →
      SSP

    sspToCoordinateIndex :
      SSP →
      CoordinateIndex

    ΔMatchesPrimeDifference :
      (observable : GL.FactorVec → Scalar) →
      (carrier : GL.FactorVec) →
      (direction : SSP) →
      Δ
        (λ base → observable (basePointToFactorVec base))
        (factorVecToBasePoint carrier)
        (sspToCoordinateIndex direction)
      ≡
      finiteDifferenceΔ direction observable carrier

    primeCommutatorToRiemannFromΔΓ :
      (observable : GL.FactorVec → Scalar) →
      (rho sigma mu nu : SSP) →
      (carrier : GL.FactorVec) →
      AntisymmetrizedDoubleDifferenceZero rho sigma observable carrier →
      RiemannFromΔΓLaw
        (factorVecToBasePoint carrier)
        (sspToCoordinateIndex rho)
        (sspToCoordinateIndex sigma)
        (sspToCoordinateIndex mu)
        (sspToCoordinateIndex nu)

    adapterNonFlatWitness :
      nonFlatWitness

    adapterBoundary :
      List String

record ConcreteCoordinateIndexSSPAlignment : Set₁ where
  field
    CoordinateIndex :
      Set

    coordinateIndexIsSSP :
      CoordinateIndex
      ≡
      SSP

    coordinateIndexToSSP :
      CoordinateIndex →
      SSP

    sspToCoordinateIndex :
      SSP →
      CoordinateIndex

    coordinateIndexFromSSPRoundTrip :
      (direction : SSP) →
      coordinateIndexToSSP (sspToCoordinateIndex direction)
      ≡
      direction

    sspFromCoordinateIndexRoundTrip :
      (index : CoordinateIndex) →
      sspToCoordinateIndex (coordinateIndexToSSP index)
      ≡
      index

    alignmentBoundary :
      List String

canonicalConcreteCoordinateIndexSSPAlignment :
  ConcreteCoordinateIndexSSPAlignment
canonicalConcreteCoordinateIndexSSPAlignment =
  record
    { CoordinateIndex =
        SSP
    ; coordinateIndexIsSSP =
        refl
    ; coordinateIndexToSSP =
        λ direction → direction
    ; sspToCoordinateIndex =
        λ direction → direction
    ; coordinateIndexFromSSPRoundTrip =
        λ _ → refl
    ; sspFromCoordinateIndexRoundTrip =
        λ _ → refl
    ; alignmentBoundary =
        "Concrete CoordinateIndex/SSP alignment is the identity on MonsterOntos.SSP"
        ∷ "This alignment does not supply a concrete DiscreteEinsteinTensorConstructionRequestSurface"
        ∷ []
    }

canonicalCoordinateIndexSSPAlignmentExact :
  ConcreteCoordinateIndexSSPAlignment.coordinateIndexIsSSP
    canonicalConcreteCoordinateIndexSSPAlignment
  ≡
  refl
canonicalCoordinateIndexSSPAlignmentExact = refl

record PrimeDifferenceToRiemannConcreteAdapterPrerequisiteBundle : Setω where
  field
    alignedConstructionRequest :
      DET.FactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface

    coordinateIndexSSPAlignment :
      ConcreteCoordinateIndexSSPAlignment

    prerequisiteBoundary :
      List String

factorVecSSPAlignedConstructionRequest :
  DET.FactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface
factorVecSSPAlignedConstructionRequest =
  DET.canonicalFactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface

factorVecSSPAlignedTarget :
  DET.DiscreteEinsteinTensorConstructionRequestSurface
factorVecSSPAlignedTarget =
  DET.FactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface.constructionRequest
    factorVecSSPAlignedConstructionRequest

factorVecSSPΔMatchesPrimeDifference :
  (observable : GL.FactorVec → GL.FactorVec) →
  (carrier : GL.FactorVec) →
  (direction : SSP) →
  DET.DiscreteEinsteinTensorConstructionRequestSurface.Δ
    factorVecSSPAlignedTarget
    observable
    carrier
    direction
  ≡
  finiteDifferenceΔ direction observable carrier
factorVecSSPΔMatchesPrimeDifference _ _ _ =
  refl

factorVecSSPPrimeCommutatorToRiemannFromΔΓ :
  (observable : GL.FactorVec → GL.FactorVec) →
  (rho sigma mu nu : SSP) →
  (carrier : GL.FactorVec) →
  AntisymmetrizedDoubleDifferenceZero rho sigma observable carrier →
  DET.DiscreteEinsteinTensorConstructionRequestSurface.RiemannFromΔΓLaw
    factorVecSSPAlignedTarget
    carrier
    rho
    sigma
    mu
    nu
factorVecSSPPrimeCommutatorToRiemannFromΔΓ
  _ _ _ _ _ _ _ =
  λ _ commutator → commutator

data PrimeDifferenceToRiemannConnectionAdapterMissingPrimitive : Set where
  missingFactorVecSSPAlignedConstructionRequest :
    PrimeDifferenceToRiemannConnectionAdapterMissingPrimitive
  missingΔMatchesPrimeDifferenceForAlignedRequest :
    PrimeDifferenceToRiemannConnectionAdapterMissingPrimitive
  missingPrimeCommutatorToRiemannFromΔΓForAlignedRequest :
    PrimeDifferenceToRiemannConnectionAdapterMissingPrimitive
  missingAdapterNonFlatWitnessForAlignedRequest :
    PrimeDifferenceToRiemannConnectionAdapterMissingPrimitive

record FactorVecSSPPrimeDifferenceRiemannAdapterLawSurface : Setω where
  field
    alignedConstructionRequest :
      DET.FactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface

    targetRequest :
      DET.DiscreteEinsteinTensorConstructionRequestSurface

    ΔMatchesPrimeDifference :
      (observable : GL.FactorVec → GL.FactorVec) →
      (carrier : GL.FactorVec) →
      (direction : SSP) →
      DET.DiscreteEinsteinTensorConstructionRequestSurface.Δ
        factorVecSSPAlignedTarget
        observable
        carrier
        direction
      ≡
      finiteDifferenceΔ direction observable carrier

    primeCommutatorToRiemannFromΔΓ :
      (observable : GL.FactorVec → GL.FactorVec) →
      (rho sigma mu nu : SSP) →
      (carrier : GL.FactorVec) →
      AntisymmetrizedDoubleDifferenceZero rho sigma observable carrier →
      DET.DiscreteEinsteinTensorConstructionRequestSurface.RiemannFromΔΓLaw
        factorVecSSPAlignedTarget
        carrier
        rho
        sigma
        mu
        nu

    remainingMissingPrimitive :
      PrimeDifferenceToRiemannConnectionAdapterMissingPrimitive

    remainingMissingPrimitiveIsNonFlatWitness :
      remainingMissingPrimitive
      ≡
      missingAdapterNonFlatWitnessForAlignedRequest

    remainingNonFlatWitnessRequest :
      DET.FactorVecSSPNonFlatConnectionWitnessRequest

    remainingNonFlatWitnessFirstMissing :
      DET.FactorVecSSPNonFlatConnectionWitnessMissingField

    remainingNonFlatWitnessFirstMissingExact :
      remainingNonFlatWitnessFirstMissing
      ≡
      DET.missingFactorVecSSPConnectionCoefficientsDifferFromZero

    lawBoundary :
      List String

data PrimeDifferenceToRiemannConnectionAdapterStatus : Set where
  primeCommutationAvailableAdapterBundleStillMissing :
    PrimeDifferenceToRiemannConnectionAdapterStatus
  coordinateIndexSSPAlignmentAvailableConcreteRequestStillMissing :
    PrimeDifferenceToRiemannConnectionAdapterStatus
  alignedRequestAndAdapterLawsAvailableNonFlatWitnessMissing :
    PrimeDifferenceToRiemannConnectionAdapterStatus

canonicalFactorVecSSPPrimeDifferenceRiemannAdapterLawSurface :
  FactorVecSSPPrimeDifferenceRiemannAdapterLawSurface
canonicalFactorVecSSPPrimeDifferenceRiemannAdapterLawSurface =
  record
    { alignedConstructionRequest =
        factorVecSSPAlignedConstructionRequest
    ; targetRequest =
        factorVecSSPAlignedTarget
    ; ΔMatchesPrimeDifference =
        factorVecSSPΔMatchesPrimeDifference
    ; primeCommutatorToRiemannFromΔΓ =
        factorVecSSPPrimeCommutatorToRiemannFromΔΓ
    ; remainingMissingPrimitive =
        missingAdapterNonFlatWitnessForAlignedRequest
    ; remainingMissingPrimitiveIsNonFlatWitness =
        refl
    ; remainingNonFlatWitnessRequest =
        DET.canonicalFactorVecSSPNonFlatConnectionWitnessRequest
    ; remainingNonFlatWitnessFirstMissing =
        DET.missingFactorVecSSPConnectionCoefficientsDifferFromZero
    ; remainingNonFlatWitnessFirstMissingExact =
        refl
    ; lawBoundary =
        "The aligned target is DET.canonicalFactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface"
        ∷ "ΔMatchesPrimeDifference is definitional because target Δ is FVI.primeBump pullback"
        ∷ "primeCommutatorToRiemannFromΔΓ inhabits the target's commutator-shaped RiemannFromΔΓLaw"
        ∷ "The remaining witness request is DET.canonicalFactorVecSSPNonFlatConnectionWitnessRequest"
        ∷ "This law surface does not inhabit PrimeDifferenceToRiemannConnectionAdapterBundle because adapterNonFlatWitness is still missing"
        ∷ []
    }

record PrimeDifferenceToRiemannConnectionAdapterReceipt : Setω where
  field
    status :
      PrimeDifferenceToRiemannConnectionAdapterStatus

    sourceFiniteDifferenceSurface :
      PrimeCarrierFiniteDifferenceBianchiSurface

    targetRequestSurfaceName :
      String

    adapterBundleName :
      String

    prerequisiteBundleName :
      String

    targetDeltaFieldName :
      String

    targetGammaFieldName :
      String

    targetRiemannFieldName :
      String

    suppliedPrimeCommutation :
      {Observable : Set} →
      (p q : SSP) →
      (observable : GL.FactorVec → Observable) →
      (carrier : GL.FactorVec) →
      doubleFiniteDifferenceΔ p q observable carrier
      ≡
      doubleFiniteDifferenceΔ q p observable carrier

    suppliedAntisymmetrizedZero :
      {Observable : Set} →
      (p q : SSP) →
      (observable : GL.FactorVec → Observable) →
      (carrier : GL.FactorVec) →
      AntisymmetrizedDoubleDifferenceZero p q observable carrier

    suppliedCoordinateIndexSSPAlignment :
      ConcreteCoordinateIndexSSPAlignment

    suppliedAlignedConstructionRequest :
      DET.FactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface

    suppliedAdapterLawSurface :
      FactorVecSSPPrimeDifferenceRiemannAdapterLawSurface

    suppliedNonFlatWitnessRequest :
      DET.FactorVecSSPNonFlatConnectionWitnessRequest

    firstMissingAdapterPrimitive :
      PrimeDifferenceToRiemannConnectionAdapterMissingPrimitive

    firstMissingAdapterPrimitiveIsNonFlatWitness :
      firstMissingAdapterPrimitive
      ≡
      missingAdapterNonFlatWitnessForAlignedRequest

    firstMissingWitnessField :
      DET.FactorVecSSPNonFlatConnectionWitnessMissingField

    firstMissingWitnessFieldIsNonZeroConnectionComponent :
      firstMissingWitnessField
      ≡
      DET.missingFactorVecSSPConnectionCoefficientsDifferFromZero

    firstMissingPrimitive :
      DiscreteBianchiIdentityMissingPrimitive

    firstMissingPrimitiveIsAdapterBundle :
      firstMissingPrimitive
      ≡
      missingPrimeDifferenceToRiemannConnectionAdapter

    adapterBoundary :
      List String

    noPromotionBoundary :
      List String

canonicalPrimeDifferenceToRiemannConnectionAdapterReceipt :
  PrimeDifferenceToRiemannConnectionAdapterReceipt
canonicalPrimeDifferenceToRiemannConnectionAdapterReceipt =
  record
    { status =
        alignedRequestAndAdapterLawsAvailableNonFlatWitnessMissing
    ; sourceFiniteDifferenceSurface =
        canonicalPrimeCarrierFiniteDifferenceBianchiSurface
    ; targetRequestSurfaceName =
        "DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate.DiscreteEinsteinTensorConstructionRequestSurface"
    ; adapterBundleName =
        "DASHI.Physics.Closure.DiscreteBianchiIdentitySurface.PrimeDifferenceToRiemannConnectionAdapterBundle"
    ; prerequisiteBundleName =
        "DASHI.Physics.Closure.DiscreteBianchiIdentitySurface.PrimeDifferenceToRiemannConcreteAdapterPrerequisiteBundle"
    ; targetDeltaFieldName =
        "DiscreteEinsteinTensorConstructionRequestSurface.Δ"
    ; targetGammaFieldName =
        "DiscreteEinsteinTensorConstructionRequestSurface.Γ"
    ; targetRiemannFieldName =
        "DiscreteEinsteinTensorConstructionRequestSurface.Riemann"
    ; suppliedPrimeCommutation =
        finiteDifferencesCommute
    ; suppliedAntisymmetrizedZero =
        antisymmetrizedDoubleDifferenceZero
    ; suppliedCoordinateIndexSSPAlignment =
        canonicalConcreteCoordinateIndexSSPAlignment
    ; suppliedAlignedConstructionRequest =
        factorVecSSPAlignedConstructionRequest
    ; suppliedAdapterLawSurface =
        canonicalFactorVecSSPPrimeDifferenceRiemannAdapterLawSurface
    ; suppliedNonFlatWitnessRequest =
        DET.canonicalFactorVecSSPNonFlatConnectionWitnessRequest
    ; firstMissingAdapterPrimitive =
        missingAdapterNonFlatWitnessForAlignedRequest
    ; firstMissingAdapterPrimitiveIsNonFlatWitness =
        refl
    ; firstMissingWitnessField =
        DET.missingFactorVecSSPConnectionCoefficientsDifferFromZero
    ; firstMissingWitnessFieldIsNonZeroConnectionComponent =
        refl
    ; firstMissingPrimitive =
        missingPrimeDifferenceToRiemannConnectionAdapter
    ; firstMissingPrimitiveIsAdapterBundle =
        refl
    ; adapterBoundary =
        "The source side supplies finiteDifferenceΔ over FactorVec and SSP"
        ∷ "The source side supplies double prime-bump commutation by FVI.primeBumpCommutes"
        ∷ "CoordinateIndex/SSP alignment is concretely inhabited by the identity on SSP"
        ∷ "DET.canonicalFactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface supplies BasePoint = FactorVec and CoordinateIndex = SSP"
        ∷ "factorVecSSPΔMatchesPrimeDifference proves the aligned target Δ is finiteDifferenceΔ"
        ∷ "factorVecSSPPrimeCommutatorToRiemannFromΔΓ proves the target commutator-shaped RiemannFromΔΓLaw"
        ∷ "The exact first remaining adapter primitive is DET.FactorVecSSPNonFlatConnectionWitness"
        ∷ "The exact first witness field is a proof that a Γ component differs from zeroFactorVec"
        ∷ []
    ; noPromotionBoundary =
        "This receipt does not inhabit PrimeDifferenceToRiemannConnectionAdapterBundle for any target"
        ∷ "This receipt does not construct non-flat Γ coefficients"
        ∷ "This receipt does not construct Riemann curvature from Δ and Γ"
        ∷ "This receipt does not prove Ricci contraction, covariant divergence, or contracted Bianchi"
        ∷ []
    }

primeDifferenceAdapterReceiptExactStatus :
  PrimeDifferenceToRiemannConnectionAdapterReceipt.status
    canonicalPrimeDifferenceToRiemannConnectionAdapterReceipt
  ≡
  alignedRequestAndAdapterLawsAvailableNonFlatWitnessMissing
primeDifferenceAdapterReceiptExactStatus = refl

primeDifferenceAdapterReceiptExactFirstAdapterMissing :
  PrimeDifferenceToRiemannConnectionAdapterReceipt.firstMissingAdapterPrimitive
    canonicalPrimeDifferenceToRiemannConnectionAdapterReceipt
  ≡
  missingAdapterNonFlatWitnessForAlignedRequest
primeDifferenceAdapterReceiptExactFirstAdapterMissing = refl

primeDifferenceAdapterReceiptExactFirstMissing :
  PrimeDifferenceToRiemannConnectionAdapterReceipt.firstMissingPrimitive
    canonicalPrimeDifferenceToRiemannConnectionAdapterReceipt
  ≡
  missingPrimeDifferenceToRiemannConnectionAdapter
primeDifferenceAdapterReceiptExactFirstMissing = refl

record ContractedBianchiPrimitiveBundle : Setω where
  field
    tensorConstructionRequest :
      DET.DiscreteEinsteinTensorConstructionRequestSurface

    primeDifferenceToRiemannConnectionAdapter :
      PrimeDifferenceToRiemannConnectionAdapterBundle
        tensorConstructionRequest

    discreteRiemannAntisymmetry :
      Set

    covariantDivergence :
      Set

    contractionLaw :
      Set

    einsteinTensorConstruction :
      Set

    contractedBianchiIdentity :
      Set

    contractedBianchiFromPrimitives :
      discreteRiemannAntisymmetry →
      covariantDivergence →
      contractionLaw →
      einsteinTensorConstruction →
      contractedBianchiIdentity

    bundleBoundary :
      List String

record DiscreteBianchiIdentitySurface : Setω where
  field
    status :
      DiscreteBianchiIdentitySurfaceStatus

    discreteEinsteinTensorDiagnostic :
      DET.DiscreteEinsteinTensorCandidateDiagnostic

    primeCarrierFiniteDifferenceBianchiSurface :
      PrimeCarrierFiniteDifferenceBianchiSurface

    primeDifferenceToRiemannConnectionAdapterReceipt :
      PrimeDifferenceToRiemannConnectionAdapterReceipt

    finiteRBianchiSidecarMissing :
      List GRB.GRDiscreteBianchiFiniteRMissingIngredient

    manifoldLikeAssumptionModule :
      String

    conditionalPrimitiveBundleName :
      String

    exactMissingPrimitives :
      List DiscreteBianchiIdentityMissingPrimitive

    exactMissingPrimitivesAreCanonical :
      exactMissingPrimitives
      ≡
      canonicalDiscreteBianchiIdentityMissingPrimitives

    firstMissingPrimitive :
      DiscreteBianchiIdentityMissingPrimitive

    firstMissingPrimitiveIsPrimeDifferenceAdapter :
      firstMissingPrimitive
      ≡
      missingPrimeDifferenceToRiemannConnectionAdapter

    unsupportedClaims :
      List DiscreteBianchiIdentityUnsupportedClaim

    unsupportedClaimsAreCanonical :
      unsupportedClaims
      ≡
      canonicalDiscreteBianchiIdentityUnsupportedClaims

    requestBoundary :
      List String

    noPromotionBoundary :
      List String

canonicalDiscreteBianchiIdentitySurface :
  DiscreteBianchiIdentitySurface
canonicalDiscreteBianchiIdentitySurface =
  record
    { status =
        blockedMissingContractedBianchiPrimitives
    ; discreteEinsteinTensorDiagnostic =
        DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; primeCarrierFiniteDifferenceBianchiSurface =
        canonicalPrimeCarrierFiniteDifferenceBianchiSurface
    ; primeDifferenceToRiemannConnectionAdapterReceipt =
        canonicalPrimeDifferenceToRiemannConnectionAdapterReceipt
    ; finiteRBianchiSidecarMissing =
        GRB.canonicalGRDiscreteBianchiFiniteRMissingIngredients
    ; manifoldLikeAssumptionModule =
        "DASHI.Physics.BianchiEinsteinAssumptions.DiscreteManifoldLike"
    ; conditionalPrimitiveBundleName =
        "DASHI.Physics.Closure.DiscreteBianchiIdentitySurface.ContractedBianchiPrimitiveBundle"
    ; exactMissingPrimitives =
        canonicalDiscreteBianchiIdentityMissingPrimitives
    ; exactMissingPrimitivesAreCanonical =
        refl
    ; firstMissingPrimitive =
        missingPrimeDifferenceToRiemannConnectionAdapter
    ; firstMissingPrimitiveIsPrimeDifferenceAdapter =
        refl
    ; unsupportedClaims =
        canonicalDiscreteBianchiIdentityUnsupportedClaims
    ; unsupportedClaimsAreCanonical =
        refl
    ; requestBoundary =
        "Prime-carrier finite differences now commute on FactorVec by FVI.primeBumpCommutes"
        ∷ "Antisymmetrized double-difference zero is typed as equality of double prime-bump pullbacks"
        ∷ "DiscreteEinsteinTensorConstructionRequestSurface names Riemann, Ricci, scalar curvature, and Einstein tensor construction fields"
        ∷ "GRDiscreteBianchiFiniteR still records missing finite-r Bianchi, metric contraction, and stress-energy compatibility ingredients"
        ∷ "BianchiEinsteinAssumptions exposes Div G == zeroS as an assumption-level gate, not as a derivation from Riemann antisymmetry"
        ∷ "PrimeDifferenceToRiemannConnectionAdapterBundle is now the typed request for a non-flat connection/Riemann adapter"
        ∷ "This surface requests the missing bridge from discrete Riemann antisymmetry through covariant divergence and contraction to the Einstein tensor identity"
        ∷ []
    ; noPromotionBoundary =
        "This module does not inhabit ContractedBianchiPrimitiveBundle"
        ∷ "This module does not inhabit PrimeDifferenceToRiemannConnectionAdapterBundle for any tensor request target"
        ∷ "This module does not construct a non-flat connection from prime finite differences"
        ∷ "This module does not construct a discrete Riemann antisymmetry proof"
        ∷ "This module does not construct a covariant divergence operator"
        ∷ "This module does not prove the Bianchi contraction law"
        ∷ "This module does not construct an inhabited non-flat Einstein tensor law"
        ∷ "This module does not promote GR, Einstein equations, or GR/QFT closure"
        ∷ []
    }

discreteBianchiIdentitySurfaceExactStatus :
  DiscreteBianchiIdentitySurface.status
    canonicalDiscreteBianchiIdentitySurface
  ≡
  blockedMissingContractedBianchiPrimitives
discreteBianchiIdentitySurfaceExactStatus = refl

discreteBianchiIdentitySurfaceExactFirstMissing :
  DiscreteBianchiIdentitySurface.firstMissingPrimitive
    canonicalDiscreteBianchiIdentitySurface
  ≡
  missingPrimeDifferenceToRiemannConnectionAdapter
discreteBianchiIdentitySurfaceExactFirstMissing = refl

discreteBianchiIdentitySurfaceExactMissingPrimitives :
  DiscreteBianchiIdentitySurface.exactMissingPrimitives
    canonicalDiscreteBianchiIdentitySurface
  ≡
  canonicalDiscreteBianchiIdentityMissingPrimitives
discreteBianchiIdentitySurfaceExactMissingPrimitives = refl
