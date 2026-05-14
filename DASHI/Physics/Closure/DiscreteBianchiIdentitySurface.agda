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

record ContractedBianchiPrimitiveBundle : Setω where
  field
    tensorConstructionRequest :
      DET.DiscreteEinsteinTensorConstructionRequestSurface

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
        ∷ "The next bridge is an adapter from prime finite-difference commutation into a non-flat connection/Riemann curvature API"
        ∷ "This surface requests the missing bridge from discrete Riemann antisymmetry through covariant divergence and contraction to the Einstein tensor identity"
        ∷ []
    ; noPromotionBoundary =
        "This module does not inhabit ContractedBianchiPrimitiveBundle"
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
