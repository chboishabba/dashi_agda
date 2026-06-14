module DASHI.Foundations.PhysicsLinearAnalysisParity where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)

open import DASHI.Foundations.RealAnalysisAxioms

------------------------------------------------------------------------
-- Fail-closed PhysLean parity surface for linear algebra and analysis.
--
-- This module deliberately exposes names and receipts, not local promotion
-- proofs.  It is a parity layer over the smaller real-analysis axiom socket.
-- Anything that would require a serious linear algebra, spectral theory, or
-- ODE development is represented as a named authority boundary and is marked
-- false in the canonical receipt below.

data ScalarDiscipline : Set where
  realScalars :
    ScalarDiscipline

  complexScalarsExternal :
    ScalarDiscipline

record ScalarAuthoritySocket : Set₁ where
  field
    scalarDiscipline :
      ScalarDiscipline

    scalarCarrier :
      Set

    scalarZero scalarOne :
      scalarCarrier

    scalarAdd scalarMul scalarSub :
      scalarCarrier →
      scalarCarrier →
      scalarCarrier

    scalarNeg scalarAbs :
      scalarCarrier →
      scalarCarrier

    scalarFieldLawsAuthority :
      Set

    scalarOrderOrModulusAuthority :
      Set

    scalarCompletenessAuthority :
      Set

open ScalarAuthoritySocket public

canonicalRealScalarAuthoritySocket :
  ScalarAuthoritySocket
canonicalRealScalarAuthoritySocket =
  record
    { scalarDiscipline =
        realScalars
    ; scalarCarrier =
        ℝ
    ; scalarZero =
        0ℝ
    ; scalarOne =
        1ℝ
    ; scalarAdd =
        _+ℝ_
    ; scalarMul =
        _*ℝ_
    ; scalarSub =
        _-ℝ_
    ; scalarNeg =
        -ℝ_
    ; scalarAbs =
        absℝ
    ; scalarFieldLawsAuthority =
        RealScalarSocket.realFieldLawsAxiom canonicalRealScalarSocket
    ; scalarOrderOrModulusAuthority =
        RealScalarSocket.realOrderLawsAxiom canonicalRealScalarSocket
    ; scalarCompletenessAuthority =
        RealScalarSocket.realCompletenessLawsAxiom canonicalRealScalarSocket
    }

record VectorSpace
  (ℓ : Level)
  (S : ScalarAuthoritySocket) :
  Set (lsuc ℓ) where
  field
    Carrier :
      Set ℓ

    zero :
      Carrier

    _+_ _-_ :
      Carrier →
      Carrier →
      Carrier

    scalarMul :
      ScalarAuthoritySocket.scalarCarrier S →
      Carrier →
      Carrier

    vectorSpaceLawsAuthority :
      Set ℓ

open VectorSpace public

record FiniteDimensionalVectorSpace
  (ℓ : Level)
  (S : ScalarAuthoritySocket) :
  Set (lsuc ℓ) where
  field
    vectorSpace :
      VectorSpace ℓ S

    dimension :
      ℕ

    basis :
      List (VectorSpace.Carrier vectorSpace)

    basisHasDimensionAuthority :
      Set ℓ

    basisSpansAuthority :
      Set ℓ

    basisLinearIndependentAuthority :
      Set ℓ

open FiniteDimensionalVectorSpace public

record NormedVectorSpace
  (ℓ : Level) :
  Set (lsuc ℓ) where
  field
    normedSpace :
      NormedSpace ℓ

    vectorSpaceOverReals :
      VectorSpace ℓ canonicalRealScalarAuthoritySocket

    normedCarrierMatchesVectorCarrier :
      NormedSpace.Carrier normedSpace
      ≡
      VectorSpace.Carrier vectorSpaceOverReals

    normedOperationsMatchAuthority :
      Set ℓ

open NormedVectorSpace public

record InnerProductSpace
  (ℓ : Level) :
  Set (lsuc ℓ) where
  field
    normedVectorSpace :
      NormedVectorSpace ℓ

    innerProduct :
      NormedSpace.Carrier (NormedVectorSpace.normedSpace normedVectorSpace) →
      NormedSpace.Carrier (NormedVectorSpace.normedSpace normedVectorSpace) →
      ℝ

    innerProductLinearityAuthority :
      Set ℓ

    innerProductSymmetryAuthority :
      Set ℓ

    innerProductPositiveDefiniteAuthority :
      Set ℓ

    normInducedByInnerProductAuthority :
      Set ℓ

open InnerProductSpace public

record HilbertSpace
  (ℓ : Level) :
  Set (lsuc ℓ) where
  field
    innerProductSpace :
      InnerProductSpace ℓ

    banachSpace :
      BanachSpace ℓ

    banachNormedSpaceMatches :
      BanachSpace.normedSpace banachSpace
      ≡
      NormedVectorSpace.normedSpace
        (InnerProductSpace.normedVectorSpace innerProductSpace)

    hilbertCompletenessAuthority :
      Set ℓ

open HilbertSpace public

postulate
  TensorProductCarrier :
    ∀ {ℓ₁ ℓ₂}
    (V : VectorSpace ℓ₁ canonicalRealScalarAuthoritySocket)
    (W : VectorSpace ℓ₂ canonicalRealScalarAuthoritySocket) →
    Set (ℓ₁ ⊔ ℓ₂)

  tensorPure :
    ∀ {ℓ₁ ℓ₂}
    {V : VectorSpace ℓ₁ canonicalRealScalarAuthoritySocket}
    {W : VectorSpace ℓ₂ canonicalRealScalarAuthoritySocket} →
    VectorSpace.Carrier V →
    VectorSpace.Carrier W →
    TensorProductCarrier V W

record TensorProductSpace
  {ℓ₁ ℓ₂ : Level}
  (V : VectorSpace ℓ₁ canonicalRealScalarAuthoritySocket)
  (W : VectorSpace ℓ₂ canonicalRealScalarAuthoritySocket) :
  Set (lsuc (lsuc (ℓ₁ ⊔ ℓ₂))) where
  field
    tensorCarrier :
      Set (ℓ₁ ⊔ ℓ₂)

    tensorCarrierIsAuthorityCarrier :
      tensorCarrier
      ≡
      TensorProductCarrier V W

    pureTensor :
      VectorSpace.Carrier V →
      VectorSpace.Carrier W →
      tensorCarrier

    tensorBilinearAuthority :
      Set (ℓ₁ ⊔ ℓ₂)

    tensorUniversalPropertyAuthority :
      Set (lsuc (ℓ₁ ⊔ ℓ₂))

open TensorProductSpace public

record AdjointableOperator
  {ℓ : Level}
  (H : InnerProductSpace ℓ) :
  Set (lsuc ℓ) where
  field
    boundedOperator :
      BoundedLinearOperator
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace H))
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace H))

    adjointOperator :
      BoundedLinearOperator
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace H))
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace H))

    adjointIdentityAuthority :
      Set ℓ

open AdjointableOperator public

record SelfAdjointOperator
  {ℓ : Level}
  (H : InnerProductSpace ℓ) :
  Set (lsuc ℓ) where
  field
    adjointableOperator :
      AdjointableOperator H

    selfAdjointAuthority :
      AdjointableOperator.adjointOperator adjointableOperator
      ≡
      AdjointableOperator.boundedOperator adjointableOperator

open SelfAdjointOperator public

record UnitaryOnHilbertSpace
  {ℓ : Level}
  (H : HilbertSpace ℓ) :
  Set (lsuc ℓ) where
  field
    unitaryOperator :
      UnitaryOperator
        (BanachSpace.normedSpace (HilbertSpace.banachSpace H))

    innerProductPreservationAuthority :
      Set ℓ

open UnitaryOnHilbertSpace public

postulate
  Spectrum :
    ∀ {ℓ}
    {N : NormedSpace ℓ} →
    BoundedLinearOperator N N →
    Set ℓ

  ResolventSet :
    ∀ {ℓ}
    {N : NormedSpace ℓ} →
    BoundedLinearOperator N N →
    Set ℓ

record SpectralTheorySocket
  {ℓ : Level}
  {H : HilbertSpace ℓ}
  (T : SelfAdjointOperator (HilbertSpace.innerProductSpace H)) :
  Set (lsuc (lsuc ℓ)) where
  field
    spectralOperator :
      BoundedLinearOperator
        (BanachSpace.normedSpace (HilbertSpace.banachSpace H))
        (BanachSpace.normedSpace (HilbertSpace.banachSpace H))

    spectralOperatorMatchesInputAuthority :
      Set ℓ

    spectrum :
      Set ℓ

    spectrumIsAuthoritySpectrum :
      spectrum
      ≡
      Spectrum spectralOperator

    resolventSet :
      Set ℓ

    resolventSetIsAuthorityResolventSet :
      resolventSet
      ≡
      ResolventSet spectralOperator

    spectralTheoremAuthority :
      Set (lsuc ℓ)

    functionalCalculusAuthority :
      Set (lsuc ℓ)

open SpectralTheorySocket public

record DifferentialEquationSocket
  {ℓ : Level}
  (stateSpace : NormedSpace ℓ) :
  Set (lsuc ℓ) where
  field
    Time :
      Set

    initialState :
      NormedSpace.Carrier stateSpace

    vectorField :
      Time →
      NormedSpace.Carrier stateSpace →
      NormedSpace.Carrier stateSpace

    solution :
      Time →
      NormedSpace.Carrier stateSpace

    solutionInitialConditionAuthority :
      Set ℓ

    solutionSatisfiesEquationAuthority :
      Set ℓ

    existenceAuthority :
      Set ℓ

    uniquenessAuthority :
      Set ℓ

open DifferentialEquationSocket public

record PhysicsLinearAnalysisParityReceipt : Set₁ where
  field
    usesRealAnalysisAxioms :
      Bool

    realScalarSocketSurfaced :
      Bool

    vectorSpaceSurfaceLocal :
      Bool

    finiteDimensionalSurfaceLocal :
      Bool

    normedSpaceSurfaceReused :
      Bool

    innerProductSurfaceLocal :
      Bool

    banachSpaceSurfaceReused :
      Bool

    hilbertSpaceSurfaceLocal :
      Bool

    tensorProductCarrierExternal :
      Bool

    tensorUniversalPropertyExternal :
      Bool

    boundedOperatorSurfaceReused :
      Bool

    adjointOperatorSurfaceLocal :
      Bool

    selfAdjointSurfaceLocal :
      Bool

    unitaryOperatorSurfaceReused :
      Bool

    spectralTheoryExternal :
      Bool

    differentialEquationSurfaceLocal :
      Bool

    differentialEquationExistenceExternal :
      Bool

    complexScalarsAreExternal :
      Bool

    promotionTokenPresent :
      Bool

    claimsPhysLeanParityComplete :
      Bool

    allExternalAuthorityIsFailClosed :
      Bool

    usesRealAnalysisAxiomsIsTrue :
      usesRealAnalysisAxioms ≡ true

    realScalarSocketSurfacedIsTrue :
      realScalarSocketSurfaced ≡ true

    vectorSpaceSurfaceLocalIsTrue :
      vectorSpaceSurfaceLocal ≡ true

    finiteDimensionalSurfaceLocalIsTrue :
      finiteDimensionalSurfaceLocal ≡ true

    normedSpaceSurfaceReusedIsTrue :
      normedSpaceSurfaceReused ≡ true

    innerProductSurfaceLocalIsTrue :
      innerProductSurfaceLocal ≡ true

    banachSpaceSurfaceReusedIsTrue :
      banachSpaceSurfaceReused ≡ true

    hilbertSpaceSurfaceLocalIsTrue :
      hilbertSpaceSurfaceLocal ≡ true

    tensorProductCarrierExternalIsTrue :
      tensorProductCarrierExternal ≡ true

    tensorUniversalPropertyExternalIsTrue :
      tensorUniversalPropertyExternal ≡ true

    boundedOperatorSurfaceReusedIsTrue :
      boundedOperatorSurfaceReused ≡ true

    adjointOperatorSurfaceLocalIsTrue :
      adjointOperatorSurfaceLocal ≡ true

    selfAdjointSurfaceLocalIsTrue :
      selfAdjointSurfaceLocal ≡ true

    unitaryOperatorSurfaceReusedIsTrue :
      unitaryOperatorSurfaceReused ≡ true

    spectralTheoryExternalIsTrue :
      spectralTheoryExternal ≡ true

    differentialEquationSurfaceLocalIsTrue :
      differentialEquationSurfaceLocal ≡ true

    differentialEquationExistenceExternalIsTrue :
      differentialEquationExistenceExternal ≡ true

    complexScalarsAreExternalIsTrue :
      complexScalarsAreExternal ≡ true

    promotionTokenPresentIsFalse :
      promotionTokenPresent ≡ false

    claimsPhysLeanParityCompleteIsFalse :
      claimsPhysLeanParityComplete ≡ false

    allExternalAuthorityIsFailClosedIsTrue :
      allExternalAuthorityIsFailClosed ≡ true

open PhysicsLinearAnalysisParityReceipt public

canonicalPhysicsLinearAnalysisParityReceipt :
  PhysicsLinearAnalysisParityReceipt
canonicalPhysicsLinearAnalysisParityReceipt =
  record
    { usesRealAnalysisAxioms =
        true
    ; realScalarSocketSurfaced =
        true
    ; vectorSpaceSurfaceLocal =
        true
    ; finiteDimensionalSurfaceLocal =
        true
    ; normedSpaceSurfaceReused =
        true
    ; innerProductSurfaceLocal =
        true
    ; banachSpaceSurfaceReused =
        true
    ; hilbertSpaceSurfaceLocal =
        true
    ; tensorProductCarrierExternal =
        true
    ; tensorUniversalPropertyExternal =
        true
    ; boundedOperatorSurfaceReused =
        true
    ; adjointOperatorSurfaceLocal =
        true
    ; selfAdjointSurfaceLocal =
        true
    ; unitaryOperatorSurfaceReused =
        true
    ; spectralTheoryExternal =
        true
    ; differentialEquationSurfaceLocal =
        true
    ; differentialEquationExistenceExternal =
        true
    ; complexScalarsAreExternal =
        true
    ; promotionTokenPresent =
        false
    ; claimsPhysLeanParityComplete =
        false
    ; allExternalAuthorityIsFailClosed =
        true
    ; usesRealAnalysisAxiomsIsTrue =
        refl
    ; realScalarSocketSurfacedIsTrue =
        refl
    ; vectorSpaceSurfaceLocalIsTrue =
        refl
    ; finiteDimensionalSurfaceLocalIsTrue =
        refl
    ; normedSpaceSurfaceReusedIsTrue =
        refl
    ; innerProductSurfaceLocalIsTrue =
        refl
    ; banachSpaceSurfaceReusedIsTrue =
        refl
    ; hilbertSpaceSurfaceLocalIsTrue =
        refl
    ; tensorProductCarrierExternalIsTrue =
        refl
    ; tensorUniversalPropertyExternalIsTrue =
        refl
    ; boundedOperatorSurfaceReusedIsTrue =
        refl
    ; adjointOperatorSurfaceLocalIsTrue =
        refl
    ; selfAdjointSurfaceLocalIsTrue =
        refl
    ; unitaryOperatorSurfaceReusedIsTrue =
        refl
    ; spectralTheoryExternalIsTrue =
        refl
    ; differentialEquationSurfaceLocalIsTrue =
        refl
    ; differentialEquationExistenceExternalIsTrue =
        refl
    ; complexScalarsAreExternalIsTrue =
        refl
    ; promotionTokenPresentIsFalse =
        refl
    ; claimsPhysLeanParityCompleteIsFalse =
        refl
    ; allExternalAuthorityIsFailClosedIsTrue =
        refl
    }
