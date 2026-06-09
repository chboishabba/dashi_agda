module DASHI.Foundations.RealAnalysisAxioms where

open import Agda.Primitive using (Level; Setω; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; _++_; [])
open import Data.Nat.Base using (ℕ; suc) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)

------------------------------------------------------------------------
-- Minimal real-analysis authority surface.
--
-- This module is intentionally an axiom boundary.  It does not construct a
-- real-number implementation, a Banach-space library, or an operator-norm
-- theorem.  Downstream modules may import it to name exactly which external
-- analysis facts they are assuming.

postulate
  ℝ :
    Set

  0ℝ 1ℝ :
    ℝ

  _+ℝ_ _-ℝ_ _*ℝ_ :
    ℝ →
    ℝ →
    ℝ

  -ℝ_ :
    ℝ →
    ℝ

  absℝ :
    ℝ →
    ℝ

  _≤ℝ_ _<ℝ_ :
    ℝ →
    ℝ →
    Set

cong :
  {A B : Set} →
  {x y : A} →
  (f : A → B) →
  x ≡ y →
  f x ≡ f y
cong f refl = refl

trans :
  {A : Set} →
  {x y z : A} →
  x ≡ y →
  y ≡ z →
  x ≡ z
trans refl y≡z = y≡z

mapList :
  {A B : Set} →
  (A → B) →
  List A →
  List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

mapListAppend :
  {A B : Set} →
  (f : A → B) →
  (left right : List A) →
  mapList f (left ++ right)
  ≡
  mapList f left ++ mapList f right
mapListAppend f [] right = refl
mapListAppend f (x ∷ left) right =
  cong
    (λ mappedTail → f x ∷ mappedTail)
    (mapListAppend f left right)

listAppendRightIdentity :
  {A : Set} →
  (xs : List A) →
  xs ++ [] ≡ xs
listAppendRightIdentity [] = refl
listAppendRightIdentity (x ∷ xs) =
  cong
    (λ rest → x ∷ rest)
    (listAppendRightIdentity xs)

record RealScalarSocket : Set₁ where
  field
    realCarrier :
      Set

    realZero realOne :
      realCarrier

    realAdd realSub realMul :
      realCarrier →
      realCarrier →
      realCarrier

    realNeg realAbs :
      realCarrier →
      realCarrier

    realLe realLt :
      realCarrier →
      realCarrier →
      Set

    realFieldLawsAxiom :
      Set

    realOrderLawsAxiom :
      Set

    realCompletenessLawsAxiom :
      Set

open RealScalarSocket public

canonicalRealScalarSocket :
  RealScalarSocket
canonicalRealScalarSocket =
  record
    { realCarrier =
        ℝ
    ; realZero =
        0ℝ
    ; realOne =
        1ℝ
    ; realAdd =
        _+ℝ_
    ; realSub =
        _-ℝ_
    ; realMul =
        _*ℝ_
    ; realNeg =
        -ℝ_
    ; realAbs =
        absℝ
    ; realLe =
        _≤ℝ_
    ; realLt =
        _<ℝ_
    ; realFieldLawsAxiom =
        Bool
    ; realOrderLawsAxiom =
        Bool
    ; realCompletenessLawsAxiom =
        Bool
    }

record NormedSpace (ℓ : Level) : Set (lsuc ℓ) where
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
      ℝ →
      Carrier →
      Carrier

    ‖_‖ :
      Carrier →
      ℝ

    normNonnegative :
      (x : Carrier) →
      0ℝ ≤ℝ ‖ x ‖

    normZero :
      ‖ zero ‖ ≡ 0ℝ

    normZeroOnlyAtZero :
      (x : Carrier) →
      ‖ x ‖ ≡ 0ℝ →
      x ≡ zero

    normTriangle :
      (x y : Carrier) →
      ‖ x + y ‖ ≤ℝ (‖ x ‖ +ℝ ‖ y ‖)

    normScalar :
      (a : ℝ) →
      (x : Carrier) →
      ‖ scalarMul a x ‖ ≡ absℝ a *ℝ ‖ x ‖

open NormedSpace public

record NormedSpaceSocket
  {ℓ : Level}
  (N : NormedSpace ℓ) :
  Set (lsuc ℓ) where
  field
    socketNormedSpace :
      NormedSpace ℓ

    socketNormedSpaceIsInput :
      socketNormedSpace ≡ N

    normedSpaceLawsAreAuthority :
      Bool

    normedSpaceLawsAreAuthorityIsTrue :
      normedSpaceLawsAreAuthority ≡ true

open NormedSpaceSocket public

postulate
  IsCauchy :
    ∀ {ℓ} →
    (N : NormedSpace ℓ) →
    (ℕ → NormedSpace.Carrier N) →
    Set ℓ

  ConvergesTo :
    ∀ {ℓ} →
    (N : NormedSpace ℓ) →
    (ℕ → NormedSpace.Carrier N) →
    NormedSpace.Carrier N →
    Set ℓ

record CauchySequenceSocket
  {ℓ : Level}
  (N : NormedSpace ℓ)
  (xs : ℕ → NormedSpace.Carrier N) :
  Set ℓ where
  field
    cauchySequenceWitness :
      IsCauchy N xs

open CauchySequenceSocket public

record SeriesConvergenceSocket
  {ℓ : Level}
  (N : NormedSpace ℓ)
  (term partialSum : ℕ → NormedSpace.Carrier N) :
  Set (lsuc ℓ) where
  field
    seriesTerm :
      ℕ →
      NormedSpace.Carrier N

    seriesTermIsInput :
      seriesTerm ≡ term

    seriesPartialSum :
      ℕ →
      NormedSpace.Carrier N

    seriesPartialSumIsInput :
      seriesPartialSum ≡ partialSum

    seriesPartialSumsCauchy :
      IsCauchy N seriesPartialSum

    seriesLimit :
      NormedSpace.Carrier N

    seriesPartialSumsConverge :
      ConvergesTo N seriesPartialSum seriesLimit

open SeriesConvergenceSocket public

record BanachSpace (ℓ : Level) : Set (lsuc ℓ) where
  field
    normedSpace :
      NormedSpace ℓ

    cauchyLimit :
      (xs : ℕ → NormedSpace.Carrier normedSpace) →
      IsCauchy normedSpace xs →
      NormedSpace.Carrier normedSpace

    cauchyLimitConverges :
      (xs : ℕ → NormedSpace.Carrier normedSpace) →
      (cauchy : IsCauchy normedSpace xs) →
      ConvergesTo normedSpace xs (cauchyLimit xs cauchy)

open BanachSpace public

record BanachSpaceSocket
  {ℓ : Level}
  (B : BanachSpace ℓ) :
  Set (lsuc ℓ) where
  field
    socketBanachSpace :
      BanachSpace ℓ

    socketBanachSpaceIsInput :
      socketBanachSpace ≡ B

    banachCompletenessIsAuthority :
      Bool

    banachCompletenessIsAuthorityIsTrue :
      banachCompletenessIsAuthority ≡ true

open BanachSpaceSocket public

record LinearOperator
  {ℓ₁ ℓ₂ : Level}
  (X : NormedSpace ℓ₁)
  (Y : NormedSpace ℓ₂) :
  Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    map :
      NormedSpace.Carrier X →
      NormedSpace.Carrier Y

    linearityAxiom :
      Set (ℓ₁ ⊔ ℓ₂)

open LinearOperator public

record BoundedLinearOperator
  {ℓ₁ ℓ₂ : Level}
  (X : NormedSpace ℓ₁)
  (Y : NormedSpace ℓ₂) :
  Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    linearOperator :
      LinearOperator X Y

    boundednessAxiom :
      Set (ℓ₁ ⊔ ℓ₂)

open BoundedLinearOperator public

postulate
  operatorNorm :
    ∀ {ℓ₁ ℓ₂} →
    {X : NormedSpace ℓ₁} →
    {Y : NormedSpace ℓ₂} →
    BoundedLinearOperator X Y →
    ℝ

record OperatorNormSocket
  {ℓ₁ ℓ₂ : Level}
  {X : NormedSpace ℓ₁}
  {Y : NormedSpace ℓ₂}
  (T : BoundedLinearOperator X Y) :
  Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    operatorNormValue :
      ℝ

    operatorNormValueIsAuthorityNorm :
      operatorNormValue ≡ operatorNorm T

    operatorNormNonnegativeSocket :
      0ℝ ≤ℝ operatorNormValue

    operatorNormBoundSocket :
      (x : NormedSpace.Carrier X) →
      NormedSpace.‖_‖ Y
        (LinearOperator.map
          (BoundedLinearOperator.linearOperator T)
          x)
      ≤ℝ
      (operatorNormValue *ℝ NormedSpace.‖_‖ X x)

open OperatorNormSocket public

record UnitaryOperator
  {ℓ : Level}
  (X : NormedSpace ℓ) :
  Set (lsuc ℓ) where
  field
    boundedOperator :
      BoundedLinearOperator X X

    inverseAdjointAxiom :
      Set ℓ

    preservesNorm :
      (x : NormedSpace.Carrier X) →
      NormedSpace.‖_‖ X
        (LinearOperator.map
          (BoundedLinearOperator.linearOperator boundedOperator)
          x)
      ≡
      NormedSpace.‖_‖ X x

open UnitaryOperator public

record UnitarySocket
  {ℓ : Level}
  {X : NormedSpace ℓ}
  (U : UnitaryOperator X) :
  Set (lsuc ℓ) where
  field
    unitaryOperator :
      UnitaryOperator X

    unitaryOperatorIsInput :
      unitaryOperator ≡ U

    unitaryPreservesNormSocket :
      (x : NormedSpace.Carrier X) →
      NormedSpace.‖_‖ X
        (LinearOperator.map
          (BoundedLinearOperator.linearOperator
            (UnitaryOperator.boundedOperator U))
          x)
      ≡
      NormedSpace.‖_‖ X x

    unitaryOperatorNormIsOneSocket :
      operatorNorm (UnitaryOperator.boundedOperator U) ≡ 1ℝ

open UnitarySocket public

record CStarAlgebra (ℓ : Level) : Set (lsuc ℓ) where
  field
    cStarNormedSpace :
      NormedSpace ℓ

    cStarBanachSpace :
      BanachSpace ℓ

    cStarBanachSpaceMatchesNormedSpace :
      BanachSpace.normedSpace cStarBanachSpace
      ≡
      cStarNormedSpace

    cStarMultiply :
      NormedSpace.Carrier cStarNormedSpace →
      NormedSpace.Carrier cStarNormedSpace →
      NormedSpace.Carrier cStarNormedSpace

    cStarInvolution :
      NormedSpace.Carrier cStarNormedSpace →
      NormedSpace.Carrier cStarNormedSpace

    cStarAlgebraLawsAxiom :
      Set ℓ

    cStarInvolutionLawsAxiom :
      Set ℓ

    cStarNormIdentityAxiom :
      Set ℓ

open CStarAlgebra public

record CStarCompletionSocket
  {ℓ : Level}
  (A : CStarAlgebra ℓ) :
  Set (lsuc (lsuc ℓ)) where
  field
    cStarCompletionAlgebra :
      CStarAlgebra ℓ

    cStarCompletionMap :
      NormedSpace.Carrier (CStarAlgebra.cStarNormedSpace A) →
      NormedSpace.Carrier
        (CStarAlgebra.cStarNormedSpace cStarCompletionAlgebra)

    cStarCompletionIsBanach :
      BanachSpace ℓ

    cStarCompletionBanachMatchesAlgebra :
      cStarCompletionIsBanach
      ≡
      CStarAlgebra.cStarBanachSpace cStarCompletionAlgebra

    cStarCompletionDenseImageAxiom :
      Set ℓ

    cStarCompletionUniversalPropertyAxiom :
      Set (lsuc ℓ)

open CStarCompletionSocket public

postulate
  geometricTerm :
    ℝ →
    ℕ →
    ℝ

  geometricPartialSum :
    ℝ →
    ℕ →
    ℝ

  geometricSeriesSum :
    ℝ →
    ℝ

  GeometricFiniteSumFormula :
    ℝ →
    ℕ →
    Set

  GeometricSeriesCauchy :
    ℝ →
    Set

  GeometricSeriesConverges :
    ℝ →
    Set

  GeometricSeriesSumLaw :
    ℝ →
    Set

record GeometricSumSocket
  (r : ℝ) :
  Set₁ where
  field
    geometricRatioInsideUnit :
      absℝ r <ℝ 1ℝ

    geometricTermAt :
      ℕ →
      ℝ

    geometricTermAtIsAuthorityTerm :
      geometricTermAt
      ≡
      geometricTerm r

    geometricPartialSumAt :
      ℕ →
      ℝ

    geometricPartialSumAtIsAuthorityPartialSum :
      geometricPartialSumAt
      ≡
      geometricPartialSum r

    geometricInfiniteSum :
      ℝ

    geometricInfiniteSumIsAuthoritySum :
      geometricInfiniteSum
      ≡
      geometricSeriesSum r

    geometricFiniteSumFormula :
      (n : ℕ) →
      GeometricFiniteSumFormula r n

    geometricSeriesCauchy :
      GeometricSeriesCauchy r

    geometricSeriesConverges :
      GeometricSeriesConverges r

    geometricSeriesSumLaw :
      GeometricSeriesSumLaw r

open GeometricSumSocket public

record DiscreteTelescopingBoundData : Set₁ where
  field
    discreteDefectBound :
      ℕ →
      ℕ

    oneStepDiscreteBound :
      (d : ℕ) →
      discreteDefectBound (suc d)
      ≤ℕ
      discreteDefectBound d

    finiteTelescopingBound :
      (start span : ℕ) →
      discreteDefectBound (span +ℕ start)
      ≤ℕ
      discreteDefectBound start

    telescopingBoundIsFiniteReceipt :
      Bool

    telescopingBoundIsFiniteReceiptIsTrue :
      telescopingBoundIsFiniteReceipt ≡ true

open DiscreteTelescopingBoundData public

record DiscreteProductBoundData : Set₁ where
  field
    productBaseBound :
      ℕ →
      ℕ

    productBound :
      ℕ →
      ℕ →
      ℕ

    productBoundAtZeroSpan :
      (start : ℕ) →
      productBound start 0
      ≡
      productBaseBound start

    productBoundTelescopes :
      (start span : ℕ) →
      productBound start span
      ≤ℕ
      productBaseBound start

    productBoundIsFiniteReceipt :
      Bool

    productBoundIsFiniteReceiptIsTrue :
      productBoundIsFiniteReceipt ≡ true

open DiscreteProductBoundData public

record LocalDiscreteNonabelianStokesProofSurface : Set₁ where
  field
    LoopAtDepth :
      ℕ →
      Set

    canonicalLoopAtDepth :
      (d : ℕ) →
      LoopAtDepth d

    SurfaceFillingAtDepth :
      (d : ℕ) →
      LoopAtDepth d →
      Set

    canonicalSurfaceFillingAtDepth :
      (d : ℕ) →
      SurfaceFillingAtDepth d (canonicalLoopAtDepth d)

    BoundaryWordAtDepth :
      (d : ℕ) →
      LoopAtDepth d →
      Set

    canonicalBoundaryWordAtDepth :
      (d : ℕ) →
      BoundaryWordAtDepth d (canonicalLoopAtDepth d)

    boundaryWordAppendAtDepth :
      (d : ℕ) →
      (loop : LoopAtDepth d) →
      BoundaryWordAtDepth d loop →
      BoundaryWordAtDepth d loop →
      BoundaryWordAtDepth d loop

    BoundaryEdgeLabelAtDepth :
      (d : ℕ) →
      LoopAtDepth d →
      Set

    boundaryWordFromEdgeLabelsAtDepth :
      (d : ℕ) →
      (loop : LoopAtDepth d) →
      List (BoundaryEdgeLabelAtDepth d loop) →
      BoundaryWordAtDepth d loop

    boundaryWordEdgeLabelsAtDepth :
      (d : ℕ) →
      (loop : LoopAtDepth d) →
      BoundaryWordAtDepth d loop →
      List (BoundaryEdgeLabelAtDepth d loop)

    boundaryWordEdgeLabelsFromConstructedAtDepth :
      (d : ℕ) →
      (loop : LoopAtDepth d) →
      (labels : List (BoundaryEdgeLabelAtDepth d loop)) →
      boundaryWordEdgeLabelsAtDepth
        d
        loop
        (boundaryWordFromEdgeLabelsAtDepth d loop labels)
      ≡
      labels

    boundaryWordEdgeLabelsAppendAtDepth :
      (d : ℕ) →
      (loop : LoopAtDepth d) →
      (left right : BoundaryWordAtDepth d loop) →
      boundaryWordEdgeLabelsAtDepth
        d
        loop
        (boundaryWordAppendAtDepth d loop left right)
      ≡
      boundaryWordEdgeLabelsAtDepth d loop left
      ++
      boundaryWordEdgeLabelsAtDepth d loop right

    boundaryWordFoldAtDepth :
      (d : ℕ) →
      (loop : LoopAtDepth d) →
      (Target : Set) →
      (BoundaryWordAtDepth d loop → Target → Target) →
      Target →
      BoundaryWordAtDepth d loop →
      Target

    boundaryWordFoldComputesEdgeLabelListAtDepth :
      (d : ℕ) →
      (loop : LoopAtDepth d) →
      (left right : BoundaryWordAtDepth d loop) →
      boundaryWordFoldAtDepth
        d
        loop
        (List (BoundaryEdgeLabelAtDepth d loop))
        (λ word accumulatedLabels →
          boundaryWordEdgeLabelsAtDepth d loop word
          ++
          accumulatedLabels)
        []
        (boundaryWordAppendAtDepth d loop left right)
      ≡
      boundaryWordEdgeLabelsAtDepth d loop left
      ++
      boundaryWordEdgeLabelsAtDepth d loop right

    boundaryWordFoldComputesMappedEdgeLabelListAtDepth :
      (d : ℕ) →
      (loop : LoopAtDepth d) →
      (TargetLabel : Set) →
      (labelMap : BoundaryEdgeLabelAtDepth d loop → TargetLabel) →
      (left right : BoundaryWordAtDepth d loop) →
      boundaryWordFoldAtDepth
        d
        loop
        (List TargetLabel)
        (λ word accumulatedLabels →
          mapList labelMap (boundaryWordEdgeLabelsAtDepth d loop word)
          ++
          accumulatedLabels)
        []
        (boundaryWordAppendAtDepth d loop left right)
      ≡
      mapList labelMap (boundaryWordEdgeLabelsAtDepth d loop left)
      ++
      mapList labelMap (boundaryWordEdgeLabelsAtDepth d loop right)

    telescopingBoundData :
      DiscreteTelescopingBoundData

    productBoundData :
      DiscreteProductBoundData

    boundaryProductControlledByTelescoping :
      (start span : ℕ) →
      DiscreteProductBoundData.productBound productBoundData start span
      ≤ℕ
      DiscreteTelescopingBoundData.discreteDefectBound
        telescopingBoundData
        start

    localDiscreteStokesConstructed :
      Bool

    localDiscreteStokesConstructedIsTrue :
      localDiscreteStokesConstructed ≡ true

    analyticNonabelianStokesStillPostulated :
      Bool

    analyticNonabelianStokesStillPostulatedIsTrue :
      analyticNonabelianStokesStillPostulated ≡ true

open LocalDiscreteNonabelianStokesProofSurface public

record WaveCoherenceUniformGeometricBoundData : Set₁ where
  field
    uniformBound :
      ℕ →
      ℕ

    oneStepUniformBound :
      (d : ℕ) →
      uniformBound (suc d)
      ≤ℕ
      uniformBound d

    uniformFiniteChainBound :
      (start span : ℕ) →
      uniformBound (span +ℕ start)
      ≤ℕ
      uniformBound start

    localUniformGeometricBoundConstructed :
      Bool

    localUniformGeometricBoundConstructedIsTrue :
      localUniformGeometricBoundConstructed ≡ true

    realGeometricSummabilityStillPostulated :
      Bool

    realGeometricSummabilityStillPostulatedIsTrue :
      realGeometricSummabilityStillPostulated ≡ true

open WaveCoherenceUniformGeometricBoundData public

record DiscreteConvergenceToIdentityBridgeData : Set₁ where
  field
    HolonomyElement :
      Set

    identityHolonomy :
      HolonomyElement

    discreteHolonomyAtDepth :
      ℕ →
      HolonomyElement

    identityDefectBound :
      ℕ →
      ℕ

    identityDefectTelescopes :
      (start span : ℕ) →
      identityDefectBound (span +ℕ start)
      ≤ℕ
      identityDefectBound start

    zeroDefectImpliesIdentity :
      (d : ℕ) →
      identityDefectBound d ≡ 0 →
      discreteHolonomyAtDepth d ≡ identityHolonomy

    localConvergenceBridgeConstructed :
      Bool

    localConvergenceBridgeConstructedIsTrue :
      localConvergenceBridgeConstructed ≡ true

    analyticConvergenceStillPostulated :
      Bool

    analyticConvergenceStillPostulatedIsTrue :
      analyticConvergenceStillPostulated ≡ true

open DiscreteConvergenceToIdentityBridgeData public

postulate
  DiscreteStokesProblem :
    Setω

  DiscreteStokesConclusion :
    DiscreteStokesProblem →
    Setω

  UniformGeometricBoundProblem :
    Setω

  UniformGeometricBoundConclusion :
    UniformGeometricBoundProblem →
    Setω

  ConvergenceToIdentityProblem :
    Setω

  ConvergenceToIdentityConclusion :
    ConvergenceToIdentityProblem →
    Setω

postulate
  HolonomyLimitProblem :
    Setω

  HolonomyLimitConclusion :
    HolonomyLimitProblem →
    Setω

record RealAnalysisAuthority : Setω where
  field
    authorityIsPostulated :
      Bool

    authorityIsPostulatedIsTrue :
      authorityIsPostulated ≡ true

    realCarrierPlaceholder :
      Set

    realCarrierPlaceholderIsℝ :
      realCarrierPlaceholder ≡ ℝ

    realScalarSocketAxiom :
      RealScalarSocket

    realScalarSocketIsCanonical :
      realScalarSocketAxiom
      ≡
      canonicalRealScalarSocket

    normedSpaceSocketAxiom :
      ∀ {ℓ} →
      (N : NormedSpace ℓ) →
      NormedSpaceSocket N

    banachSpaceSocketAxiom :
      ∀ {ℓ} →
      (B : BanachSpace ℓ) →
      BanachSpaceSocket B

    cauchySequenceSocketAxiom :
      ∀ {ℓ} →
      {N : NormedSpace ℓ} →
      {xs : ℕ → NormedSpace.Carrier N} →
      IsCauchy N xs →
      CauchySequenceSocket N xs

    cauchyCompletenessAxiom :
      ∀ {ℓ} →
      (B : BanachSpace ℓ) →
      (xs : ℕ → NormedSpace.Carrier (BanachSpace.normedSpace B)) →
      (cauchy : IsCauchy (BanachSpace.normedSpace B) xs) →
      ConvergesTo
        (BanachSpace.normedSpace B)
        xs
        (BanachSpace.cauchyLimit B xs cauchy)

    seriesConvergenceSocketAxiom :
      ∀ {ℓ} →
      (B : BanachSpace ℓ) →
      (term partialSum :
        ℕ → NormedSpace.Carrier (BanachSpace.normedSpace B)) →
      IsCauchy (BanachSpace.normedSpace B) partialSum →
      SeriesConvergenceSocket
        (BanachSpace.normedSpace B)
        term
        partialSum

    operatorNormSocketAxiom :
      ∀ {ℓ₁ ℓ₂} →
      {X : NormedSpace ℓ₁} →
      {Y : NormedSpace ℓ₂} →
      (T : BoundedLinearOperator X Y) →
      OperatorNormSocket T

    operatorNormNonnegativeAxiom :
      ∀ {ℓ₁ ℓ₂} →
      {X : NormedSpace ℓ₁} →
      {Y : NormedSpace ℓ₂} →
      (T : BoundedLinearOperator X Y) →
      0ℝ ≤ℝ operatorNorm T

    operatorNormBoundAxiom :
      ∀ {ℓ₁ ℓ₂} →
      {X : NormedSpace ℓ₁} →
      {Y : NormedSpace ℓ₂} →
      (T : BoundedLinearOperator X Y) →
      (x : NormedSpace.Carrier X) →
      NormedSpace.‖_‖ Y
        (LinearOperator.map
          (BoundedLinearOperator.linearOperator T)
          x)
      ≤ℝ
      (operatorNorm T *ℝ NormedSpace.‖_‖ X x)

    geometricSeriesCauchyAxiom :
      (r : ℝ) →
      absℝ r <ℝ 1ℝ →
      GeometricSeriesCauchy r

    geometricSeriesConvergesAxiom :
      (r : ℝ) →
      absℝ r <ℝ 1ℝ →
      GeometricSeriesConverges r

    geometricSumSocketAxiom :
      (r : ℝ) →
      absℝ r <ℝ 1ℝ →
      GeometricSumSocket r

    unitaryPreservesNormAxiom :
      ∀ {ℓ} →
      {X : NormedSpace ℓ} →
      (U : UnitaryOperator X) →
      (x : NormedSpace.Carrier X) →
      NormedSpace.‖_‖ X
        (LinearOperator.map
          (BoundedLinearOperator.linearOperator
            (UnitaryOperator.boundedOperator U))
          x)
      ≡
      NormedSpace.‖_‖ X x

    unitaryOperatorNormIsOneAxiom :
      ∀ {ℓ} →
      {X : NormedSpace ℓ} →
      (U : UnitaryOperator X) →
      operatorNorm (UnitaryOperator.boundedOperator U) ≡ 1ℝ

    unitarySocketAxiom :
      ∀ {ℓ} →
      {X : NormedSpace ℓ} →
      (U : UnitaryOperator X) →
      UnitarySocket U

    cStarCompletionSocketAxiom :
      ∀ {ℓ} →
      (A : CStarAlgebra ℓ) →
      CStarCompletionSocket A

    discreteStokesTheoremAxiom :
      (problem : DiscreteStokesProblem) →
      DiscreteStokesConclusion problem

    uniformGeometricBoundAxiom :
      (problem : UniformGeometricBoundProblem) →
      UniformGeometricBoundConclusion problem

    convergenceToIdentityAxiom :
      (problem : ConvergenceToIdentityProblem) →
      ConvergenceToIdentityConclusion problem

    holonomyLimitTheoremAxiom :
      (problem : HolonomyLimitProblem) →
      HolonomyLimitConclusion problem

open RealAnalysisAuthority public

postulate
  postulatedRealAnalysisAuthority :
    RealAnalysisAuthority
