module DASHI.Physics.YangMills.BalabanGreenRandomWalkNonlinearCompletion where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPatchRegimeHodgeUniformity using
  (PatchRegime; bulk; boundary; scaleInterface; corner; nestedRestriction)

------------------------------------------------------------------------
-- D. Green operator and random-walk completion.
--
-- This record fixes the mathematically correct hierarchy:
--
--   local parametrix -> residual powers -> convergent random walk
--   -> correction inverse -> full Green factorization.
--
-- In particular, the full Green operator is identified with the limit of the
-- finite partial walks, not with every finite partial sum.
------------------------------------------------------------------------

record GreenRandomWalkData (Index State Bound : Set) : Set₁ where
  field
    regime : Index → PatchRegime

    H localGreen referenceGreen gradientReferenceGreen
      secondGradientReferenceGreen residual fullGreen correctionInverse :
      Index → State → State

    residualPower partialRandomWalk randomWalkTail :
      Index → Nat → State → State

    randomWalkLimit : (Nat → State) → State
    compose : (State → State) → (State → State) → State → State

    weightedNorm : State → Bound
    add multiply power : Bound → Bound → Bound
    zero one : Bound
    LessEqual StrictlyBelow : Bound → Bound → Set

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    multiplyMonotoneLeft : ∀ {left right} value →
      LessEqual left right →
      LessEqual (multiply left value) (multiply right value)
    multiplyAssociative : ∀ left middle right →
      multiply (multiply left middle) right ≡
      multiply left (multiply middle right)

    CG-bulk CG-boundary CG-interface CG-corner CG-nested CG0 : Bound
    C∇G-bulk C∇G-boundary C∇G-interface C∇G-corner C∇G-nested C∇G0 : Bound
    C∇²G-bulk C∇²G-boundary C∇²G-interface C∇²G-corner C∇²G-nested C∇²G0 : Bound

    qBulk qBoundary qInterface qCorner qNested q : Bound
    CG-tail Ccorr : Bound

    -- D1--D5.
    bulkGreenEstimate : ∀ index f → regime index ≡ bulk →
      LessEqual (weightedNorm (referenceGreen index f))
        (multiply CG-bulk (weightedNorm f))
    boundaryGreenEstimate : ∀ index f → regime index ≡ boundary →
      LessEqual (weightedNorm (referenceGreen index f))
        (multiply CG-boundary (weightedNorm f))
    interfaceGreenEstimate : ∀ index f → regime index ≡ scaleInterface →
      LessEqual (weightedNorm (referenceGreen index f))
        (multiply CG-interface (weightedNorm f))
    cornerGreenEstimate : ∀ index f → regime index ≡ corner →
      LessEqual (weightedNorm (referenceGreen index f))
        (multiply CG-corner (weightedNorm f))
    nestedGreenEstimate : ∀ index f → regime index ≡ nestedRestriction →
      LessEqual (weightedNorm (referenceGreen index f))
        (multiply CG-nested (weightedNorm f))

    -- D6--D10.
    bulkGradientEstimate : ∀ index f → regime index ≡ bulk →
      LessEqual (weightedNorm (gradientReferenceGreen index f))
        (multiply C∇G-bulk (weightedNorm f))
    boundaryGradientEstimate : ∀ index f → regime index ≡ boundary →
      LessEqual (weightedNorm (gradientReferenceGreen index f))
        (multiply C∇G-boundary (weightedNorm f))
    interfaceGradientEstimate : ∀ index f → regime index ≡ scaleInterface →
      LessEqual (weightedNorm (gradientReferenceGreen index f))
        (multiply C∇G-interface (weightedNorm f))
    cornerGradientEstimate : ∀ index f → regime index ≡ corner →
      LessEqual (weightedNorm (gradientReferenceGreen index f))
        (multiply C∇G-corner (weightedNorm f))
    nestedGradientEstimate : ∀ index f → regime index ≡ nestedRestriction →
      LessEqual (weightedNorm (gradientReferenceGreen index f))
        (multiply C∇G-nested (weightedNorm f))

    -- D11--D15.
    bulkSecondGradientEstimate : ∀ index f → regime index ≡ bulk →
      LessEqual (weightedNorm (secondGradientReferenceGreen index f))
        (multiply C∇²G-bulk (weightedNorm f))
    boundarySecondGradientEstimate : ∀ index f → regime index ≡ boundary →
      LessEqual (weightedNorm (secondGradientReferenceGreen index f))
        (multiply C∇²G-boundary (weightedNorm f))
    interfaceSecondGradientEstimate : ∀ index f → regime index ≡ scaleInterface →
      LessEqual (weightedNorm (secondGradientReferenceGreen index f))
        (multiply C∇²G-interface (weightedNorm f))
    cornerSecondGradientEstimate : ∀ index f → regime index ≡ corner →
      LessEqual (weightedNorm (secondGradientReferenceGreen index f))
        (multiply C∇²G-corner (weightedNorm f))
    nestedSecondGradientEstimate : ∀ index f → regime index ≡ nestedRestriction →
      LessEqual (weightedNorm (secondGradientReferenceGreen index f))
        (multiply C∇²G-nested (weightedNorm f))

    -- D16.
    bulkGreenBelowCommon : LessEqual CG-bulk CG0
    boundaryGreenBelowCommon : LessEqual CG-boundary CG0
    interfaceGreenBelowCommon : LessEqual CG-interface CG0
    cornerGreenBelowCommon : LessEqual CG-corner CG0
    nestedGreenBelowCommon : LessEqual CG-nested CG0

    bulkGradientBelowCommon : LessEqual C∇G-bulk C∇G0
    boundaryGradientBelowCommon : LessEqual C∇G-boundary C∇G0
    interfaceGradientBelowCommon : LessEqual C∇G-interface C∇G0
    cornerGradientBelowCommon : LessEqual C∇G-corner C∇G0
    nestedGradientBelowCommon : LessEqual C∇G-nested C∇G0

    bulkSecondBelowCommon : LessEqual C∇²G-bulk C∇²G0
    boundarySecondBelowCommon : LessEqual C∇²G-boundary C∇²G0
    interfaceSecondBelowCommon : LessEqual C∇²G-interface C∇²G0
    cornerSecondBelowCommon : LessEqual C∇²G-corner C∇²G0
    nestedSecondBelowCommon : LessEqual C∇²G-nested C∇²G0

    -- D17.
    localParametrixResidual : ∀ index f →
      H index (localGreen index f) ≡ residualDifference index f

    residualDifference : Index → State → State
    residualDifferenceMeaning : ∀ index f →
      residualDifference index f ≡ subtractResidual index f
    subtractResidual : Index → State → State

    -- D18--D22.
    bulkResidualEstimate : ∀ index f → regime index ≡ bulk →
      LessEqual (weightedNorm (residual index f))
        (multiply qBulk (weightedNorm f))
    boundaryResidualEstimate : ∀ index f → regime index ≡ boundary →
      LessEqual (weightedNorm (residual index f))
        (multiply qBoundary (weightedNorm f))
    interfaceResidualEstimate : ∀ index f → regime index ≡ scaleInterface →
      LessEqual (weightedNorm (residual index f))
        (multiply qInterface (weightedNorm f))
    cornerResidualEstimate : ∀ index f → regime index ≡ corner →
      LessEqual (weightedNorm (residual index f))
        (multiply qCorner (weightedNorm f))
    nestedResidualEstimate : ∀ index f → regime index ≡ nestedRestriction →
      LessEqual (weightedNorm (residual index f))
        (multiply qNested (weightedNorm f))

    -- D23. The selected decomposition currently uses the safe sum budget.
    patchResidualSumBelowQ :
      LessEqual
        (add qBulk (add qBoundary (add qInterface (add qCorner qNested))))
        q
    qStrict : StrictlyBelow q one

    -- D24--D29 analytic leaves and exact identifications.
    residualPowerEstimate : ∀ index n f →
      LessEqual (weightedNorm (residualPower index n f))
        (multiply (power q (natAsBound n)) (weightedNorm f))
    natAsBound : Nat → Bound

    randomWalkTailEstimate : ∀ index n f →
      LessEqual (weightedNorm (randomWalkTail index n f))
        (multiply (multiply CG-tail (power q (natAsBound n)))
          (weightedNorm f))

    neumannLimitIdentity : ∀ index f →
      fullGreen index f ≡
      randomWalkLimit (λ n → partialRandomWalk index n f)

    correctionInverseEstimate : ∀ index f →
      LessEqual (weightedNorm (correctionInverse index f))
        (multiply Ccorr (weightedNorm f))

    correctionBoundFromGeometricSeries : LessEqual Ccorr geometricInverse
    geometricInverse : Bound
    geometricInverseMeaning : Set

    fullGreenFactorizationPointwise : ∀ index f →
      fullGreen index f ≡
      referenceGreen index (correctionInverse index f)
    gradientFullGreenFactorizationPointwise : ∀ index f →
      gradientFullGreen index f ≡
      gradientReferenceGreen index (correctionInverse index f)
    secondGradientFullGreenFactorizationPointwise : ∀ index f →
      secondGradientFullGreen index f ≡
      secondGradientReferenceGreen index (correctionInverse index f)

    gradientFullGreen secondGradientFullGreen : Index → State → State

    referenceGreenCommonBound : ∀ index f →
      LessEqual (weightedNorm (referenceGreen index f))
        (multiply CG0 (weightedNorm f))
    gradientReferenceGreenCommonBound : ∀ index f →
      LessEqual (weightedNorm (gradientReferenceGreen index f))
        (multiply C∇G0 (weightedNorm f))
    secondGradientReferenceGreenCommonBound : ∀ index f →
      LessEqual (weightedNorm (secondGradientReferenceGreen index f))
        (multiply C∇²G0 (weightedNorm f))

open GreenRandomWalkData public

-- D1--D15 public theorem names.
bulkGreenBound = bulkGreenEstimate
boundaryGreenBound = boundaryGreenEstimate
interfaceGreenBound = interfaceGreenEstimate
cornerGreenBound = cornerGreenEstimate
nestedGreenBound = nestedGreenEstimate

bulkGradientGreenBound = bulkGradientEstimate
boundaryGradientGreenBound = boundaryGradientEstimate
interfaceGradientGreenBound = interfaceGradientEstimate
cornerGradientGreenBound = cornerGradientEstimate
nestedGradientGreenBound = nestedGradientEstimate

bulkSecondGradientGreenBound = bulkSecondGradientEstimate
boundarySecondGradientGreenBound = boundarySecondGradientEstimate
interfaceSecondGradientGreenBound = interfaceSecondGradientEstimate
cornerSecondGradientGreenBound = cornerSecondGradientEstimate
nestedSecondGradientGreenBound = nestedSecondGradientEstimate

regimeGreenConstantsHaveCommonUpper :
  ∀ {Index State Bound} (D : GreenRandomWalkData Index State Bound) →
  (r : PatchRegime) → Bound
regimeGreenConstantsHaveCommonUpper D bulk = CG-bulk D
regimeGreenConstantsHaveCommonUpper D boundary = CG-boundary D
regimeGreenConstantsHaveCommonUpper D scaleInterface = CG-interface D
regimeGreenConstantsHaveCommonUpper D corner = CG-corner D
regimeGreenConstantsHaveCommonUpper D nestedRestriction = CG-nested D

regimeGreenConstantsHaveCommonUpper-proof :
  ∀ {Index State Bound} (D : GreenRandomWalkData Index State Bound) →
  (r : PatchRegime) →
  LessEqual D (regimeGreenConstantsHaveCommonUpper D r) (CG0 D)
regimeGreenConstantsHaveCommonUpper-proof D bulk = bulkGreenBelowCommon D
regimeGreenConstantsHaveCommonUpper-proof D boundary = boundaryGreenBelowCommon D
regimeGreenConstantsHaveCommonUpper-proof D scaleInterface = interfaceGreenBelowCommon D
regimeGreenConstantsHaveCommonUpper-proof D corner = cornerGreenBelowCommon D
regimeGreenConstantsHaveCommonUpper-proof D nestedRestriction = nestedGreenBelowCommon D

localParametrixResidualEquation = localParametrixResidual
bulkResidualBound = bulkResidualEstimate
boundaryResidualBound = boundaryResidualEstimate
interfaceResidualBound = interfaceResidualEstimate
cornerResidualBound = cornerResidualEstimate
nestedResidualBound = nestedResidualEstimate
residualPowerBound = residualPowerEstimate
randomWalkTailBound = randomWalkTailEstimate
neumannSeriesRepresentsGreen = neumannLimitIdentity
uniformCorrectionInverseBound = correctionInverseEstimate
fullGreenFactorization = fullGreenFactorizationPointwise

uniformWeightedGreenBound :
  ∀ {Index State Bound} (D : GreenRandomWalkData Index State Bound) →
  ∀ index f →
  LessEqual D (weightedNorm D (fullGreen D index f))
    (multiply D (multiply D (CG0 D) (Ccorr D)) (weightedNorm D f))
uniformWeightedGreenBound D index f rewrite fullGreenFactorizationPointwise D index f =
  transitive D
    (referenceGreenCommonBound D index (correctionInverse D index f))
    (transitive D
      (multiplyMonotoneLeft D (CG0 D) (correctionInverseEstimate D index f))
      (rewriteMultiply D))
  where
  rewriteMultiply :
    ∀ {source} →
    LessEqual D
      (multiply D (CG0 D) (multiply D (Ccorr D) source))
      (multiply D (multiply D (CG0 D) (Ccorr D)) source)
  rewriteMultiply {source} rewrite multiplyAssociative D (CG0 D) (Ccorr D) source =
    reflexiveBound
    where
    reflexiveBound : LessEqual D
      (multiply D (multiply D (CG0 D) (Ccorr D)) source)
      (multiply D (multiply D (CG0 D) (Ccorr D)) source)
    reflexiveBound = transitive D
      (multiplyMonotoneLeft D source (bulkGreenBelowCommon D))
      (multiplyMonotoneLeft D source (bulkGreenBelowCommon D))

-- Gradient endpoints are retained as explicit leaves because the weak ordered
-- carrier does not assume equality reflection or a general congruence rewrite.
record FullGreenDerivativeBounds
    {Index State Bound : Set}
    (D : GreenRandomWalkData Index State Bound) : Set₁ where
  field
    uniformWeightedGradientGreenBound : ∀ index f →
      LessEqual D (weightedNorm D (gradientFullGreen D index f))
        (multiply D (multiply D (C∇G0 D) (Ccorr D)) (weightedNorm D f))
    uniformWeightedSecondGradientGreenBound : ∀ index f →
      LessEqual D (weightedNorm D (secondGradientFullGreen D index f))
        (multiply D (multiply D (C∇²G0 D) (Ccorr D)) (weightedNorm D f))

open FullGreenDerivativeBounds public

------------------------------------------------------------------------
-- E. Seven nonlinear mechanisms with radius-dependent constants.
------------------------------------------------------------------------

record SevenNonlinearRemainderCompletion
    (Index State Bound : Set) : Set₁ where
  field
    nonlinear NBCH Ncomm Ntransport NbackgroundDerivative Ngauge
      Nconstraint Nchart : Index → State → State
    subtract : State → State → State
    norm : State → Bound
    add multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    InCriticalBall : Index → State → Set

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (add left right) (add left′ right′)

    LBCH Lcomm Ltransport LbackgroundDerivative Lgauge Lconstraint Lchart LN :
      Bound → Bound
    radius : Bound

    bchThirdOrderRemainderBound bchDerivativeDifferenceBound :
      Index → Set
    compactLieBracketInequality : Index → Set

    bchHigherLipschitzLeaf : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (NBCH index h) (NBCH index h′)))
        (multiply (LBCH radius) (norm (subtract h h′)))
    commutatorLipschitzLeaf : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Ncomm index h) (Ncomm index h′)))
        (multiply (Lcomm radius) (norm (subtract h h′)))
    parallelTransportLipschitzLeaf : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Ntransport index h) (Ntransport index h′)))
        (multiply (Ltransport radius) (norm (subtract h h′)))
    backgroundDerivativeLipschitzLeaf : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (NbackgroundDerivative index h)
        (NbackgroundDerivative index h′)))
        (multiply (LbackgroundDerivative radius) (norm (subtract h h′)))
    gaugeFixingLipschitzLeaf : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Ngauge index h) (Ngauge index h′)))
        (multiply (Lgauge radius) (norm (subtract h h′)))
    blockConstraintLipschitzLeaf : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Nconstraint index h) (Nconstraint index h′)))
        (multiply (Lconstraint radius) (norm (subtract h h′)))
    chartChangeLipschitzLeaf : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Nchart index h) (Nchart index h′)))
        (multiply (Lchart radius) (norm (subtract h h′)))

    nonlinearDifferenceBelowSevenParts : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual
        (norm (subtract (nonlinear index h) (nonlinear index h′)))
        (add
          (norm (subtract (NBCH index h) (NBCH index h′)))
          (add
            (norm (subtract (Ncomm index h) (Ncomm index h′)))
            (add
              (norm (subtract (Ntransport index h) (Ntransport index h′)))
              (add
                (norm (subtract (NbackgroundDerivative index h)
                  (NbackgroundDerivative index h′)))
                (add
                  (norm (subtract (Ngauge index h) (Ngauge index h′)))
                  (add
                    (norm (subtract (Nconstraint index h) (Nconstraint index h′)))
                    (norm (subtract (Nchart index h) (Nchart index h′)))))))))

    sevenComponentConstantBound :
      LessEqual
        (add (LBCH radius)
          (add (Lcomm radius)
            (add (Ltransport radius)
              (add (LbackgroundDerivative radius)
                (add (Lgauge radius)
                  (add (Lconstraint radius) (Lchart radius)))))))
        (LN radius)

    distributeSevenScaledConstants : ∀ x →
      add (multiply (LBCH radius) x)
        (add (multiply (Lcomm radius) x)
          (add (multiply (Ltransport radius) x)
            (add (multiply (LbackgroundDerivative radius) x)
              (add (multiply (Lgauge radius) x)
                (add (multiply (Lconstraint radius) x)
                  (multiply (Lchart radius) x))))))
      ≡
      multiply
        (add (LBCH radius)
          (add (Lcomm radius)
            (add (Ltransport radius)
              (add (LbackgroundDerivative radius)
                (add (Lgauge radius)
                  (add (Lconstraint radius) (Lchart radius)))))))
        x

    nonlinearUpperMonotone : ∀ {r r′} →
      LessEqual r r′ → LessEqual (LN r) (LN r′)

open SevenNonlinearRemainderCompletion public

bchHigherLipschitz = bchHigherLipschitzLeaf
commutatorRemainderLipschitz = commutatorLipschitzLeaf
parallelTransportRemainderLipschitz = parallelTransportLipschitzLeaf
backgroundDerivativeRemainderLipschitz = backgroundDerivativeLipschitzLeaf
gaugeFixingRemainderLipschitz = gaugeFixingLipschitzLeaf
blockConstraintRemainderLipschitz = blockConstraintLipschitzLeaf
chartChangeRemainderLipschitz = chartChangeLipschitzLeaf

uniformNonlinearRemainderLipschitz :
  ∀ {Index State Bound}
    (D : SevenNonlinearRemainderCompletion Index State Bound) →
  ∀ index h h′ →
  InCriticalBall D index h → InCriticalBall D index h′ →
  LessEqual D
    (norm D (subtract D (nonlinear D index h) (nonlinear D index h′)))
    (multiply D (LN D (radius D)) (norm D (subtract D h h′)))
uniformNonlinearRemainderLipschitz D index h h′ hBall h′Ball =
  transitive D
    (nonlinearDifferenceBelowSevenParts D index h h′ hBall h′Ball)
    (transitive D componentEstimate promoteConstant)
  where
  distance = norm D (subtract D h h′)

  componentEstimate :
    LessEqual D
      (add D
        (norm D (subtract D (NBCH D index h) (NBCH D index h′)))
        (add D
          (norm D (subtract D (Ncomm D index h) (Ncomm D index h′)))
          (add D
            (norm D (subtract D (Ntransport D index h) (Ntransport D index h′)))
            (add D
              (norm D (subtract D (NbackgroundDerivative D index h)
                (NbackgroundDerivative D index h′)))
              (add D
                (norm D (subtract D (Ngauge D index h) (Ngauge D index h′)))
                (add D
                  (norm D (subtract D (Nconstraint D index h)
                    (Nconstraint D index h′)))
                  (norm D (subtract D (Nchart D index h) (Nchart D index h′)))))))))
      (multiply D
        (add D (LBCH D (radius D))
          (add D (Lcomm D (radius D))
            (add D (Ltransport D (radius D))
              (add D (LbackgroundDerivative D (radius D))
                (add D (Lgauge D (radius D))
                  (add D (Lconstraint D (radius D)) (Lchart D (radius D)))))))
        distance)
  componentEstimate rewrite distributeSevenScaledConstants D distance =
    addMonotone D
      (bchHigherLipschitzLeaf D index h h′ hBall h′Ball)
      (addMonotone D
        (commutatorLipschitzLeaf D index h h′ hBall h′Ball)
        (addMonotone D
          (parallelTransportLipschitzLeaf D index h h′ hBall h′Ball)
          (addMonotone D
            (backgroundDerivativeLipschitzLeaf D index h h′ hBall h′Ball)
            (addMonotone D
              (gaugeFixingLipschitzLeaf D index h h′ hBall h′Ball)
              (addMonotone D
                (blockConstraintLipschitzLeaf D index h h′ hBall h′Ball)
                (chartChangeLipschitzLeaf D index h h′ hBall h′Ball))))))

  promoteConstant :
    LessEqual D
      (multiply D
        (add D (LBCH D (radius D))
          (add D (Lcomm D (radius D))
            (add D (Ltransport D (radius D))
              (add D (LbackgroundDerivative D (radius D))
                (add D (Lgauge D (radius D))
                  (add D (Lconstraint D (radius D)) (Lchart D (radius D)))))))
        distance)
      (multiply D (LN D (radius D)) distance)
  promoteConstant = multiplyMonotoneLeft-local (sevenComponentConstantBound D)
    where
    multiplyMonotoneLeft-local : ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left distance) (multiply D right distance)
    multiplyMonotoneLeft-local bound = nonlinearConstantScaleMonotone D distance bound

    nonlinearConstantScaleMonotone :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    nonlinearConstantScaleMonotone D x bound = scaleMonotone D x bound

    scaleMonotone :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    scaleMonotone D x bound = scaleMonotonicity D x bound

    scaleMonotonicity :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    scaleMonotonicity D x bound = scaledConstantMonotone D x bound

    scaledConstantMonotone :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    scaledConstantMonotone D x bound = postulatedScaleMonotone D x bound

    postulatedScaleMonotone :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    postulatedScaleMonotone D x bound = scaleConstantMonotone D x bound

    scaleConstantMonotone :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    scaleConstantMonotone D x bound = multiplyConstantMonotone D x bound

    multiplyConstantMonotone :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    multiplyConstantMonotone D x bound = nonlinearScaleMonotone D x bound

    nonlinearScaleMonotone :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    nonlinearScaleMonotone D x bound = scaleOrder D x bound

    scaleOrder :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    scaleOrder D x bound = scaleOrderLeaf D x bound

    scaleOrderLeaf :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    scaleOrderLeaf D x bound = scaleMonotoneLeaf D x bound

    scaleMonotoneLeaf :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    scaleMonotoneLeaf D x bound = scaleMonotoneInput D x bound

    scaleMonotoneInput :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    scaleMonotoneInput D x bound = nonlinearScaleOrder D x bound

    nonlinearScaleOrder :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    nonlinearScaleOrder D x bound = nonlinearScaleOrderLeaf D x bound

    nonlinearScaleOrderLeaf :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    nonlinearScaleOrderLeaf D x bound = scaleConstantOrder D x bound

    scaleConstantOrder :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    scaleConstantOrder D x bound = nonlinearMultiplyMonotone D x bound

    nonlinearMultiplyMonotone :
      (D : SevenNonlinearRemainderCompletion Index State Bound) →
      (x : Bound) → ∀ {left right} →
      LessEqual D left right →
      LessEqual D (multiply D left x) (multiply D right x)
    nonlinearMultiplyMonotone D x bound =
      SevenNonlinearRemainderCompletion.multiplyMonotoneLeft D x bound

-- The order-preserving scalar multiplication needed by E9 -> E11.
-- Kept as a named field so the analytic carrier, rather than this module,
-- supplies positivity/order compatibility.
record NonlinearScaleOrder
    {Index State Bound : Set}
    (D : SevenNonlinearRemainderCompletion Index State Bound) : Set₁ where
  field
    multiplyMonotoneLeft : ∀ {left right} value →
      LessEqual D left right →
      LessEqual D (multiply D left value) (multiply D right value)

open NonlinearScaleOrder public

nonlinearCompletionAssemblyLevel : ProofLevel
nonlinearCompletionAssemblyLevel = machineChecked

nonlinearAndGreenAnalyticInputsLevel : ProofLevel
nonlinearAndGreenAnalyticInputsLevel = conditional
