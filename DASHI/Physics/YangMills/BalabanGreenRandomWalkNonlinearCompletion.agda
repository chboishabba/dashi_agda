module DASHI.Physics.YangMills.BalabanGreenRandomWalkNonlinearCompletion where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPatchRegimeHodgeUniformity using
  (PatchRegime; bulk; boundary; scaleInterface; corner; nestedRestriction)

------------------------------------------------------------------------
-- D. Green operator and random-walk estimates.
--
-- Analytic estimates remain proof-relevant leaves.  The structural correction
-- is exact: fullGreen is the limit of finite random-walk partial sums, not every
-- finite partial sum.
------------------------------------------------------------------------

record GreenRandomWalkCompletion (Index State Bound : Set) : Set₁ where
  field
    regime : Index → PatchRegime

    H localGreen referenceGreen gradientGreen secondGradientGreen residual
      fullGreen gradientFullGreen secondGradientFullGreen correctionInverse :
      Index → State → State

    residualPower partialRandomWalk tail : Index → Nat → State → State
    limit : (Nat → State) → State
    difference : State → State → State

    weightedNorm : State → Bound
    add multiply : Bound → Bound → Bound
    pow : Bound → Nat → Bound
    one : Bound
    LessEqual StrictlyBelow : Bound → Bound → Set

    CG-bulk CG-boundary CG-interface CG-corner CG-nested CG0 : Bound
    C∇G-bulk C∇G-boundary C∇G-interface C∇G-corner C∇G-nested C∇G0 : Bound
    C∇²G-bulk C∇²G-boundary C∇²G-interface C∇²G-corner C∇²G-nested C∇²G0 : Bound
    qBulk qBoundary qInterface qCorner qNested q : Bound
    CG-tail Ccorr geometricCorrectionBound : Bound

    -- D1--D5.
    bulkGreenBound : ∀ index f → regime index ≡ bulk →
      LessEqual (weightedNorm (referenceGreen index f))
        (multiply CG-bulk (weightedNorm f))
    boundaryGreenBound : ∀ index f → regime index ≡ boundary →
      LessEqual (weightedNorm (referenceGreen index f))
        (multiply CG-boundary (weightedNorm f))
    interfaceGreenBound : ∀ index f → regime index ≡ scaleInterface →
      LessEqual (weightedNorm (referenceGreen index f))
        (multiply CG-interface (weightedNorm f))
    cornerGreenBound : ∀ index f → regime index ≡ corner →
      LessEqual (weightedNorm (referenceGreen index f))
        (multiply CG-corner (weightedNorm f))
    nestedGreenBound : ∀ index f → regime index ≡ nestedRestriction →
      LessEqual (weightedNorm (referenceGreen index f))
        (multiply CG-nested (weightedNorm f))

    -- D6--D10.
    bulkGradientGreenBound : ∀ index f → regime index ≡ bulk →
      LessEqual (weightedNorm (gradientGreen index f))
        (multiply C∇G-bulk (weightedNorm f))
    boundaryGradientGreenBound : ∀ index f → regime index ≡ boundary →
      LessEqual (weightedNorm (gradientGreen index f))
        (multiply C∇G-boundary (weightedNorm f))
    interfaceGradientGreenBound : ∀ index f → regime index ≡ scaleInterface →
      LessEqual (weightedNorm (gradientGreen index f))
        (multiply C∇G-interface (weightedNorm f))
    cornerGradientGreenBound : ∀ index f → regime index ≡ corner →
      LessEqual (weightedNorm (gradientGreen index f))
        (multiply C∇G-corner (weightedNorm f))
    nestedGradientGreenBound : ∀ index f → regime index ≡ nestedRestriction →
      LessEqual (weightedNorm (gradientGreen index f))
        (multiply C∇G-nested (weightedNorm f))

    -- D11--D15.
    bulkSecondGradientGreenBound : ∀ index f → regime index ≡ bulk →
      LessEqual (weightedNorm (secondGradientGreen index f))
        (multiply C∇²G-bulk (weightedNorm f))
    boundarySecondGradientGreenBound : ∀ index f → regime index ≡ boundary →
      LessEqual (weightedNorm (secondGradientGreen index f))
        (multiply C∇²G-boundary (weightedNorm f))
    interfaceSecondGradientGreenBound : ∀ index f → regime index ≡ scaleInterface →
      LessEqual (weightedNorm (secondGradientGreen index f))
        (multiply C∇²G-interface (weightedNorm f))
    cornerSecondGradientGreenBound : ∀ index f → regime index ≡ corner →
      LessEqual (weightedNorm (secondGradientGreen index f))
        (multiply C∇²G-corner (weightedNorm f))
    nestedSecondGradientGreenBound : ∀ index f → regime index ≡ nestedRestriction →
      LessEqual (weightedNorm (secondGradientGreen index f))
        (multiply C∇²G-nested (weightedNorm f))

    -- D16 leaves, assembled into regime-indexed theorems below.
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

    bulkSecondGradientBelowCommon : LessEqual C∇²G-bulk C∇²G0
    boundarySecondGradientBelowCommon : LessEqual C∇²G-boundary C∇²G0
    interfaceSecondGradientBelowCommon : LessEqual C∇²G-interface C∇²G0
    cornerSecondGradientBelowCommon : LessEqual C∇²G-corner C∇²G0
    nestedSecondGradientBelowCommon : LessEqual C∇²G-nested C∇²G0

    -- D17.
    localParametrixResidualEquation : ∀ index f →
      H index (localGreen index f) ≡ difference f (residual index f)

    -- D18--D22.
    bulkResidualBound : ∀ index f → regime index ≡ bulk →
      LessEqual (weightedNorm (residual index f))
        (multiply qBulk (weightedNorm f))
    boundaryResidualBound : ∀ index f → regime index ≡ boundary →
      LessEqual (weightedNorm (residual index f))
        (multiply qBoundary (weightedNorm f))
    interfaceResidualBound : ∀ index f → regime index ≡ scaleInterface →
      LessEqual (weightedNorm (residual index f))
        (multiply qInterface (weightedNorm f))
    cornerResidualBound : ∀ index f → regime index ≡ corner →
      LessEqual (weightedNorm (residual index f))
        (multiply qCorner (weightedNorm f))
    nestedResidualBound : ∀ index f → regime index ≡ nestedRestriction →
      LessEqual (weightedNorm (residual index f))
        (multiply qNested (weightedNorm f))

    -- D23.  The current safe aggregate is the sum; a disjoint-patch producer
    -- may later replace this by a maximum without changing D24--D29.
    patchResidualSumBelowQ :
      LessEqual
        (add qBulk (add qBoundary (add qInterface (add qCorner qNested))))
        q
    qStrict : StrictlyBelow q one

    -- D24--D25.
    residualPowerBound : ∀ index n f →
      LessEqual (weightedNorm (residualPower index n f))
        (multiply (pow q n) (weightedNorm f))
    randomWalkTailBound : ∀ index n f →
      LessEqual (weightedNorm (tail index n f))
        (multiply (multiply CG-tail (pow q n)) (weightedNorm f))

    -- D26.
    neumannSeriesRepresentsGreen : ∀ index f →
      fullGreen index f ≡ limit (λ n → partialRandomWalk index n f)

    -- D27.
    uniformCorrectionInverseBound : ∀ index f →
      LessEqual (weightedNorm (correctionInverse index f))
        (multiply Ccorr (weightedNorm f))
    correctionBoundBelowGeometricSeries :
      LessEqual Ccorr geometricCorrectionBound
    geometricCorrectionBoundIsOneOverOneMinusQ : Set

    -- D28, pointwise operator equality.
    fullGreenFactorization : ∀ index f →
      fullGreen index f ≡ referenceGreen index (correctionInverse index f)
    gradientFullGreenFactorization : ∀ index f →
      gradientFullGreen index f ≡ gradientGreen index (correctionInverse index f)
    secondGradientFullGreenFactorization : ∀ index f →
      secondGradientFullGreen index f ≡
      secondGradientGreen index (correctionInverse index f)

    -- D29, with constants CG0*Ccorr, C∇G0*Ccorr and C∇²G0*Ccorr.
    uniformWeightedGreenBound : ∀ index f →
      LessEqual (weightedNorm (fullGreen index f))
        (multiply (multiply CG0 Ccorr) (weightedNorm f))
    uniformWeightedGradientGreenBound : ∀ index f →
      LessEqual (weightedNorm (gradientFullGreen index f))
        (multiply (multiply C∇G0 Ccorr) (weightedNorm f))
    uniformWeightedSecondGradientGreenBound : ∀ index f →
      LessEqual (weightedNorm (secondGradientFullGreen index f))
        (multiply (multiply C∇²G0 Ccorr) (weightedNorm f))

open GreenRandomWalkCompletion public

greenConstant :
  ∀ {Index State Bound} →
  GreenRandomWalkCompletion Index State Bound → PatchRegime → Bound
greenConstant D bulk = CG-bulk D
greenConstant D boundary = CG-boundary D
greenConstant D scaleInterface = CG-interface D
greenConstant D corner = CG-corner D
greenConstant D nestedRestriction = CG-nested D

gradientConstant :
  ∀ {Index State Bound} →
  GreenRandomWalkCompletion Index State Bound → PatchRegime → Bound
gradientConstant D bulk = C∇G-bulk D
gradientConstant D boundary = C∇G-boundary D
gradientConstant D scaleInterface = C∇G-interface D
gradientConstant D corner = C∇G-corner D
gradientConstant D nestedRestriction = C∇G-nested D

secondGradientConstant :
  ∀ {Index State Bound} →
  GreenRandomWalkCompletion Index State Bound → PatchRegime → Bound
secondGradientConstant D bulk = C∇²G-bulk D
secondGradientConstant D boundary = C∇²G-boundary D
secondGradientConstant D scaleInterface = C∇²G-interface D
secondGradientConstant D corner = C∇²G-corner D
secondGradientConstant D nestedRestriction = C∇²G-nested D

regimeGreenConstantsHaveCommonUpper :
  ∀ {Index State Bound}
    (D : GreenRandomWalkCompletion Index State Bound) (r : PatchRegime) →
  LessEqual D (greenConstant D r) (CG0 D)
regimeGreenConstantsHaveCommonUpper D bulk = bulkGreenBelowCommon D
regimeGreenConstantsHaveCommonUpper D boundary = boundaryGreenBelowCommon D
regimeGreenConstantsHaveCommonUpper D scaleInterface = interfaceGreenBelowCommon D
regimeGreenConstantsHaveCommonUpper D corner = cornerGreenBelowCommon D
regimeGreenConstantsHaveCommonUpper D nestedRestriction = nestedGreenBelowCommon D

regimeGradientConstantsHaveCommonUpper :
  ∀ {Index State Bound}
    (D : GreenRandomWalkCompletion Index State Bound) (r : PatchRegime) →
  LessEqual D (gradientConstant D r) (C∇G0 D)
regimeGradientConstantsHaveCommonUpper D bulk = bulkGradientBelowCommon D
regimeGradientConstantsHaveCommonUpper D boundary = boundaryGradientBelowCommon D
regimeGradientConstantsHaveCommonUpper D scaleInterface = interfaceGradientBelowCommon D
regimeGradientConstantsHaveCommonUpper D corner = cornerGradientBelowCommon D
regimeGradientConstantsHaveCommonUpper D nestedRestriction = nestedGradientBelowCommon D

regimeSecondGradientConstantsHaveCommonUpper :
  ∀ {Index State Bound}
    (D : GreenRandomWalkCompletion Index State Bound) (r : PatchRegime) →
  LessEqual D (secondGradientConstant D r) (C∇²G0 D)
regimeSecondGradientConstantsHaveCommonUpper D bulk = bulkSecondGradientBelowCommon D
regimeSecondGradientConstantsHaveCommonUpper D boundary = boundarySecondGradientBelowCommon D
regimeSecondGradientConstantsHaveCommonUpper D scaleInterface = interfaceSecondGradientBelowCommon D
regimeSecondGradientConstantsHaveCommonUpper D corner = cornerSecondGradientBelowCommon D
regimeSecondGradientConstantsHaveCommonUpper D nestedRestriction = nestedSecondGradientBelowCommon D

------------------------------------------------------------------------
-- E. Seven radius-dependent nonlinear mechanisms.
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

    radius : Bound
    LBCH Lcomm Ltransport LbackgroundDerivative Lgauge Lconstraint Lchart LN :
      Bound → Bound

    bchThirdOrderRemainderBound : Index → Set
    bchDerivativeDifferenceBound : Index → Set
    compactLieBracketInequality : Index → Set

    -- E1--E2.
    bchHigherLipschitz : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (NBCH index h) (NBCH index h′)))
        (multiply (LBCH radius) (norm (subtract h h′)))
    commutatorRemainderLipschitz : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Ncomm index h) (Ncomm index h′)))
        (multiply (Lcomm radius) (norm (subtract h h′)))

    -- E3--E7.
    parallelTransportRemainderLipschitz : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Ntransport index h) (Ntransport index h′)))
        (multiply (Ltransport radius) (norm (subtract h h′)))
    backgroundDerivativeRemainderLipschitz : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual
        (norm (subtract (NbackgroundDerivative index h)
          (NbackgroundDerivative index h′)))
        (multiply (LbackgroundDerivative radius) (norm (subtract h h′)))
    gaugeFixingRemainderLipschitz : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Ngauge index h) (Ngauge index h′)))
        (multiply (Lgauge radius) (norm (subtract h h′)))
    blockConstraintRemainderLipschitz : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Nconstraint index h) (Nconstraint index h′)))
        (multiply (Lconstraint radius) (norm (subtract h h′)))
    chartChangeRemainderLipschitz : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Nchart index h) (Nchart index h′)))
        (multiply (Lchart radius) (norm (subtract h h′)))

    -- E8.
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
                    (norm (subtract (Nconstraint index h)
                      (Nconstraint index h′)))
                    (norm (subtract (Nchart index h) (Nchart index h′)))))))))

    -- E9--E10.
    sevenComponentConstantBound :
      LessEqual
        (add (LBCH radius)
          (add (Lcomm radius)
            (add (Ltransport radius)
              (add (LbackgroundDerivative radius)
                (add (Lgauge radius)
                  (add (Lconstraint radius) (Lchart radius)))))))
        (LN radius)
    nonlinearUpperMonotone : ∀ {r r′} →
      LessEqual r r′ → LessEqual (LN r) (LN r′)

    -- E11.  This is the exact assembled endpoint consumed by contraction.
    uniformNonlinearRemainderLipschitz : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual
        (norm (subtract (nonlinear index h) (nonlinear index h′)))
        (multiply (LN radius) (norm (subtract h h′)))

open SevenNonlinearRemainderCompletion public

record GreenNonlinearAnalyticCompletion
    (Index State Bound : Set) : Set₁ where
  field
    greenRandomWalk : GreenRandomWalkCompletion Index State Bound
    nonlinearRemainder : SevenNonlinearRemainderCompletion Index State Bound

open GreenNonlinearAnalyticCompletion public

greenRandomWalkAssemblyLevel : ProofLevel
greenRandomWalkAssemblyLevel = machineChecked

greenRandomWalkEstimateInputsLevel : ProofLevel
greenRandomWalkEstimateInputsLevel = conditional

sevenNonlinearAssemblyLevel : ProofLevel
sevenNonlinearAssemblyLevel = machineChecked

sevenNonlinearEstimateInputsLevel : ProofLevel
sevenNonlinearEstimateInputsLevel = conditional
