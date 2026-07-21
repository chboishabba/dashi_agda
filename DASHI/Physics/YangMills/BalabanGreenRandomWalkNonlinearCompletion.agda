module DASHI.Physics.YangMills.BalabanGreenRandomWalkNonlinearCompletion where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPatchRegimeHodgeUniformity using
  (PatchRegime; bulk; boundary; scaleInterface; corner; nestedRestriction)

------------------------------------------------------------------------
-- D. Green operator and random-walk estimates.
--
-- The analytic estimates remain proof-relevant leaves at the geometry and
-- real-analysis boundary.  The important structural correction is enforced:
-- fullGreen is the limit of the finite random-walk partial sums, rather than
-- being equated with every finite partial sum.
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

    -- D1--D5: regimewise reference Green bounds.
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

    -- D6--D10: regimewise first-derivative bounds.
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

    -- D11--D15: regimewise second-derivative bounds.
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

    -- D16: common constants.  The regime-indexed selectors below prevent the
    -- common bounds from drifting away from the five concrete constants.
    regimeGreenConstantsHaveCommonUpper :
      (r : PatchRegime) → LessEqual (greenConstant r) CG0
    regimeGradientConstantsHaveCommonUpper :
      (r : PatchRegime) → LessEqual (gradientConstant r) C∇G0
    regimeSecondGradientConstantsHaveCommonUpper :
      (r : PatchRegime) → LessEqual (secondGradientConstant r) C∇²G0

    -- D17: exact local-parametrix residual equation.
    localParametrixResidualEquation : ∀ index f →
      H index (localGreen index f) ≡ difference f (residual index f)

    -- D18--D22: regimewise weighted residual bounds.
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

    -- D23: selected safe aggregate.  A future disjoint-patch theorem may
    -- replace this sum by a maximum without changing the downstream surface.
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

    -- D26: mathematically correct Neumann representation.
    neumannSeriesRepresentsGreen : ∀ index f →
      fullGreen index f ≡ limit (λ n → partialRandomWalk index n f)

    -- D27.
    uniformCorrectionInverseBound : ∀ index f →
      LessEqual (weightedNorm (correctionInverse index f))
        (multiply Ccorr (weightedNorm f))
    correctionBoundBelowGeometricSeries :
      LessEqual Ccorr geometricCorrectionBound
    geometricCorrectionBoundIsOneOverOneMinusQ : Set

    -- D28: pointwise form of operator factorization.
    fullGreenFactorization : ∀ index f →
      fullGreen index f ≡ referenceGreen index (correctionInverse index f)
    gradientFullGreenFactorization : ∀ index f →
      gradientFullGreen index f ≡
      gradientGreen index (correctionInverse index f)
    secondGradientFullGreenFactorization : ∀ index f →
      secondGradientFullGreen index f ≡
      secondGradientGreen index (correctionInverse index f)

    -- D29: final full Green estimates with the product constants fixed here.
    uniformWeightedGreenBound : ∀ index f →
      LessEqual (weightedNorm (fullGreen index f))
        (multiply (multiply CG0 Ccorr) (weightedNorm f))
    uniformWeightedGradientGreenBound : ∀ index f →
      LessEqual (weightedNorm (gradientFullGreen index f))
        (multiply (multiply C∇G0 Ccorr) (weightedNorm f))
    uniformWeightedSecondGradientGreenBound : ∀ index f →
      LessEqual (weightedNorm (secondGradientFullGreen index f))
        (multiply (multiply C∇²G0 Ccorr) (weightedNorm f))

  greenConstant : PatchRegime → Bound
  greenConstant bulk = CG-bulk
  greenConstant boundary = CG-boundary
  greenConstant scaleInterface = CG-interface
  greenConstant corner = CG-corner
  greenConstant nestedRestriction = CG-nested

  gradientConstant : PatchRegime → Bound
  gradientConstant bulk = C∇G-bulk
  gradientConstant boundary = C∇G-boundary
  gradientConstant scaleInterface = C∇G-interface
  gradientConstant corner = C∇G-corner
  gradientConstant nestedRestriction = C∇G-nested

  secondGradientConstant : PatchRegime → Bound
  secondGradientConstant bulk = C∇²G-bulk
  secondGradientConstant boundary = C∇²G-boundary
  secondGradientConstant scaleInterface = C∇²G-interface
  secondGradientConstant corner = C∇²G-corner
  secondGradientConstant nestedRestriction = C∇²G-nested

open GreenRandomWalkCompletion public

------------------------------------------------------------------------
-- E. Nonlinear remainder estimates.
--
-- The seven component constants depend on the selected radius.  E11 is retained
-- as the assembled endpoint of E1--E10 because the generic Bound carrier does
-- not assume the ordered-semiring laws needed to reconstruct it silently.
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

    -- Concrete lower analytic inputs for E1 and E2.
    bchThirdOrderRemainderBound : Index → Set
    bchDerivativeDifferenceBound : Index → Set
    compactLieBracketInequality : Index → Set

    -- E1.
    bchHigherLipschitz : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (NBCH index h) (NBCH index h′)))
        (multiply (LBCH radius) (norm (subtract h h′)))

    -- E2.
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

    -- E8: exact seven-part majorization of the nonlinear difference.
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

    -- E9.
    sevenComponentConstantBound :
      LessEqual
        (add (LBCH radius)
          (add (Lcomm radius)
            (add (Ltransport radius)
              (add (LbackgroundDerivative radius)
                (add (Lgauge radius)
                  (add (Lconstraint radius) (Lchart radius)))))))
        (LN radius)

    -- E10.
    nonlinearUpperMonotone : ∀ {r r′} →
      LessEqual r r′ → LessEqual (LN r) (LN r′)

    -- E11: assembled endpoint consumed by the contraction theorem.
    uniformNonlinearRemainderLipschitz : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual
        (norm (subtract (nonlinear index h) (nonlinear index h′)))
        (multiply (LN radius) (norm (subtract h h′)))

open SevenNonlinearRemainderCompletion public

------------------------------------------------------------------------
-- One coherent package prevents Green constants, residual data, and nonlinear
-- constants from being mixed across unrelated patch families or radii.
------------------------------------------------------------------------

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
