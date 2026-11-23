module DASHI.Physics.YangMills.YMClayW0OriginalF19CandidateEquation171TExact where

------------------------------------------------------------------------
-- W0: finite original SU(N) Wilson/F19 marked conditional Haar mass
-- as an inhabitant of the EXISTING CMP122 Eq.(1.71) T SEMANTICS TYPE.
--
-- Crucial source boundary: This is a CANONICAL CANDIDATE T of the
-- original F19 fine link pairs and ALL 896 coupled spectators.
-- It is NOT yet Bałaban's physically selected Eq.(1.71) local T:
-- source Omega/Lambda/S domains, delta constraints, background,
-- FP/gauge fixing, R modifications and scale history still need a
-- source identification theorem. The Nat scale here is deliberately
-- ignored: no fake running coupling or all-scale RG result.
--
-- Reuse F19's arbitrary-integrand Haar disintegration and source
-- Wilson weight. No new integral law, factorization or quotient.
-- Source written: pinned Agda kernel/transitive trust pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base using (Vec; _∷_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNWeightedDisjointPairFibreReparamExact as Fibre
import DASHI.Physics.YangMills.YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact as Original
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (source : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
    (linear : Ordered.OneLinkOrderedHaarAlgebra source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Pair : Set
  Pair = Fibre.Pair theory source bilateral

  FineTest : Set
  FineTest = Vec Pair 64 → Vec Link 896 → ℝ

  FinePairField : Set
  FinePairField = Vec Pair 64

  SlowField : Set
  SlowField = Vec Link 64

  -- The fixed-coarse source integral is EXACTLY the original
  -- F19 64-pair constrained Haar integral. No new P3 quadrature.
  sourceConstrainedHaarT :
    SlowField → (FinePairField → ℝ) → ℝ
  sourceConstrainedHaarT coarse integrand =
    Fibre.actualAllPairsFibreIntegral
      theory source bilateral integrand coarse

  ----------------------------------------------------------------------
  -- TRUE ORIGINAL F19 LOCALIZED ONE-PAIR T STEP, NOT A MODEL STEP.
  --
  -- At the first one of 64 native ordered pair-fibres, integrate its
  -- actual SU(N) Haar V.  Hold coarse W fixed, feed the resulting
  -- original pair (W V^-1,V) into the ORIGINAL 63-fibre continuation.
  -- The continuation may couple arbitrarily to all other pairs.
  -- No tensor factorization of the physical Wilson weight is assumed.
  ----------------------------------------------------------------------

  sourceFirstPairTStep :
    Link → Vec Link 63 → (FinePairField → ℝ) → ℝ
  sourceFirstPairTStep headCoarse tailCoarse integrand =
    Haar.integrateOne source
      (λ headFibre →
        Fibre.actualAllPairsFibreIntegral
          theory source bilateral
          (λ restPairs →
            integrand
              (Fibre.pairFromCoarseAndFibre
                theory source bilateral headCoarse headFibre
               ∷ restPairs))
          tailCoarse)

  -- This is an actual geometry-respecting one-step source equality:
  -- the left side unfolds directly into first-conditional-pair T
  -- followed by the remaining 63 source pair-fibre T operations.
  -- Both sides are the same original F19 source for EVERY integrand.
  sourceF19FirstPairLocalizationExact :
    (headCoarse : Link)
    (tailCoarse : Vec Link 63)
    (integrand : FinePairField → ℝ) →
    sourceConstrainedHaarT (headCoarse ∷ tailCoarse) integrand
    ≡ sourceFirstPairTStep headCoarse tailCoarse integrand
  sourceF19FirstPairLocalizationExact headCoarse tailCoarse integrand =
    refl

  -- 896 spectators are integrated inside the pair integrand.
  -- This is NOT an assertion that spectators are independent.
  spectatorMarginalOfFineIntegrand :
    FineTest → FinePairField → ℝ
  spectatorMarginalOfFineIntegrand integrand pairs =
    Haar.productIntegral source
      (λ spectators → integrand pairs spectators)

  -- Definitionally the SAME source conditional four-coefficient density
  -- already constructed in YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact.
  candidateF19Mass : FineTest → SlowField → ℝ
  candidateF19Mass integrand coarse =
    sourceConstrainedHaarT coarse
      (spectatorMarginalOfFineIntegrand integrand)

  -- Both original fine marks and all 896 interacting spectators travel
  -- through that same ordered local step. Crucially F*G stays within
  -- the continuation, not multiplied after the two Haar integrations.
  sourceF19MarkedFirstPairLocalizationExact :
    (headCoarse : Link)
    (tailCoarse : Vec Link 63)
    (integrand : FineTest) →
    candidateF19Mass integrand (headCoarse ∷ tailCoarse)
    ≡
    sourceFirstPairTStep headCoarse tailCoarse
      (spectatorMarginalOfFineIntegrand integrand)
  sourceF19MarkedFirstPairLocalizationExact
    headCoarse tailCoarse integrand =
    sourceF19FirstPairLocalizationExact
      headCoarse tailCoarse
      (spectatorMarginalOfFineIntegrand integrand)

  candidateMassIsExistingOriginalF19 :
    (integrand : FineTest) (coarse : SlowField) →
    candidateF19Mass integrand coarse
    ≡
    Original.originalF19CoefficientDensity
      theory traceData exponential beta source bilateral linear
      integrand coarse
  candidateMassIsExistingOriginalF19 integrand coarse = refl

  ----------------------------------------------------------------------
  -- W0 geometry correction: one FIXED original Wilson density and a
  -- FUNCTIONAL argument. Four marks do NOT define four physical Ts.
  -- The underlying F19 Haar fibre and its 896 spectator integral are
  -- identical for every observable, including F and G.
  ----------------------------------------------------------------------

  sourceFixedWilsonDensity : FineTest
  sourceFixedWilsonDensity =
    Original.originalFineWilsonWeight
      theory traceData exponential beta source bilateral linear

  sourceFixedWilsonT :
    FineTest → SlowField → ℝ
  sourceFixedWilsonT observable coarse =
    candidateF19Mass
      (Original.originalWilsonFineF
        theory traceData exponential beta source bilateral linear
        observable)
      coarse

  -- Keep the actual W*F*G multiplication association selected by
  -- Original.originalWilsonFineFG. No fake independence or implicit
  -- associativity proof is required to retain its exact moment.
  sourceFixedWilsonTTwoMarks :
    FineTest → FineTest → SlowField → ℝ
  sourceFixedWilsonTTwoMarks left right coarse =
    candidateF19Mass
      (Original.originalWilsonFineFG
        theory traceData exponential beta source bilateral linear
        left right)
      coarse

  -- Generic Eq171 semantic record accepts an evaluated integrand.
  -- This is only a carrier adapter: its field name
  -- equation171ExponentialDensity does NOT prove that a marked
  -- spectator marginal is Bałaban's localized exponential action.

  -- The existing real-valued Eq.(1.71) record can express this
  -- candidate Haar constrained T without any rational embedding.
  -- Scale is intentionally inert at this original side-four cutoff.
  originalF19CandidateEquation171 :
    FineTest →
    Eq171.CMP122Equation171TOperationSemantics FinePairField SlowField
  originalF19CandidateEquation171 integrand = record
    { Eq171.CMP122Equation171TOperationSemantics.equation171ExponentialDensity =
        λ cutoff coarse pairs →
          spectatorMarginalOfFineIntegrand integrand pairs
    ; Eq171.CMP122Equation171TOperationSemantics.equation171ConstrainedIntegral =
        λ cutoff coarse values →
          sourceConstrainedHaarT coarse values
    ; Eq171.CMP122Equation171TOperationSemantics.sourceTOperationMass =
        λ cutoff coarse →
          candidateF19Mass integrand coarse
    ; Eq171.CMP122Equation171TOperationSemantics.equation171DefinesTOperationMass =
        λ cutoff coarse → refl
    }

  originalF19UnmarkedEquation171 :
    Eq171.CMP122Equation171TOperationSemantics FinePairField SlowField
  originalF19UnmarkedEquation171 =
    originalF19CandidateEquation171 sourceFixedWilsonDensity

  -- Only this finite candidate source and its F19 normalization,
  -- not the selected CMP119 step / E-R-B-V physical dictionary.
  originalF19CandidateSourceTIsPhysicalFineIntegral :
    (integrand : FineTest) →
    Original.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      integrand
    ≡
    Haar.productIntegral source
      (λ coarse →
        Eq171.sourceTOperationMass
          (originalF19CandidateEquation171 integrand) 0 coarse)
  originalF19CandidateSourceTIsPhysicalFineIntegral integrand =
    Original.originalFineCoefficientEqualsF19
      theory traceData exponential beta source bilateral linear integrand

  -- Four explicit original source moment columns, one SAME finite
  -- conditional Haar T, with both unique marks still inside that T.
  sourceK0 : SlowField → ℝ
  sourceK0 =
    candidateF19Mass
      (Original.originalFineWilsonWeight
        theory traceData exponential beta source bilateral linear)

  -- Pointwise the same FIXED unmarked Eq171 candidate mass.
  -- This is not an identification with the source-localized CMP122 T.
  sourceK0IsUnmarkedEq171 :
    (coarse : SlowField) →
    sourceK0 coarse
    ≡ Eq171.sourceTOperationMass
        originalF19UnmarkedEquation171 0 coarse
  sourceK0IsUnmarkedEq171 coarse = refl

  sourceKF : FineTest → SlowField → ℝ
  sourceKF left = sourceFixedWilsonT left

  sourceKG : FineTest → SlowField → ℝ
  sourceKG right = sourceFixedWilsonT right

  sourceKFG : FineTest → FineTest → SlowField → ℝ
  sourceKFG left right = sourceFixedWilsonTTwoMarks left right

  -- The same Haar reindex theorem proves each source column.
  physicalFineZEqualsCoarseCandidateT :
    Original.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (Original.originalFineWilsonWeight
        theory traceData exponential beta source bilateral linear)
    ≡ Haar.productIntegral source sourceK0
  physicalFineZEqualsCoarseCandidateT =
    originalF19CandidateSourceTIsPhysicalFineIntegral
      (Original.originalFineWilsonWeight
        theory traceData exponential beta source bilateral linear)

  physicalFineFEqualsCoarseCandidateT :
    (left : FineTest) →
    Original.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (Original.originalWilsonFineF
        theory traceData exponential beta source bilateral linear left)
    ≡ Haar.productIntegral source (sourceKF left)
  physicalFineFEqualsCoarseCandidateT left =
    originalF19CandidateSourceTIsPhysicalFineIntegral
      (Original.originalWilsonFineF
        theory traceData exponential beta source bilateral linear left)

  physicalFineGEqualsCoarseCandidateT :
    (right : FineTest) →
    Original.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (Original.originalWilsonFineF
        theory traceData exponential beta source bilateral linear right)
    ≡ Haar.productIntegral source (sourceKG right)
  physicalFineGEqualsCoarseCandidateT right =
    originalF19CandidateSourceTIsPhysicalFineIntegral
      (Original.originalWilsonFineF
        theory traceData exponential beta source bilateral linear right)

  physicalFineFGEqualsCoarseCandidateT :
    (left right : FineTest) →
    Original.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (Original.originalWilsonFineFG
        theory traceData exponential beta source bilateral linear
        left right)
    ≡ Haar.productIntegral source (sourceKFG left right)
  physicalFineFGEqualsCoarseCandidateT left right =
    originalF19CandidateSourceTIsPhysicalFineIntegral
      (Original.originalWilsonFineFG
        theory traceData exponential beta source bilateral linear
        left right)

  -- No sourceKF*sourceKG/sourceK0 shortcut: sourceKFG retains the
  -- original fine-fibre mixed coefficient, including 896 spectators.


  ----------------------------------------------------------------------
  -- W0 PHYSICAL CHANGE-OF-AVERAGING TEST: Q NEED NOT EQUAL PAIR W.
  --
  -- CMP98's nonlinear, transported-contour block average Q(U) and
  -- the straight original R445 pair holonomy W(U) are different
  -- functions in general. F19 is an arbitrary-integrand theorem:
  -- carry any selected Q(pairs,spectators) THROUGH the ORIGINAL
  -- 64 native-pair and 896 spectator Haar disintegration.
  --
  -- The parameter "average" is a real original fine-field function;
  -- supplying CMP98's literal Q and its domain/gauge constraints is
  -- a further named source identification, not silently assumed here.
  ----------------------------------------------------------------------

  sourceAverageObservable :
    (FinePairField → Vec Link 896 → SlowField) →
    (SlowField → ℝ) →
    FineTest
  sourceAverageObservable average observable pairs spectators =
    observable (average pairs spectators)

  -- 1 marked Q-observable, ONE fixed original physical Wilson weight.
  -- No Q=W premise, nor a change of variable on coarse W whose
  -- Jacobian is presumed to be unity.
  originalWilsonAverageMarkedNumeratorEqualsOriginalF19 :
    (average : FinePairField → Vec Link 896 → SlowField)
    (observable : SlowField → ℝ) →
    Original.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (Original.originalWilsonFineF
        theory traceData exponential beta source bilateral linear
        (sourceAverageObservable average observable))
    ≡
    Haar.productIntegral source
      (sourceFixedWilsonT
        (sourceAverageObservable average observable))
  originalWilsonAverageMarkedNumeratorEqualsOriginalF19
    average observable =
    originalF19CandidateSourceTIsPhysicalFineIntegral
      (Original.originalWilsonFineF
        theory traceData exponential beta source bilateral linear
        (sourceAverageObservable average observable))

  -- Two marked Q-observables; their product is inside the SAME
  -- physical conditional fibre, including all interacting spectators.
  originalWilsonTwoAverageMarksEqualsOriginalF19 :
    (average : FinePairField → Vec Link 896 → SlowField)
    (left right : SlowField → ℝ) →
    Original.originalFineCoefficient
      theory traceData exponential beta source bilateral linear
      (Original.originalWilsonFineFG
        theory traceData exponential beta source bilateral linear
        (sourceAverageObservable average left)
        (sourceAverageObservable average right))
    ≡
    Haar.productIntegral source
      (sourceFixedWilsonTTwoMarks
        (sourceAverageObservable average left)
        (sourceAverageObservable average right))
  originalWilsonTwoAverageMarksEqualsOriginalF19
    average left right =
    originalF19CandidateSourceTIsPhysicalFineIntegral
      (Original.originalWilsonFineFG
        theory traceData exponential beta source bilateral linear
        (sourceAverageObservable average left)
        (sourceAverageObservable average right))

  -- The two statements above are already unconditional within the
  -- existing certified Haar algebra for the original selected
  -- side-four cutoff. They do not identify the selected Q with
  -- CMP98 Eq.(15) nor derive CMP119 scale-localized T^(j).
