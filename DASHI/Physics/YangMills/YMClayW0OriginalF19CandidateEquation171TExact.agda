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
open import Data.Vec.Base using (Vec)
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

  originalF19UnmarkedEquation171 :
    Eq171.CMP122Equation171TOperationSemantics FinePairField SlowField
  originalF19UnmarkedEquation171 =
    originalF19CandidateEquation171 sourceFixedWilsonDensity

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
