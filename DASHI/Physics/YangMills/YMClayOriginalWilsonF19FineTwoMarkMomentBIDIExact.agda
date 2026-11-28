module DASHI.Physics.YangMills.YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact where

------------------------------------------------------------------------
-- ORIGINAL P0 / F19 : fine-observable four-moment receiver.
--
-- Do NOT replace the existing coarse-only two-mark theorem.  The
-- original F19 effective source already preserves marks F(W),G(W)
-- on the 64 ordered noncommutative coarse holonomies.
--
-- Here F,G may depend on the full actual 64 fine pairs and all 896
-- spectators. Their four moments (1,F,G,FG) MUST be transported as
-- four weighted coefficients, not as a product of two separately
-- fibre-averaged coarse marks. The same source Wilson weight and
-- all existing Haar pair reparametrizations are reused.
--
-- Compiles EXACT finite source integrals.  No claims about physical
-- KP smallness, W3 clustering, all-cutoff continuum or OS spectrum.
-- Agda kernel acceptance of this new owner remains pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (trans; cong₂)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceCoreExact as Trace
import DASHI.Physics.YangMills.YMClayStrictPositiveRealExponentialCoreExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNWeightedDisjointPairFibreReparamExact as Fibre
import DASHI.Physics.YangMills.YMClayOriginalWilsonF19ConcreteWeightExact as Original

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

  CoarseTest : Set
  CoarseTest = Vec Link 64 → ℝ

  originalFineWilsonWeight : FineTest
  originalFineWilsonWeight =
    Original.physicalWeight theory traceData exponential beta
      source bilateral linear

  -- One canonical coefficient integrand; all four marked moments are
  -- specializations of the SAME original 1024-bond sorted Wilson weight.
  originalFineCoefficient : FineTest → ℝ
  originalFineCoefficient integrand =
    Fibre.finePairsIntegral theory source bilateral
      (λ pairs →
        Haar.productIntegral source
          (λ spectators → integrand pairs spectators))

  originalF19CoefficientDensity : FineTest → CoarseTest
  originalF19CoefficientDensity integrand =
    Fibre.actualAllPairsFibreIntegral theory source bilateral
      (λ pairs →
        Haar.productIntegral source
          (λ spectators → integrand pairs spectators))

  originalF19Coefficient : FineTest → ℝ
  originalF19Coefficient integrand =
    Haar.productIntegral source (originalF19CoefficientDensity integrand)

  -- Reuse the two existing ORIGINAL all-arbitrary-integrand theorems.
  -- No factorization, new probability measure or fresh Haar axiom.
  originalFineCoefficientEqualsF19 :
    ∀ integrand →
    originalFineCoefficient integrand
    ≡ originalF19Coefficient integrand
  originalFineCoefficientEqualsF19 integrand =
    trans
      (Fibre.selectedSideFour64Pair896SpectatorChange
        theory source bilateral integrand)
      (Fibre.originalInterleavedIntegralIsCoarseFibre
        theory source bilateral
        (λ pairs →
          Haar.productIntegral source
            (λ spectators → integrand pairs spectators)))

  originalWilsonFineF : FineTest → FineTest
  originalWilsonFineF observable pairs spectators =
    originalFineWilsonWeight pairs spectators *ℝ
      observable pairs spectators

  originalWilsonFineFG : FineTest → FineTest → FineTest
  originalWilsonFineFG left right pairs spectators =
    (originalFineWilsonWeight pairs spectators *ℝ
      left pairs spectators) *ℝ right pairs spectators

  -- Four coefficients of the original two-source affine generating
  -- polynomial, with the F,G product inside the SAME F19 fibre.
  originalPhysicalF19Z :
    originalFineCoefficient originalFineWilsonWeight
    ≡ originalF19Coefficient originalFineWilsonWeight
  originalPhysicalF19Z =
    originalFineCoefficientEqualsF19 originalFineWilsonWeight

  originalPhysicalF19F :
    ∀ left →
    originalFineCoefficient (originalWilsonFineF left)
    ≡ originalF19Coefficient (originalWilsonFineF left)
  originalPhysicalF19F left =
    originalFineCoefficientEqualsF19 (originalWilsonFineF left)

  originalPhysicalF19G :
    ∀ right →
    originalFineCoefficient (originalWilsonFineF right)
    ≡ originalF19Coefficient (originalWilsonFineF right)
  originalPhysicalF19G right =
    originalFineCoefficientEqualsF19 (originalWilsonFineF right)

  originalPhysicalF19FG :
    ∀ left right →
    originalFineCoefficient (originalWilsonFineFG left right)
    ≡ originalF19Coefficient (originalWilsonFineFG left right)
  originalPhysicalF19FG left right =
    originalFineCoefficientEqualsF19 (originalWilsonFineFG left right)

  -- Normalize by the ONE original fine Wilson Z, not an independent
  -- bare-coarse action. In particular this transports the original
  -- mixed moment before use by the existing finite Wilson cumulant.
  originalPhysicalF19NormalizedFG :
    (divide : ℝ → ℝ → ℝ) (left right : FineTest) →
    divide
      (originalFineCoefficient (originalWilsonFineFG left right))
      (originalFineCoefficient originalFineWilsonWeight)
    ≡
    divide
      (originalF19Coefficient (originalWilsonFineFG left right))
      (originalF19Coefficient originalFineWilsonWeight)
  originalPhysicalF19NormalizedFG divide left right =
    cong₂ divide
      (originalPhysicalF19FG left right)
      originalPhysicalF19Z
