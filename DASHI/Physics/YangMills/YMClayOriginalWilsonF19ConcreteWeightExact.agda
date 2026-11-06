module DASHI.Physics.YangMills.YMClayOriginalWilsonF19ConcreteWeightExact where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayNative1024WeightedWilsonReindexExact as Original
import DASHI.Physics.YangMills.YMClaySUNOriginal64Pair896MarkedEffectiveSourceExact as F19

twice : Nat → Nat
twice zero = zero
twice (suc n) = suc (suc (twice n))

flattenPairs : ∀ {A : Set} {n} →
  Vec.Vec (Torus.Product A A) n → Vec.Vec A (twice n)
flattenPairs Vec.[] = Vec.[]
flattenPairs (pair Vec.∷ rest) =
  Torus.first pair Vec.∷ Torus.second pair Vec.∷ flattenPairs rest

appendVec : ∀ {A : Set} {n m} →
  Vec.Vec A n → Vec.Vec A m → Vec.Vec A (n + m)
appendVec Vec.[] right = right
appendVec (head Vec.∷ tail) right = head Vec.∷ appendVec tail right

originalPairsAndSpectators :
  ∀ {A : Set} →
  Vec.Vec (Torus.Product A A) 64 →
  Vec.Vec A 896 → Vec.Vec A (Codec.originalPositiveBondCount 4)
originalPairsAndSpectators pairs spectators =
  subst (λ n → Vec.Vec _ n)
    (sym Codec.originalSideFourCountIs1024)
    (appendVec (flattenPairs pairs) spectators)

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
  physicalWeight : F19.OriginalFineWeight theory source bilateral linear
  physicalWeight pairs spectators =
    Original.physicallySortedWilsonWeight theory traceData exponential beta
      (originalPairsAndSpectators pairs spectators)

  actualF19WilsonTwoMarkTheorem :
    (left right : F19.OriginalCoarseTest theory source bilateral linear)
    (s t : ℝ) →
    F19.actualOriginalFineTwoMarkedNumerator
      theory source bilateral linear physicalWeight left right s t
    ≡ F19.actualEffectiveTwoMarkedNumerator
      theory source bilateral linear physicalWeight left right s t
  actualF19WilsonTwoMarkTheorem left right s t =
    F19.originalFullTwoMarkedFibreEqualsActualEffectiveDensity
      theory source bilateral linear physicalWeight left right s t
