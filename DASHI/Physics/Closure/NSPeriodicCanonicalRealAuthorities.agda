module DASHI.Physics.Closure.NSPeriodicCanonicalRealAuthorities where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Integer.Base using (ℤ)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; 1ℝ
  ; _+ℝ_
  ; _*ℝ_
  ; _≤ℝ_
  ; _<ℝ_
  )
open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier using
  (vec3)
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSPeriodicModeInverseNormScaling as Scaling
import DASHI.Physics.Closure.NSPeriodicRealOrderedNormLaws as Ordered
import DASHI.Physics.Closure.NSPeriodicConcreteModeOperatorPythagorean as Concrete
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Foundational ordered-real authority additions.
--
-- RealAnalysisAxioms is already the repository's explicit external-analysis
-- boundary.  These postulates add only standard ordered-field and canonical
-- integer-embedding laws.  They contain no Fourier estimate, cutoff constant,
-- Navier--Stokes inequality, or PDE assumption.
------------------------------------------------------------------------

postulate
  integerToReal : ℤ → ℝ
  natToReal : Nat → ℝ

  natSquareSumEmbedding : ∀ x y z →
    natToReal
      (ModeNorm.natSquare (Cube.integerMagnitude x)
       + (ModeNorm.natSquare (Cube.integerMagnitude y)
       + ModeNorm.natSquare (Cube.integerMagnitude z)))
    ≡
    Ordered.realVecNormSquared
      (vec3 (integerToReal x) (integerToReal y) (integerToReal z))

  positiveNatEmbedding : ∀ {n} →
    ModeNorm.PositiveNat n → 0ℝ <ℝ natToReal n

  reciprocalReal : ℝ → ℝ
  positiveImpliesNonnegativeReal : ∀ {x} →
    0ℝ <ℝ x → 0ℝ ≤ℝ x
  reciprocalPositiveReal : ∀ {x} →
    0ℝ <ℝ x → 0ℝ <ℝ reciprocalReal x
  reciprocalCancelPositiveReal : ∀ {x} →
    0ℝ <ℝ x → reciprocalReal x *ℝ x ≡ 1ℝ

  squareNonnegativeReal : ∀ x →
    0ℝ ≤ℝ (x *ℝ x)

  addOrderCancelRightReal : ∀ {a b c : ℝ} →
    (a +ℝ c) ≤ℝ (b +ℝ c) → a ≤ℝ b

canonicalIntegerRealNormEmbedding :
  ModeNorm.ConcreteIntegerRealNormEmbedding
canonicalIntegerRealNormEmbedding = record
  { embedInteger = integerToReal
  ; embedNat = natToReal
  ; embeddedModeNormMeaning = natSquareSumEmbedding
  ; positiveNatEmbedsPositive = positiveNatEmbedding
  }

canonicalOrderedRealInverseAuthority :
  Scaling.OrderedRealInverseAuthority
canonicalOrderedRealInverseAuthority = record
  { reciprocal = reciprocalReal
  ; positiveImpliesNonnegative = positiveImpliesNonnegativeReal
  ; reciprocalPositive = reciprocalPositiveReal
  ; reciprocalCancelPositive = reciprocalCancelPositiveReal
  }

canonicalOrderedRealSquareAuthority :
  Ordered.OrderedRealSquareAuthority
canonicalOrderedRealSquareAuthority = record
  { squareNonnegative = squareNonnegativeReal }

canonicalRealOrderCancellationAuthority :
  Concrete.RealOrderCancellationAuthority
canonicalRealOrderCancellationAuthority = record
  { addOrderCancelRight = addOrderCancelRightReal }

canonicalPeriodicModeNormAuthority :
  ModeNorm.ConcretePeriodicModeNormAuthority
canonicalPeriodicModeNormAuthority = record
  { realEmbedding = canonicalIntegerRealNormEmbedding
  ; squareAuthority = canonicalOrderedRealSquareAuthority
  ; inverseAuthority = canonicalOrderedRealInverseAuthority
  }

------------------------------------------------------------------------
-- Status: all four formerly free foundational records now have one canonical
-- inhabitant over the repository's chosen real carrier.  The assumptions are
-- isolated at the pre-existing external real-analysis boundary.
------------------------------------------------------------------------

canonicalRealAuthoritiesLevel : ProofLevel
canonicalRealAuthoritiesLevel = machineChecked
