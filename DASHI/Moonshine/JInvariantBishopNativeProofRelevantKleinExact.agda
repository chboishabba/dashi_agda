module DASHI.Moonshine.JInvariantBishopNativeProofRelevantKleinExact where

-- Original unit-disk limits and native reciprocal; no legacy carrier.
-- The remaining strict inequality must concern the literal denominator.
open import Data.Sum.Base using (inj₁)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Inv
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as Apart
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantProofRelevantKleinJExact as K

cube : C.BishopComplex → C.BishopComplex
cube z = A._*C_ (A._*C_ z z) z

normalizedDelta : C.BishopComplex → C.BishopComplex → C.BishopComplex
normalizedDelta e4 e6 =
  A.scaleC (R._⋆ (+ 1 / 1728))
    (A._-C_ (cube e4) (A._*C_ e6 e6))

-- Fix Set₁ disk data in module parameters; Klein.Point remains Set.
module AtDisk {q : C.BishopComplex} {r : R.ℝ}
              (input : Disk.BishopUnitDiskQ q r) where

  completion : Disk.BishopUnitDiskEisensteinCompletion q r input
  completion = Disk.completeBishopUnitDiskEisenstein input

  E4 : C.BishopComplex
  E4 = Disk.e4Limit completion

  E6 : C.BishopComplex
  E6 = Disk.e6Limit completion

  Delta : C.BishopComplex
  Delta = normalizedDelta E4 E6

  Point : Set
  Point = Inv.BishopComplexNonzero Delta

  nativeKlein : K.ProofRelevantKleinJAlgebra
  nativeKlein = K.proof-relevant-klein-j-algebra
    Point C.BishopComplex (λ _ → E4) (λ _ → Delta) cube
    Inv.BishopComplexNonzero (λ nz → nz)
    (λ n d nz → A._*C_ n (Inv.reciprocalC d nz))

  negativeDeltaWitness :
    R._<_ (C.re Delta) R.0ℝ → Point
  negativeDeltaWitness negative =
    Apart.complexNonzeroFromRealApart {z = Delta} (inj₁ negative)

  jFromNegativeDelta :
    R._<_ (C.re Delta) R.0ℝ → C.BishopComplex
  jFromNegativeDelta negative =
    K.KleinJ nativeKlein (negativeDeltaWitness negative)

-- Source-written consumer only. Selected CM strict inequality,
-- quantitative Bishop transport, and pinned kernel acceptance are open.
