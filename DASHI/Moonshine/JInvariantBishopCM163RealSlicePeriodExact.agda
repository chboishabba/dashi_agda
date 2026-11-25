module DASHI.Moonshine.JInvariantBishopCM163RealSlicePeriodExact where

-- SOURCE-WRITTEN, UNCOMPILED. Bind the actual proof-relevant Klein
-- quotient, not an arbitrary j variable, to the native period consumer.
-- The CM root at the actual selected q remains an analytic producer.
open import Data.Integer.Base using (+_)
import Data.Integer.Base as Z
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
open import Data.Product.Base using (proj₁)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantBishopNativeProofRelevantKleinExact as K
import DASHI.Moonshine.JInvariantBishopEisensteinRealSliceExact as Slice
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as Norm
import DASHI.Foundations.BishopChudnovskyNativeEulerLimitsExact as Euler
import DASHI.Foundations.BishopChudnovskyNativePeriodProductExact as End
import DASHI.Foundations.BishopMachinArctanConstructionExact as M

-- Real projection is multiplicative on the actual real slice.
mulRe : ∀ {u v : C.BishopComplex} → Slice.RealSlice v →
  C.re (A._*C_ u v) ≃ (C.re u * C.re v)
mulRe {C.complex a b} {C.complex c d} hd =
  P.≃-trans (P.+-cong P.≃-refl (P.-‿cong (P.*-congˡ hd)))
    (let open P.ℝ-Solver in
      solve 3 (λ a b c → (a ⊗ c) ⊖ (b ⊗ Κ Q.0ℚᵘ) ⊜ a ⊗ c)
        P.≃-refl a b c)

negCQ : Q.ℚᵘ
negCQ = (Z.-_ (+ 262537412640768000)) / 1

negC : ℝ
negC = negCQ ⋆

module AtDisk {q : C.BishopComplex} {r : ℝ}
  (input : Disk.BishopUnitDiskQ q r) (realQ : Slice.RealSlice q) where

  module RealSlice = Slice.AtDisk input realQ
  module Actual = K.AtDisk input

  X Y d : ℝ
  X = C.re Actual.E4
  Y = C.re Actual.E6
  d = C.re Actual.Delta

  cubeRe : C.re (K.cube Actual.E4) ≃ Norm.cube X
  cubeRe = P.≃-trans (mulRe {u = A._*C_ Actual.E4 Actual.E4} RealSlice.e4Real)
    (P.*-congʳ (mulRe {u = Actual.E4} RealSlice.e4Real))

  squareRe : C.re (A._*C_ Actual.E6 Actual.E6) ≃ Norm.sq Y
  squareRe = mulRe {u = Actual.E6} RealSlice.e6Real

  deltaRe : d ≃ (((+ 1 / 1728) ⋆) * (Norm.cube X - Norm.sq Y))
  deltaRe = P.*-congˡ (P.+-cong cubeRe (P.-‿cong squareRe))

  module AtNegativeDelta (negative : R._<_ d R.0ℝ) where

    nz = Actual.negativeDeltaWitness negative

    inv : C.BishopComplex
    inv = Rec.reciprocalC Actual.Delta nz

    invReal : Slice.RealSlice inv
    invReal = Slice.reciprocalReal nz RealSlice.deltaReal

    j : ℝ
    j = C.re (Actual.jFromNegativeDelta negative)

    reciprocalRe : (d * C.re inv) ≃ R.1ℝ
    reciprocalRe = P.≃-trans
      (P.≃-symm (mulRe {u = Actual.Delta} invReal))
      (proj₁ (Rec.multiplyReciprocal Actual.Delta nz))

    jRe : j ≃ (Norm.cube X * C.re inv)
    jRe = P.≃-trans (mulRe {u = K.cube Actual.E4} invReal)
      (P.*-congʳ cubeRe)

    -- Exact clearing of the original guarded quotient.
    jCross : (j * d) ≃ Norm.cube X
    jCross = P.≃-trans (P.*-congʳ jRe)
      (P.≃-trans
        (let open P.ℝ-Solver in
          solve 3 (λ u v d → (u ⊗ v) ⊗ d ⊜ u ⊗ (d ⊗ v))
            P.≃-refl (Norm.cube X) (C.re inv) d)
        (P.≃-trans (P.*-congˡ reciprocalRe) (P.*-identityʳ (Norm.cube X))))

    -- Forward CM root -> period cubic. Rational coefficients only.
    rootToCubic : j ≃ negC → Norm.sq Y ≃ (Norm.t * Norm.cube X)
    rootToCubic hj =
      let
        u = Norm.cube X
        v = Norm.sq Y
        lhs = negC * (((+ 1 / 1728) ⋆) * (u - v))
        eq : lhs ≃ u
        eq = P.≃-trans (P.≃-symm (P.*-cong hj deltaRe)) jCross
        open P.ℝ-Solver
      in P.≃-trans
        (solve 2 (λ u v → v ⊜ u ⊕ Κ (+ 1728 / 262537412640768000) ⊗
          (Κ negCQ ⊗ (Κ (+ 1 / 1728) ⊗ (u ⊖ v)))) P.≃-refl u v)
        (P.≃-trans (P.+-cong P.≃-refl (P.*-congˡ eq))
          (solve 1 (λ u → u ⊕ Κ (+ 1728 / 262537412640768000) ⊗ u
            ⊜ Κ (+ 262537412640769728 / 262537412640768000) ⊗ u) P.≃-refl u))

    -- Reverse on the SAME quotient and same apartness witness.
    cubicToRoot : Norm.sq Y ≃ (Norm.t * Norm.cube X) → j ≃ negC
    cubicToRoot hy =
      let
        u = Norm.cube X
        v = C.re inv
        eq : (negC * d) ≃ u
        eq = P.≃-trans (P.*-congˡ deltaRe)
          (P.≃-trans
            (P.*-congˡ (P.*-congˡ (P.+-cong P.≃-refl (P.-‿cong hy))))
            (let open P.ℝ-Solver in
              solve 1 (λ u → Κ negCQ ⊗ (Κ (+ 1 / 1728) ⊗
                (u ⊖ (Κ (+ 262537412640769728 / 262537412640768000) ⊗ u))) ⊜ u)
                P.≃-refl u))
      in P.≃-trans jRe
        (P.≃-trans (P.*-congʳ (P.≃-symm eq))
          (P.≃-trans (P.*-assoc negC d v)
            (P.≃-trans (P.*-congˡ reciprocalRe) (P.*-identityʳ negC))))

    -- Actual normalized E4/E6 and actual constructed Euler limits.
    -- No arbitrary cubic equality or weighted-series convergence premise.
    periodFromRootAndSignedJet : (e : ℝ) → R.Positive X →
      j ≃ negC →
      Norm.sq Euler.H ≃ X →
      (Norm.six * Y * Euler.J₁) ≃ (Euler.H * (e * X - Y)) →
      ((M.bishopMachinPi * Norm.r) * (Norm.B * X * e - Norm.D * Y)) ≃
        (Norm.six * Norm.B * X) →
      End.NativePeriod
    periodFromRootAndSignedJet e px hj hf he hc =
      Euler.periodFromActualEulerLimits X Y e px hf (rootToCubic hj) he hc
