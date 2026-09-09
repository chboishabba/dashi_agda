module DASHI.Physics.Closure.NSTriadKNFactoredFullTransposeSymmetryRound566Exact where

------------------------------------------------------------------------
-- ROUND566 / FULL-SQUARE AMPLITUDE HALF IS THE TRANSPOSE OF THE FORCING HALF
--
-- R545 leaves two signed terms in every spectator row:
--
--   K(alpha,beta) Re<G_alpha,D_beta>
--   K(alpha,beta) Re<D_alpha,G_beta>.
--
-- On the COMPLETE ordered square, the second term is exactly the transpose of
-- the first because
--
--   K(alpha,beta) = K(beta,alpha)
--
-- and the real Hermitian cross is symmetric.  Transposition is a finite square
-- permutation, so the two full-square sums are equal.  Hence they are not two
-- independent analytic leaves.
--
-- This owner proves the generic finite transpose theorem first, then instantiates
-- it on the literal R538/R545 physical pair scalar.  No norm, positivity,
-- integration, cutoff estimate or PDE estimate appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- 1. Generic finite transpose invariance of a complete ordered square.
------------------------------------------------------------------------

rowOfTransposeIsColumn :
  ∀ {A : Set}
    (P Q : A → A → ℚ) →
    ((x y : A) → P x y ≡ Q y x) →
    (x : A) (rest : List A) →
  R539.rowSum P x rest ≡ R539.columnSum Q rest x
rowOfTransposeIsColumn P Q transposeP x [] = refl
rowOfTransposeIsColumn P Q transposeP x (y ∷ rest) =
  cong₂ _+_
    (transposeP x y)
    (rowOfTransposeIsColumn P Q transposeP x rest)

columnOfTransposeIsRow :
  ∀ {A : Set}
    (P Q : A → A → ℚ) →
    ((x y : A) → P x y ≡ Q y x) →
    (x : A) (rest : List A) →
  R539.columnSum P rest x ≡ R539.rowSum Q x rest
columnOfTransposeIsRow P Q transposeP x [] = refl
columnOfTransposeIsRow P Q transposeP x (y ∷ rest) =
  cong₂ _+_
    (transposeP y x)
    (columnOfTransposeIsRow P Q transposeP x rest)

fullSquareTransposeInvariant :
  ∀ {A : Set}
    (P Q : A → A → ℚ) →
    ((x y : A) → P x y ≡ Q y x) →
    (items : List A) →
  R543.fullSquareSum P items ≡ R543.fullSquareSum Q items
fullSquareTransposeInvariant P Q transposeP [] = refl
fullSquareTransposeInvariant P Q transposeP (x ∷ rest)
  rewrite transposeP x x
        | rowOfTransposeIsColumn P Q transposeP x rest
        | columnOfTransposeIsRow P Q transposeP x rest
        | fullSquareTransposeInvariant P Q transposeP rest =
  solve
    ( Q x x
      ∷ R539.rowSum Q x rest
      ∷ R539.columnSum Q rest x
      ∷ R543.fullSquareSum Q rest
      ∷ [])

------------------------------------------------------------------------
-- 2. Literal physical forcing/amplitude pair halves.
------------------------------------------------------------------------

module PhysicalTranspose
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Row = R545.Row physicalSystem S
  module Swap = R538.PairSwap physicalSystem S

  forcingPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  forcingPair alpha beta =
    R179.realHermitianCross
      (Row.Weighted.Force.weightedDouble beta alpha)
      (Row.doubleCell beta)

  amplitudePair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  amplitudePair alpha beta =
    R179.realHermitianCross
      (Row.Weighted.Amp.weightedDoubleCell beta alpha)
      (Row.D.doubleForcing beta)

  forcingPairScalarized :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    forcingPair alpha beta
    ≡ Swap.pairResolvent alpha beta
      * R179.realHermitianCross
          (Row.D.doubleForcing alpha) (Row.doubleCell beta)
  forcingPairScalarized alpha beta
    rewrite Row.Spec.spectatorWeightMeaning beta alpha =
    R291.scaledRealCrossLeft
      (Swap.pairResolvent alpha beta)
      (Row.D.doubleForcing alpha) (Row.doubleCell beta)

  amplitudePairScalarized :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    amplitudePair alpha beta
    ≡ Swap.pairResolvent alpha beta
      * R179.realHermitianCross
          (Row.doubleCell alpha) (Row.D.doubleForcing beta)
  amplitudePairScalarized alpha beta
    rewrite Row.Spec.spectatorWeightMeaning beta alpha =
    R291.scaledRealCrossLeft
      (Swap.pairResolvent alpha beta)
      (Row.doubleCell alpha) (Row.D.doubleForcing beta)

  amplitudePairIsTransposeForcing :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    amplitudePair alpha beta ≡ forcingPair beta alpha
  amplitudePairIsTransposeForcing alpha beta =
    let
      swapScalar :
        Swap.pairResolvent alpha beta
          * R179.realHermitianCross
              (Row.doubleCell alpha) (Row.D.doubleForcing beta)
        ≡
        Swap.pairResolvent beta alpha
          * R179.realHermitianCross
              (Row.D.doubleForcing beta) (Row.doubleCell alpha)
      swapScalar =
        cong₂ _*_
          (Swap.pairResolventSymmetric alpha beta)
          (R287.realHermitianCrossSymmetric
            (Row.doubleCell alpha) (Row.D.doubleForcing beta))
    in
    trans
      (amplitudePairScalarized alpha beta)
      (trans swapScalar (sym (forcingPairScalarized beta alpha)))

  amplitudeFullEqualsForcingFull :
    (items : List Physical.PhysicalTriadIncidence) →
    R543.fullSquareSum amplitudePair items
    ≡ R543.fullSquareSum forcingPair items
  amplitudeFullEqualsForcingFull =
    fullSquareTransposeInvariant
      amplitudePair forcingPair amplitudePairIsTransposeForcing

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round566GenericFullSquareTransposeInvariantClosed : Bool
round566GenericFullSquareTransposeInvariantClosed = true

round566LiteralAmplitudeHalfIsTransposeForcingHalf : Bool
round566LiteralAmplitudeHalfIsTransposeForcingHalf = true

round566FullAmplitudeAndForcingHalvesEqual : Bool
round566FullAmplitudeAndForcingHalvesEqual = true

round566TwoIndependentFactoredSpacetimeHalvesRemain : Bool
round566TwoIndependentFactoredSpacetimeHalvesRemain = false

round566IntroducesAnyAnalyticEstimate : Bool
round566IntroducesAnyAnalyticEstimate = false

round566FactoredForcingSpacetimeBoundClosed : Bool
round566FactoredForcingSpacetimeBoundClosed = false

round566CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round566CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round566ClayPromotion : Bool
round566ClayPromotion = false

round566FullAmplitudeAndForcingHalvesEqualIsTrue :
  round566FullAmplitudeAndForcingHalvesEqual ≡ true
round566FullAmplitudeAndForcingHalvesEqualIsTrue = refl

round566TwoIndependentFactoredSpacetimeHalvesRemainIsFalse :
  round566TwoIndependentFactoredSpacetimeHalvesRemain ≡ false
round566TwoIndependentFactoredSpacetimeHalvesRemainIsFalse = refl

round566ClayPromotionIsFalse : round566ClayPromotion ≡ false
round566ClayPromotionIsFalse = refl
