module DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact where

------------------------------------------------------------------------
-- ROUND567 / FACTORED FULL = ONE TRANSPOSE-REDUCED COMMUTATOR HALF
--
-- R545 writes the complete pair scalar pointwise as
--
--   pairScalar(alpha,beta)
--     = 2 * (forcingPair(alpha,beta) + amplitudePair(alpha,beta)).
--
-- R566 proves on the complete ordered square
--
--   Full(amplitudePair) = Full(forcingPair).
--
-- Therefore
--
--   Full(pairScalar) = 4 * Full(forcingPair).
--
-- R547 already identifies Full(pairScalar) with the literal factoredFull.
-- Thus the apparent commutator/amplitude two-term spacetime debt collapses to
-- one signed forcing/commutator square with an exact factor four.  No norm,
-- positivity, integration or PDE estimate enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNLiteralR406CommutatorDiagonalNormalFormRound547Exact as R547
import DASHI.Physics.Closure.NSTriadKNFactoredFullTransposeSymmetryRound566Exact as R566
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

four567 : ℚ
four567 = (1ℚ + 1ℚ) * (1ℚ + 1ℚ)

------------------------------------------------------------------------
-- 1. Generic full-square linearity for 2 * (P + Q).
------------------------------------------------------------------------

scaledSumPair :
  ∀ {A : Set} → (A → A → ℚ) → (A → A → ℚ) → A → A → ℚ
scaledSumPair P Q x y = R291.two * (P x y + Q x y)

fullSquareScaledSum :
  ∀ {A : Set}
    (P Q : A → A → ℚ) →
    (items : List A) →
  R543.fullSquareSum (scaledSumPair P Q) items
  ≡ R291.two *
      (R543.fullSquareSum P items + R543.fullSquareSum Q items)
fullSquareScaledSum P Q [] = refl
fullSquareScaledSum P Q (x ∷ rest)
  rewrite fullSquareScaledSum P Q rest =
  solve
    ( P x x
      ∷ Q x x
      ∷ DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact.rowSum P x rest
      ∷ DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact.rowSum Q x rest
      ∷ DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact.columnSum P rest x
      ∷ DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact.columnSum Q rest x
      ∷ R543.fullSquareSum P rest
      ∷ R543.fullSquareSum Q rest
      ∷ [])

------------------------------------------------------------------------
-- 2. Literal physical instantiation.
------------------------------------------------------------------------

module CommutatorOnly
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Row = R545.Row physicalSystem S
  module NF = R547.NormalForm physicalSystem S
  module T = R566.PhysicalTranspose physicalSystem S

  pairScalarIsScaledForcingPlusAmplitude :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Row.pairScalar alpha beta
    ≡ scaledSumPair T.forcingPair T.amplitudePair alpha beta
  pairScalarIsScaledForcingPlusAmplitude alpha beta =
    Row.pairScalarPointwise alpha beta

  fullPairScalarIsScaledHalves :
    (items : List Physical.PhysicalTriadIncidence) →
    R543.fullSquareSum Row.pairScalar items
    ≡ R291.two *
        (R543.fullSquareSum T.forcingPair items
          + R543.fullSquareSum T.amplitudePair items)
  fullPairScalarIsScaledHalves items =
    trans
      (fullSquarePointwise items)
      (fullSquareScaledSum T.forcingPair T.amplitudePair items)
    where
    fullSquarePointwise :
      (xs : List Physical.PhysicalTriadIncidence) →
      R543.fullSquareSum Row.pairScalar xs
      ≡ R543.fullSquareSum
          (scaledSumPair T.forcingPair T.amplitudePair) xs
    fullSquarePointwise [] = refl
    fullSquarePointwise (x ∷ rest)
      rewrite pairScalarIsScaledForcingPlusAmplitude x x
            | rowPointwise x rest
            | columnPointwise rest x
            | fullSquarePointwise rest = refl
      where
      rowPointwise :
        (a : Physical.PhysicalTriadIncidence) →
        (ys : List Physical.PhysicalTriadIncidence) →
        DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact.rowSum
          Row.pairScalar a ys
        ≡ DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact.rowSum
          (scaledSumPair T.forcingPair T.amplitudePair) a ys
      rowPointwise a [] = refl
      rowPointwise a (y ∷ ys) =
        cong₂ _+_
          (pairScalarIsScaledForcingPlusAmplitude a y)
          (rowPointwise a ys)

      columnPointwise :
        (ys : List Physical.PhysicalTriadIncidence) →
        (b : Physical.PhysicalTriadIncidence) →
        DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact.columnSum
          Row.pairScalar ys b
        ≡ DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact.columnSum
          (scaledSumPair T.forcingPair T.amplitudePair) ys b
      columnPointwise [] b = refl
      columnPointwise (y ∷ ys) b =
        cong₂ _+_
          (pairScalarIsScaledForcingPlusAmplitude y b)
          (columnPointwise ys b)

  fullPairScalarIsFourForcing :
    (items : List Physical.PhysicalTriadIncidence) →
    R543.fullSquareSum Row.pairScalar items
    ≡ four567 * R543.fullSquareSum T.forcingPair items
  fullPairScalarIsFourForcing items =
    trans
      (fullPairScalarIsScaledHalves items)
      (trans
        (cong
          (R291.two *_)
          (cong₂ _+_ refl (T.amplitudeFullEqualsForcingFull items)))
        (solve (R543.fullSquareSum T.forcingPair items ∷ [])))

  factoredFullIsFourForcingFull :
    (output : Z3.FourierMode) →
    let items = Output.physicalOutputFiber
      (DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.cutoff
        (Field30.finiteSystem physicalSystem)) output
    in
    NF.factoredFull output items
    ≡ four567 * R543.fullSquareSum T.forcingPair items
  factoredFullIsFourForcingFull output =
    let
      items = Output.physicalOutputFiber
        (DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.cutoff
          (Field30.finiteSystem physicalSystem)) output
    in
    trans
      (sym (NF.fullSquareIsFactoredFull output))
      (fullPairScalarIsFourForcing items)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round567FactoredFullTwoHalvesCollapsed : Bool
round567FactoredFullTwoHalvesCollapsed = true

round567FactoredFullIsFourForcingSquare : Bool
round567FactoredFullIsFourForcingSquare = true

round567IndependentAmplitudeSpacetimeEstimateRequired : Bool
round567IndependentAmplitudeSpacetimeEstimateRequired = false

round567IntroducesAnyAnalyticEstimate : Bool
round567IntroducesAnyAnalyticEstimate = false

round567ForcingCommutatorSpacetimeBoundClosed : Bool
round567ForcingCommutatorSpacetimeBoundClosed = false

round567CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round567CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round567ClayPromotion : Bool
round567ClayPromotion = false

round567FactoredFullIsFourForcingSquareIsTrue :
  round567FactoredFullIsFourForcingSquare ≡ true
round567FactoredFullIsFourForcingSquareIsTrue = refl

round567IndependentAmplitudeSpacetimeEstimateRequiredIsFalse :
  round567IndependentAmplitudeSpacetimeEstimateRequired ≡ false
round567IndependentAmplitudeSpacetimeEstimateRequiredIsFalse = refl

round567ClayPromotionIsFalse : round567ClayPromotion ≡ false
round567ClayPromotionIsFalse = refl
