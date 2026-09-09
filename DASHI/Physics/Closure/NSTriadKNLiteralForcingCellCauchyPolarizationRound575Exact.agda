module DASHI.Physics.Closure.NSTriadKNLiteralForcingCellCauchyPolarizationRound575Exact where

------------------------------------------------------------------------
-- ROUND575 / LITERAL R567 FORCING SQUARE -> R446 CAUCHY POLARIZATION
--
-- Instantiate R574 on one physical nonzero output fibre with
--
--   G_tau = literal R388 doubleForcing tau,
--   D_tau = literal R225 doubleMixedCell tau,
--   rate_tau = physical viscous cell rate.
--
-- The mixed Cauchy form is definitionally the forcing half used by R566/R567:
--
--   K(alpha,beta) Re<G_alpha,D_beta>.
--
-- Hence the exact R446 difference PSD gives
--
--   2 forcingFull_k <= forcingQuadratic_k + cellQuadratic_k.
--
-- This is an alternative producer reduction only.  It is useful precisely if
-- both positive quadratics can be paid cutoff-uniformly without importing the
-- still-open critical barrier.  That adequacy is audited next; no promotion is
-- made here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNDoubleMixedPhysicalDampedTangentRound388Exact as R388
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNFactoredFullTransposeSymmetryRound566Exact as R566
import DASHI.Physics.Closure.NSTriadKNCauchyPolarizationUpperRound573Exact as R573
import DASHI.Physics.Closure.NSTriadKNCauchyVectorPolarizationRound574Exact as R574
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalPolarization
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module D = R388.PhysicalDoubleMixed physicalSystem S
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive
  module T = R566.PhysicalTranspose physicalSystem S

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Output.physicalOutputFiber cutoff output

  doubleCell : Physical.PhysicalTriadIncidence → C3.Complex3 F
  doubleCell tau = R225.doubleMixedCell S D.Pair.velocity tau

  buildCells575 :
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    List R574.CauchyVectorPairCell574
  buildCells575 [] allOutput = []
  buildCells575 (tau ∷ rest) allOutput =
    R574.cauchy-vector-pair-cell-574
      (D.Pair.cellRate tau)
      (D.doubleForcing tau)
      (doubleCell tau)
      (Rate.cellRatePositiveFromNonzeroOutput
        output outputNonzero tau (allOutput tau R396.here))
    ∷ buildCells575 rest
        (λ selected member → allOutput selected (R396.there member))

  cells575 : List R574.CauchyVectorPairCell574
  cells575 = buildCells575 fibre (Rate.allElementsHaveOutput cutoff output)

  forcingQuadratic575 : ℚ
  forcingQuadratic575 = R543.fullSquareSum R574.leftPair574 cells575

  cellQuadratic575 : ℚ
  cellQuadratic575 = R543.fullSquareSum R574.rightPair574 cells575

  mixedQuadratic575 : ℚ
  mixedQuadratic575 = R543.fullSquareSum R574.mixedPair574 cells575

  pairMixedExact575 :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R574.mixedPair574
      (R574.cauchy-vector-pair-cell-574
        (D.Pair.cellRate alpha) (D.doubleForcing alpha) (doubleCell alpha)
        (Rate.cellRatePositiveFromNonzeroOutput
          output outputNonzero alpha (Rate.allElementsHaveOutput cutoff output alpha R396.here)))
      (R574.cauchy-vector-pair-cell-574
        (D.Pair.cellRate beta) (D.doubleForcing beta) (doubleCell beta)
        (Rate.cellRatePositiveFromNonzeroOutput
          output outputNonzero beta (Rate.allElementsHaveOutput cutoff output beta R396.here)))
    ≡ T.forcingPair alpha beta
  pairMixedExact575 alpha beta = T.forcingPairScalarized alpha beta

  -- Proof objects for positivity do not occur in the scalar pair.  The
  -- structural recursion below therefore compares the actual built list
  -- directly with the literal physical incidence square.
  mixedRowExact575 :
    (head : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    (allOutput :
      (tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn (head ∷ rest) → Physical.k tau ≡ output) →
    R539.rowSum R574.mixedPair574
      (R574.cauchy-vector-pair-cell-574
        (D.Pair.cellRate head) (D.doubleForcing head) (doubleCell head)
        (Rate.cellRatePositiveFromNonzeroOutput
          output outputNonzero head (allOutput head R396.here)))
      (buildCells575 rest
        (λ selected member → allOutput selected (R396.there member)))
    ≡ R539.rowSum T.forcingPair head rest
  mixedRowExact575 head [] allOutput = refl
  mixedRowExact575 head (beta ∷ rest) allOutput =
    cong₂ _+_ refl
      (mixedRowExact575 head rest
        (λ selected member →
          allOutput selected
            (case member of λ where
              R396.here → R396.there R396.here
              (R396.there deeper) → R396.there (R396.there deeper))))

  mixedFullExact575 :
    (items : List Physical.PhysicalTriadIncidence) →
    (allOutput :
      (tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    R543.fullSquareSum R574.mixedPair574 (buildCells575 items allOutput)
    ≡ R543.fullSquareSum T.forcingPair items
  mixedFullExact575 [] allOutput = refl
  mixedFullExact575 (head ∷ rest) allOutput =
    -- Both full-square recursions see the same pair scalar by definition of
    -- R443.cauchyEntry and R538.pairResolvent.  The remaining tails recurse.
    cong₂ _+_
      (cong₂ _+_ refl
        (cong₂ _+_ refl refl))
      (mixedFullExact575 rest
        (λ selected member → allOutput selected (R396.there member)))

  physicalForcingPolarizationUpper575 :
    R573.two573 * R543.fullSquareSum T.forcingPair fibre
    ≤ forcingQuadratic575 + cellQuadratic575
  physicalForcingPolarizationUpper575 =
    let source = R574.mixedCauchyPolarizationUpper574 cells575 in
    Relation.Binary.PropositionalEquality.subst
      (λ mixed → R573.two573 * mixed ≤ forcingQuadratic575 + cellQuadratic575)
      (mixedFullExact575 fibre (Rate.allElementsHaveOutput cutoff output))
      source

round575LiteralForcingHalfAttachedToR446Polarization : Bool
round575LiteralForcingHalfAttachedToR446Polarization = true

round575ForcingFullUpperByTwoPositiveQuadratics : Bool
round575ForcingFullUpperByTwoPositiveQuadratics = true

round575ForcingQuadraticCutoffUniformSpacetimePaid : Bool
round575ForcingQuadraticCutoffUniformSpacetimePaid = false

round575CellQuadraticCutoffUniformSpacetimePaid : Bool
round575CellQuadraticCutoffUniformSpacetimePaid = false

round575PolarizationDeclaredShortestRoute : Bool
round575PolarizationDeclaredShortestRoute = false

round575CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round575CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round575ClayPromotion : Bool
round575ClayPromotion = false

round575ClayPromotionIsFalse : round575ClayPromotion ≡ false
round575ClayPromotionIsFalse = refl
