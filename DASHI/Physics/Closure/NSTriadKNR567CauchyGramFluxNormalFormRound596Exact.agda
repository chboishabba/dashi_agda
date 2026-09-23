{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR567CauchyGramFluxNormalFormRound596Exact where

------------------------------------------------------------------------
-- ROUND596 / R567 CAUCHY-RESOLVED GRAM + FLUX-TANGENT NORMAL FORM
--
-- On a nonzero physical fixed-output fibre, R290 gives pointwise
--
--   w_ab * nonlinearRemainder_ab
--     = gram_ab + w_ab * gramTangent_ab,
--
-- because
--
--   w_ab * gramTangent_ab
--     = - gram_ab + w_ab * nonlinearRemainder_ab.
--
-- R538's symmetric pair scalar is exactly the left-hand side.  R547 identifies
-- its complete full square with factoredFull, and R567 proves
--
--   factoredFull = 4 * forcingFull.
--
-- Therefore, on the SAME literal fibre,
--
--   4 * forcingFull
--     = fullSquare(gram) + fullSquare(weightedGramFluxTangent).
--
-- This is finite exact algebra.  No sign estimate, absolute value, norm,
-- spacetime bound, Schur estimate, or Clay promotion is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNLiteralR406CommutatorDiagonalNormalFormRound547Exact as R547
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedFullSquareRateCancellationExact as R595
import DASHI.Physics.Closure.NSTriadKNFullGramCoherentFoldRound597Exact as R597

F : C3.RealField _
F = Rational.rationalRealField

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module Swap = R538.PairSwap physicalSystem S
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive
  module NF = R547.NormalForm physicalSystem S
  module C = R567.CommutatorOnly physicalSystem S

  cutoff : Nat
  cutoff = Audit.cutoff (Field30.finiteSystem physicalSystem)

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Output.physicalOutputFiber cutoff output

  doubleCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  doubleCell =
    R225.doubleMixedCell S Pair.D.Pair.velocity

  gramPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  gramPair alpha beta =
    R291.gram (Swap.Q alpha beta)

  gramPairIsCoherentWorkPair :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    gramPair alpha beta ≡ R597.workPair doubleCell alpha beta
  gramPairIsCoherentWorkPair alpha beta = refl

  weightedFluxTangentPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  weightedFluxTangentPair alpha beta =
    Swap.pairResolvent alpha beta
      * R291.gramTangent (Swap.Q alpha beta)

  pairPositive :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    Positive (R291.pairRate (Swap.Q alpha beta))
  pairPositive alpha beta alphaOutput betaOutput =
    Rate.pairRatePositiveFromCellRates
      alpha beta
      (Rate.cellRatePositiveFromNonzeroOutput
        output outputNonzero alpha alphaOutput)
      (Rate.cellRatePositiveFromNonzeroOutput
        output outputNonzero beta betaOutput)

  weightedRemainderAsGramPlusFlux :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (positive : Positive (R291.pairRate (Swap.Q alpha beta))) →
    Swap.symmetricWeightedRemainder alpha beta
    ≡ gramPair alpha beta + weightedFluxTangentPair alpha beta
  weightedRemainderAsGramPlusFlux alpha beta positive =
    let
      P = Pair.pairRatePositiveBuildsR290 alpha beta positive

      remainderForm :
        R290.weightedNonlinearRemainder P
        ≡ R290.gram P + R290.weightedGramFluxTangent P
      remainderForm
        rewrite R290.weightedFluxDerivativeIdentity P =
        solve
          (R290.gram P
            ∷ R290.weightedNonlinearRemainder P
            ∷ [])
    in
    trans
      (sym
        (Swap.literalR290WeightedRemainderIsSymmetricScalar
          alpha beta positive))
      remainderForm

  pairScalarNormalForm :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    Swap.symmetricWeightedRemainder alpha beta
    ≡ gramPair alpha beta + weightedFluxTangentPair alpha beta
  pairScalarNormalForm alpha beta alphaOutput betaOutput =
    weightedRemainderAsGramPlusFlux
      alpha beta
      (pairPositive alpha beta alphaOutput betaOutput)

  rowNormalForm :
    (alpha : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    (items : List Physical.PhysicalTriadIncidence) →
    ((beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn items → Physical.k beta ≡ output) →
    R539.rowSum Swap.symmetricWeightedRemainder alpha items
    ≡
    R539.rowSum gramPair alpha items
      + R539.rowSum weightedFluxTangentPair alpha items
  rowNormalForm alpha alphaOutput [] allOutput = refl
  rowNormalForm alpha alphaOutput (beta ∷ rest) allOutput =
    trans
      (cong₂ _+_
        (pairScalarNormalForm
          alpha beta alphaOutput (allOutput beta R396.here))
        (rowNormalForm
          alpha alphaOutput rest
          (λ gamma member → allOutput gamma (R396.there member))))
      (solve
        ( gramPair alpha beta
        ∷ weightedFluxTangentPair alpha beta
        ∷ R539.rowSum gramPair alpha rest
        ∷ R539.rowSum weightedFluxTangentPair alpha rest
        ∷ []))

  columnNormalForm :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    (beta : Physical.PhysicalTriadIncidence) →
    Physical.k beta ≡ output →
    R539.columnSum Swap.symmetricWeightedRemainder items beta
    ≡
    R539.columnSum gramPair items beta
      + R539.columnSum weightedFluxTangentPair items beta
  columnNormalForm [] allOutput beta betaOutput = refl
  columnNormalForm (alpha ∷ rest) allOutput beta betaOutput =
    trans
      (cong₂ _+_
        (pairScalarNormalForm
          alpha beta (allOutput alpha R396.here) betaOutput)
        (columnNormalForm
          rest
          (λ gamma member → allOutput gamma (R396.there member))
          beta betaOutput))
      (solve
        ( gramPair alpha beta
        ∷ weightedFluxTangentPair alpha beta
        ∷ R539.columnSum gramPair rest beta
        ∷ R539.columnSum weightedFluxTangentPair rest beta
        ∷ []))

  fullSquareNormalForm :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    R543.fullSquareSum Swap.symmetricWeightedRemainder items
    ≡
    R543.fullSquareSum gramPair items
      + R543.fullSquareSum weightedFluxTangentPair items
  fullSquareNormalForm [] allOutput = refl
  fullSquareNormalForm (alpha ∷ rest) allOutput
    rewrite
      pairScalarNormalForm
        alpha alpha
        (allOutput alpha R396.here)
        (allOutput alpha R396.here)
        | rowNormalForm
            alpha
            (allOutput alpha R396.here)
            rest
            (λ beta member → allOutput beta (R396.there member))
        | columnNormalForm
            rest
            (λ beta member → allOutput beta (R396.there member))
            alpha
            (allOutput alpha R396.here)
        | fullSquareNormalForm
            rest
            (λ beta member → allOutput beta (R396.there member)) =
    solve
      ( gramPair alpha alpha
      ∷ weightedFluxTangentPair alpha alpha
      ∷ R539.rowSum gramPair alpha rest
      ∷ R539.rowSum weightedFluxTangentPair alpha rest
      ∷ R539.columnSum gramPair rest alpha
      ∷ R539.columnSum weightedFluxTangentPair rest alpha
      ∷ R543.fullSquareSum gramPair rest
      ∷ R543.fullSquareSum weightedFluxTangentPair rest
      ∷ [])

  literalFullSquareNormalForm :
    R543.fullSquareSum Swap.symmetricWeightedRemainder fibre
    ≡
    R543.fullSquareSum gramPair fibre
      + R543.fullSquareSum weightedFluxTangentPair fibre
  literalFullSquareNormalForm =
    fullSquareNormalForm
      fibre
      (Rate.allElementsHaveOutput cutoff output)

  fourForcingFullIsGramPlusFlux :
    R567.four567
      * R543.fullSquareSum C.T.forcingPair fibre
    ≡
    R543.fullSquareSum gramPair fibre
      + R543.fullSquareSum weightedFluxTangentPair fibre
  fourForcingFullIsGramPlusFlux =
    trans
      (sym (C.factoredFullIsFourForcingFull output))
      (trans
        (sym (NF.fullSquareIsFactoredFull output))
        literalFullSquareNormalForm)

  fullGramIsCoherentSelfWork :
    R543.fullSquareSum gramPair fibre
    ≡ Work.coherentWork
        (R224.foldVector doubleCell fibre)
        (R224.foldVector doubleCell fibre)
  fullGramIsCoherentSelfWork =
    trans
      (R595.fullSquareCongruent
        gramPair
        (R597.workPair doubleCell)
        gramPairIsCoherentWorkPair
        fibre)
      (R597.fullGramIsCoherentFold doubleCell fibre)

  fourForcingFullIsCoherentSelfWorkPlusFlux :
    R567.four567
      * R543.fullSquareSum C.T.forcingPair fibre
    ≡
    Work.coherentWork
      (R224.foldVector doubleCell fibre)
      (R224.foldVector doubleCell fibre)
    + R543.fullSquareSum weightedFluxTangentPair fibre
  fourForcingFullIsCoherentSelfWorkPlusFlux =
    trans
      fourForcingFullIsGramPlusFlux
      (cong
        (_+ R543.fullSquareSum weightedFluxTangentPair fibre)
        fullGramIsCoherentSelfWork)

  fourForcingFullMinusSelfWorkIsFlux :
    R567.four567
      * R543.fullSquareSum C.T.forcingPair fibre
      - Work.coherentWork
          (R224.foldVector doubleCell fibre)
          (R224.foldVector doubleCell fibre)
    ≡ R543.fullSquareSum weightedFluxTangentPair fibre
  fourForcingFullMinusSelfWorkIsFlux
    rewrite fourForcingFullIsCoherentSelfWorkPlusFlux =
    solve
      ( Work.coherentWork
          (R224.foldVector doubleCell fibre)
          (R224.foldVector doubleCell fibre)
      ∷ R543.fullSquareSum weightedFluxTangentPair fibre
      ∷ [])

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round596LiteralR567CauchyGramFluxNormalFormClosed : Bool
round596LiteralR567CauchyGramFluxNormalFormClosed = true

round596UsesOnlyExistingR290R400R547R567Identities : Bool
round596UsesOnlyExistingR290R400R547R567Identities = true

round596FullGramAlignedWithA3CoherentSelfWork : Bool
round596FullGramAlignedWithA3CoherentSelfWork = true

round596OnlyResidualAfterSelfWorkPeelIsWeightedFluxTangent : Bool
round596OnlyResidualAfterSelfWorkPeelIsWeightedFluxTangent = true

round596IntroducesNewNSEstimate : Bool
round596IntroducesNewNSEstimate = false

round596ClosesR568SpacetimeBudget : Bool
round596ClosesR568SpacetimeBudget = false

round596IdentifiesA3CenteredKernelWithCauchyKernel : Bool
round596IdentifiesA3CenteredKernelWithCauchyKernel = false

round596LiteralR567CauchyGramFluxNormalFormClosedIsTrue :
  round596LiteralR567CauchyGramFluxNormalFormClosed ≡ true
round596LiteralR567CauchyGramFluxNormalFormClosedIsTrue = refl

round596FullGramAlignedWithA3CoherentSelfWorkIsTrue :
  round596FullGramAlignedWithA3CoherentSelfWork ≡ true
round596FullGramAlignedWithA3CoherentSelfWorkIsTrue = refl

round596OnlyResidualAfterSelfWorkPeelIsWeightedFluxTangentIsTrue :
  round596OnlyResidualAfterSelfWorkPeelIsWeightedFluxTangent ≡ true
round596OnlyResidualAfterSelfWorkPeelIsWeightedFluxTangentIsTrue = refl

round596IntroducesNewNSEstimateIsFalse :
  round596IntroducesNewNSEstimate ≡ false
round596IntroducesNewNSEstimateIsFalse = refl

round596ClosesR568SpacetimeBudgetIsFalse :
  round596ClosesR568SpacetimeBudget ≡ false
round596ClosesR568SpacetimeBudgetIsFalse = refl

round596IdentifiesA3CenteredKernelWithCauchyKernelIsFalse :
  round596IdentifiesA3CenteredKernelWithCauchyKernel ≡ false
round596IdentifiesA3CenteredKernelWithCauchyKernelIsFalse = refl
