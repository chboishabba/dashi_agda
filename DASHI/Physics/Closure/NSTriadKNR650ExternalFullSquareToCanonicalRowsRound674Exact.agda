{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650ExternalFullSquareToCanonicalRowsRound674Exact where

------------------------------------------------------------------------
-- ROUND674 / R606 EXTERNAL FULL SQUARE -> CANONICAL TOTAL EXTERNAL ROWS
--
-- R673 closes the vector-level splice for every swap-invariant R294 weight,
-- including R630's p=0 branch:
--
--   fold_alpha [ W_alpha * externalDoubleForcing_alpha ]
--     =
--   fold_alpha [ totalExternalNestedCommutator_alpha ].
--
-- Fix a spectator beta.  R541 realizes the literal Cauchy resolvent
--
--   K(alpha,beta)
--
-- as exactly such a swap-invariant R294 weight in alpha.  Real-Hermitian
-- linearity therefore turns the R606 external spectator row
--
--   sum_alpha K(alpha,beta)
--     Re<externalDoubleForcing_alpha, doubleCell_beta>
--
-- into the scalar test of the R673 totalized vector fold.  R631 then identifies
-- that totalized scalar with the canonical orbit-resolved external nested row
-- already consumed by R623/R624.
--
-- Summing over beta and using R546 gives the complete R606 external full square
-- as the canonical external row sum on the SAME physical output fibre.
--
-- No estimate, norm, absolute value, or new Clay-facing analytic leaf appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNFullSquareAsSpectatorRowsRound546Exact as R546
import DASHI.Physics.Closure.NSTriadKNR567ForcingFullSelfExternalSplitRound606Exact as R606
import DASHI.Physics.Closure.NSTriadKNSpectatorNestedSelfCanonicalExternalRowRound623Exact as R623
import DASHI.Physics.Closure.NSTriadKNCanonicalExternalTotalCommutatorScalarRound631Exact as R631
import DASHI.Physics.Closure.NSTriadKNR650ExternalZeroBranchEliminationRound673Exact as R673

F : C3.RealField _
F = Rational.rationalRealField

module ExternalRows674
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode))
    (output : Z3.FourierMode) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system

  module Split = R606.FixedOutput physicalSystem S output
  module Spec = R541.Spectator physicalSystem S
  module Row = R545.Row physicalSystem S
  module Rows = R623.SignedRowSplit
    physicalSystem S L H velocityTransverse

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Output.physicalOutputFiber cutoff output

  module ZeroBridge (beta : Physical.PhysicalTriadIncidence) =
    R673.ExternalZeroElimination673
      physicalSystem S L H velocityTransverse
      (Spec.spectatorWeight beta)

  module Canonical (beta : Physical.PhysicalTriadIncidence) =
    R631.CanonicalExternalTotalCommutator631
      E I (Spec.spectatorWeight beta) S L H system velocityTransverse

  pairCellIsWeightedCross :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Split.externalForcingPair alpha beta
    ≡
    R179.realHermitianCross
      (C3.complex3Scale
        (R294.weight (Spec.spectatorWeight beta) alpha)
        (Split.externalDoubleForcing alpha))
      (Row.doubleCell beta)
  pairCellIsWeightedCross alpha beta
      rewrite Spec.spectatorWeightMeaning beta alpha =
    sym
      (R291.scaledRealCrossLeft
        (Row.Swap.pairResolvent alpha beta)
        (Split.externalDoubleForcing alpha)
        (Row.doubleCell beta))

  spectatorRowFactorsThroughWeightedExternalFold :
    (beta : Physical.PhysicalTriadIncidence) →
    R546.spectatorRow Split.externalForcingPair beta fibre
    ≡
    R179.realHermitianCross
      (R224.foldVector
        (λ alpha →
          C3.complex3Scale
            (R294.weight (Spec.spectatorWeight beta) alpha)
            (Split.externalDoubleForcing alpha))
        fibre)
      (Row.doubleCell beta)
  spectatorRowFactorsThroughWeightedExternalFold beta =
    go fibre
    where
    weighted :
      Physical.PhysicalTriadIncidence → C3.Complex3 F
    weighted alpha =
      C3.complex3Scale
        (R294.weight (Spec.spectatorWeight beta) alpha)
        (Split.externalDoubleForcing alpha)

    go :
      (items : List Physical.PhysicalTriadIncidence) →
      R546.spectatorRow Split.externalForcingPair beta items
      ≡
      R179.realHermitianCross
        (R224.foldVector weighted items)
        (Row.doubleCell beta)
    go [] =
      sym (R545.Row.forcingHalfFactors physicalSystem S beta [])
    go (alpha ∷ rest) =
      trans
        (cong₂ _+_
          (pairCellIsWeightedCross alpha beta)
          (go rest))
        (sym
          (R291.realCrossAddLeft
            (weighted alpha)
            (R224.foldVector weighted rest)
            (Row.doubleCell beta)))

  externalSpectatorRowIsCanonicalExternalNestedRow :
    (beta : Physical.PhysicalTriadIncidence) →
    R546.spectatorRow Split.externalForcingPair beta fibre
    ≡ Rows.canonicalExternalNestedForcingRow output beta
  externalSpectatorRowIsCanonicalExternalNestedRow beta =
    let
      module Z = ZeroBridge beta
      module ZA = Z.AtOutput output
      module C = Canonical beta

      test = Row.doubleCell beta
      totalFold =
        R224.foldVector
          Z.Base.Total.totalExternalNestedCommutator
          fibre
    in
    trans
      (spectatorRowFactorsThroughWeightedExternalFold beta)
      (trans
        (cong
          (λ value → R179.realHermitianCross value test)
          ZA.fixedOutputR606ExternalFoldIsR630Total)
        (sym (C.canonicalExternalScalarIsTotalCommutatorScalar output test)))

  canonicalExternalRows :
    List Physical.PhysicalTriadIncidence → ℚ
  canonicalExternalRows [] = 0ℚ
  canonicalExternalRows (beta ∷ rest) =
    Rows.canonicalExternalNestedForcingRow output beta
      + canonicalExternalRows rest

  allExternalSpectatorRowsAreCanonicalRows :
    (betas : List Physical.PhysicalTriadIncidence) →
    R546.allSpectatorRows Split.externalForcingPair fibre betas
    ≡ canonicalExternalRows betas
  allExternalSpectatorRowsAreCanonicalRows [] = refl
  allExternalSpectatorRowsAreCanonicalRows (beta ∷ rest)
    rewrite externalSpectatorRowIsCanonicalExternalNestedRow beta
          | allExternalSpectatorRowsAreCanonicalRows rest = refl

  externalForcingFullIsCanonicalExternalRows :
    Split.externalForcingFull
    ≡ canonicalExternalRows fibre
  externalForcingFullIsCanonicalExternalRows =
    trans
      (R546.fullSquareIsAllSpectatorRows
        Split.externalForcingPair fibre)
      (allExternalSpectatorRowsAreCanonicalRows fibre)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round674R606ExternalSpectatorRowToR631Closed : Bool
round674R606ExternalSpectatorRowToR631Closed = true

round674R606ExternalFullSquareToCanonicalRowsClosed : Bool
round674R606ExternalFullSquareToCanonicalRowsClosed = true

round674R630ZeroBranchPreservedAndEliminatedByR673 : Bool
round674R630ZeroBranchPreservedAndEliminatedByR673 = true

round674IntroducesEstimate : Bool
round674IntroducesEstimate = false

round674ExternalSignedPaymentClosed : Bool
round674ExternalSignedPaymentClosed = false

round674IntroducesNewClayLeaf : Bool
round674IntroducesNewClayLeaf = false

round674ClayPromotion : Bool
round674ClayPromotion = false

round674R606ExternalSpectatorRowToR631ClosedIsTrue :
  round674R606ExternalSpectatorRowToR631Closed ≡ true
round674R606ExternalSpectatorRowToR631ClosedIsTrue = refl

round674R606ExternalFullSquareToCanonicalRowsClosedIsTrue :
  round674R606ExternalFullSquareToCanonicalRowsClosed ≡ true
round674R606ExternalFullSquareToCanonicalRowsClosedIsTrue = refl

round674R630ZeroBranchPreservedAndEliminatedByR673IsTrue :
  round674R630ZeroBranchPreservedAndEliminatedByR673 ≡ true
round674R630ZeroBranchPreservedAndEliminatedByR673IsTrue = refl

round674IntroducesEstimateIsFalse :
  round674IntroducesEstimate ≡ false
round674IntroducesEstimateIsFalse = refl

round674ExternalSignedPaymentClosedIsFalse :
  round674ExternalSignedPaymentClosed ≡ false
round674ExternalSignedPaymentClosedIsFalse = refl

round674IntroducesNewClayLeafIsFalse :
  round674IntroducesNewClayLeaf ≡ false
round674IntroducesNewClayLeafIsFalse = refl

round674ClayPromotionIsFalse :
  round674ClayPromotion ≡ false
round674ClayPromotionIsFalse = refl
