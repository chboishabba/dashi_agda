module DASHI.Biology.Molecular.BH4RationalReactionSourceZeroExact where

-- P0: all-six-axes original semidiscrete reaction conservation from
-- 12 *net stoichiometry column* left-kernel certificates, arbitrary
-- exact rational 27-site source rates, and the SAME 29x12 operator.
--
-- Original Rhea-generated positive/negative gross source data must
-- independently construct the 12 signed-net-column kernel receipts.
-- This theorem does not fabricate any 29x12 chemistry or rates.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import NonReflectiveQ as Solver

import DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact as Op
import DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact as Lift
import DASHI.Biology.Molecular.BH4RationalFiniteFubiniExact as Fubini
import DASHI.Biology.Molecular.BH4NativeTransportRationalZeroExact as NativeZero
import DASHI.Biology.Molecular.BH4ComputedRationalSixDefectCompositionExact as Compose
import DASHI.Biology.Molecular.BH4OriginalComputedRationalRHSSplitExact as Split
import DASHI.Biology.Molecular.BH4OriginalNative369IncidenceExact as Native
import Real as BishopReal
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Embed

-- Each source weight scales a *whole finite reaction column*.
reactionTerms :
  ∀ {species reactions}
  (weights : V.Vec Q.ℚᵘ species)
  (matrix : Op.Matrix species reactions)
  (rates : V.Vec Q.ℚᵘ reactions) →
  Op.Matrix species reactions
reactionTerms weights matrix rates =
  V.zipWith
    (λ w row →
      V.map (λ x → Q._*_ w x)
        (V.zipWith Q._*_ row rates))
    weights matrix

-- Finite rational scaling of a sum, no approximation or limit.
scaleFiniteSum :
  ∀ {n} (w : Q.ℚᵘ) (xs : V.Vec Q.ℚᵘ n) →
  Q._≃_
    (Q._*_ w (Fubini.qFiniteSum xs))
    (Fubini.qFiniteSum (V.map (λ x → Q._*_ w x) xs))
scaleFiniteSum w V.[] =
  let open Solver in
  solve 1 (λ w′ → (w′ ⊗ Κ Q.0ℚᵘ) ⊜ Κ Q.0ℚᵘ)
    QP.≃-refl w
scaleFiniteSum w (V._∷_ x xs) =
  QP.≃-trans
    (Fubini.qMulDistributes w x (Fubini.qFiniteSum xs))
    (QP.+-cong QP.≃-refl (scaleFiniteSum w xs))

-- The original weighted reaction RHS is exactly the double sum of
-- source weights times net stoichiometry times the SAME site rates.
weightedReactionAsDoubleSum :
  ∀ {species reactions}
  (weights : V.Vec Q.ℚᵘ species)
  (matrix : Op.Matrix species reactions)
  (rates : V.Vec Q.ℚᵘ reactions) →
  Q._≃_
    (Lift.sourceWeightedRow weights
      (V.map (λ row → Op.rationalDot row rates) matrix))
    (Fubini.qFiniteSum
      (V.map Fubini.qFiniteSum
        (reactionTerms weights matrix rates)))
weightedReactionAsDoubleSum V.[] V.[] rates = QP.≃-refl
weightedReactionAsDoubleSum
  (V._∷_ w weights) (V._∷_ row matrix) rates =
  QP.+-cong
    (scaleFiniteSum w (V.zipWith Q._*_ row rates))
    (weightedReactionAsDoubleSum weights matrix rates)

-- A symbolic reaction-column projection of the weighted term matrix
-- factors into (source left-kernel coefficient) times that same rate.
reactionTermColumnFactors :
  ∀ {species reactions}
  (weights : V.Vec Q.ℚᵘ species)
  (matrix : Op.Matrix species reactions)
  (rates : V.Vec Q.ℚᵘ reactions)
  (column : F.Fin reactions) →
  Q._≃_
    (V.lookup (Fubini.qColumnTotals
      (reactionTerms weights matrix rates)) column)
    (Q._*_
      (Lift.sourceWeightedRow weights
        (Op.rationalColumn matrix column))
      (V.lookup rates column))
reactionTermColumnFactors V.[] V.[] rates column =
  QP.≃-trans
    (NativeZero.lookupReplicateZero column)
    (let open Solver in
     solve 1
       (λ rate → Κ Q.0ℚᵘ ⊜ Κ Q.0ℚᵘ ⊗ rate)
       QP.≃-refl (V.lookup rates column))
reactionTermColumnFactors
  (V._∷_ w weights) (V._∷_ row matrix) rates column =
  QP.≃-trans
    (QP.≃-reflexive
      (NativeZero.lookupZipAdd
        (V.map (λ x → Q._*_ w x)
          (V.zipWith Q._*_ row rates))
        (Fubini.qColumnTotals (reactionTerms weights matrix rates))
        column))
    (QP.≃-trans
      (QP.+-cong
        (QP.≃-reflexive
          (trans
            (NativeZero.lookupMapExact
              (Q._*_ w) (V.zipWith Q._*_ row rates) column)
            (cong (Q._*_ w)
              (Split.lookupZipWith Q._*_ row rates column))))
        (reactionTermColumnFactors weights matrix rates column))
      (let open Solver in
       solve 4
         (λ w′ coefficient rate rest →
           (w′ ⊗ (coefficient ⊗ rate))
               ⊕ (rest ⊗ rate)
           ⊜ ((w′ ⊗ coefficient) ⊕ rest) ⊗ rate)
         QP.≃-refl
         w (V.lookup row column) (V.lookup rates column)
         (Lift.sourceWeightedRow weights
           (Op.rationalColumn matrix column))))

-- Higher-level rational conservation uses source-column annihilation
-- and finite Fubini, not a global zero-defect assumption.
oneSiteRationalReactionZero :
  ∀ {species reactions}
  (weights : V.Vec Q.ℚᵘ species)
  (matrix : Op.Matrix species reactions)
  (rates : V.Vec Q.ℚᵘ reactions) →
  ((column : F.Fin reactions) →
    Q._≃_
      (Lift.sourceWeightedRow weights
        (Op.rationalColumn matrix column))
      Q.0ℚᵘ) →
  Q._≃_
    (Lift.sourceWeightedRow weights
      (V.map (λ row → Op.rationalDot row rates) matrix))
    Q.0ℚᵘ
oneSiteRationalReactionZero {reactions = reactions} weights matrix rates columnZero =
  QP.≃-trans
    (weightedReactionAsDoubleSum weights matrix rates)
    (QP.≃-trans
      (Fubini.qFiniteFubini
        (reactionTerms weights matrix rates))
      (QP.≃-trans
        (Fubini.qFiniteSumCong
          (Fubini.qColumnTotals (reactionTerms weights matrix rates))
          (V.replicate {n = reactions} Q.0ℚᵘ)
          (λ column →
            QP.≃-trans
              (reactionTermColumnFactors weights matrix rates column)
              (QP.≃-trans
                (QP.*-cong (columnZero column) QP.≃-refl)
                (let open Solver in
                 solve 1
                   (λ rate → (Κ Q.0ℚᵘ ⊗ rate) ⊜ Κ Q.0ℚᵘ)
                   QP.≃-refl (V.lookup rates column)))))
        (Fubini.qSumReplicateZero reactions)))


------------------------------------------------------------------------
-- The 27-site source reaction rate field and the actual computed
-- reaction sub-RHS are one and the same index-wise matrix.
------------------------------------------------------------------------

reactionSiteRowMatchesMap :
  (matrix : Op.Matrix 29 12)
  (rates : V.Vec Q.ℚᵘ 12) →
  V.tabulate (λ species →
    Op.rationalDot (V.lookup matrix species) rates)
  ≡ V.map (λ row → Op.rationalDot row rates) matrix
reactionSiteRowMatchesMap matrix rates =
  NativeZero.vecExtensional
    (V.tabulate (λ species →
      Op.rationalDot (V.lookup matrix species) rates))
    (V.map (λ row → Op.rationalDot row rates) matrix)
    λ species →
      trans
        (Op.lookupTabulateExact
          (λ j → Op.rationalDot (V.lookup matrix j) rates)
          species)
        (sym (NativeZero.lookupMapExact
          (λ row → Op.rationalDot row rates)
          matrix species))

reactionAllSitesRowsMatchMap :
  ∀ {sites}
  (matrix : Op.Matrix 29 12)
  (rates : V.Vec (V.Vec Q.ℚᵘ 12) sites) →
  V.tabulate (λ site →
    V.tabulate (λ species →
      Op.rationalDot (V.lookup matrix species)
        (V.lookup rates site)))
  ≡
  V.map
    (λ rateRow → V.map (λ row → Op.rationalDot row rateRow) matrix)
    rates
reactionAllSitesRowsMatchMap matrix rates =
  NativeZero.vecExtensional
    (V.tabulate (λ site →
      V.tabulate (λ species →
        Op.rationalDot (V.lookup matrix species)
          (V.lookup rates site))))
    (V.map
      (λ rateRow → V.map
        (λ row → Op.rationalDot row rateRow) matrix)
      rates)
    λ site →
      trans
        (Op.lookupTabulateExact
          (λ j → V.tabulate (λ species →
            Op.rationalDot (V.lookup matrix species)
              (V.lookup rates j)))
          site)
        (trans
          (reactionSiteRowMatchesMap
            matrix (V.lookup rates site))
          (sym (NativeZero.lookupMapExact
            (λ rateRow →
              V.map (λ row → Op.rationalDot row rateRow) matrix)
            rates site)))

allSitesRationalReactionZero :
  ∀ {sites reactions}
  (weights : V.Vec Q.ℚᵘ 29)
  (matrix : Op.Matrix 29 reactions)
  (rates : V.Vec (V.Vec Q.ℚᵘ reactions) sites) →
  ((column : F.Fin reactions) →
    Q._≃_
      (Lift.sourceWeightedRow weights
        (Op.rationalColumn matrix column))
      Q.0ℚᵘ) →
  Q._≃_
    (Lift.sourceSpatialWeighted weights
      (V.map
        (λ rateRow →
          V.map (λ row → Op.rationalDot row rateRow) matrix)
        rates))
    Q.0ℚᵘ
allSitesRationalReactionZero weights matrix V.[] balanced =
  QP.≃-refl
allSitesRationalReactionZero weights matrix
  (V._∷_ rateRow rest) balanced =
  QP.≃-trans
    (QP.+-cong
      (oneSiteRationalReactionZero weights matrix rateRow balanced)
      (allSitesRationalReactionZero
        weights matrix rest balanced))
    (QP.+-identityˡ Q.0ℚᵘ)

-- The source reaction term of the *actual* 27x29 operator is neutral
-- in each axis solely from the 12 source net-column left kernels.
original369ReactionWeightedZeroFromColumns :
  (fluxes : Op.Matrix 54 29)
  (stoichiometry : Op.Matrix 29 12)
  (rates : Op.Matrix 27 12)
  (weights : V.Vec Q.ℚᵘ 29) →
  ((column : F.Fin 12) →
    Q._≃_
      (Lift.sourceWeightedRow weights
        (Op.rationalColumn stoichiometry column))
      Q.0ℚᵘ) →
  Q._≃_
    (Lift.sourceSpatialWeighted weights
      (Compose.originalReactionRHS
        (Native.originalNativeRationalInputs
          fluxes stoichiometry rates)))
    Q.0ℚᵘ
original369ReactionWeightedZeroFromColumns
  fluxes stoichiometry rates weights columnBalanced =
  QP.≃-trans
    (QP.≃-reflexive
      (cong (Lift.sourceSpatialWeighted weights)
        (reactionAllSitesRowsMatchMap stoichiometry rates)))
    (allSitesRationalReactionZero
      weights stoichiometry rates columnBalanced)

-- All 72 source net-column proofs are sufficient for all six axes
-- of the real-valued Bishop accounting lift on the SAME original
-- native 27x54 incidence + finite 29x12 source operator.
original369SixBishopZeroFromNativeAndNetSource :
  (fluxes : Op.Matrix 54 29)
  (stoichiometry : Op.Matrix 29 12)
  (rates : Op.Matrix 27 12)
  (weights : Op.Matrix 6 29) →
  ((axis : F.Fin 6) (column : F.Fin 12) →
    Q._≃_
      (Lift.sourceWeightedRow
        (V.lookup weights axis)
        (Op.rationalColumn stoichiometry column))
      Q.0ℚᵘ) →
  (axis : F.Fin 6) →
  BishopReal._≃_
    (Lift.bishopSpatialWeighted
      (V.map Embed.embed (V.lookup weights axis))
      (V.map (V.map Embed.embed)
        (Op.rational369SemidiscreteRHS
          (Native.originalNativeRationalInputs
            fluxes stoichiometry rates))))
    (Embed.embed Q.0ℚᵘ)
original369SixBishopZeroFromNativeAndNetSource
  fluxes stoichiometry rates weights columnBalanced =
  NativeZero.originalNativeRHSSixBishopZeroGivenReactionSource
    fluxes stoichiometry rates weights
    (λ axis →
      original369ReactionWeightedZeroFromColumns
        fluxes stoichiometry rates
        (V.lookup weights axis)
        (columnBalanced axis))
