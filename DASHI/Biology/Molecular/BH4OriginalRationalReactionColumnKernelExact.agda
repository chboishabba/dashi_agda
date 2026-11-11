module DASHI.Biology.Molecular.BH4OriginalRationalReactionColumnKernelExact where

-- Algebraic 29×12 reaction operator left-kernel -> arbitrary-rate
-- weighted source zero. Uses the SAME rationalDot as the original
-- 783-coordinate RHS, and the SAME weightedRow as the Bishop lift.
-- In particular, no six pre-existing reaction-zero receipts assumed.
-- Source-generated 72 literal column proofs are required instead.
--
-- No Agda kernel acceptance or measured kinetics claimed.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import NonReflectiveQ as QSolver

import DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact as Operator
import DASHI.Biology.Molecular.BH4RationalFiniteFubiniExact as Fubini
import DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact as Lift
import DASHI.Biology.Molecular.BH4OriginalComputedRationalRHSSplitExact as Split
import DASHI.Biology.Molecular.BH4OriginalNative369IncidenceExact as Native

-- Dot is linear in the first (stoichiometric) argument.
rationalDotAdd :
  ∀ {n} (left right rates : V.Vec Q.ℚᵘ n) →
  Q._≃_
    (Operator.rationalDot (V.zipWith Q._+_ left right) rates)
    (Q._+_
      (Operator.rationalDot left rates)
      (Operator.rationalDot right rates))
rationalDotAdd V.[] V.[] V.[] =
  QP.≃-sym (QP.+-identityˡ Q.0ℚᵘ)
rationalDotAdd
  (V._∷_ a left) (V._∷_ b right) (V._∷_ rate rates) =
  QP.≃-trans
    (QP.+-cong
      (mulRightDistributes a b rate)
      (rationalDotAdd left right rates))
    (Fubini.qShuffle
      (Q._*_ a rate) (Q._*_ b rate)
      (Operator.rationalDot left rates)
      (Operator.rationalDot right rates))
  where
    mulRightDistributes : (a b rate : Q.ℚᵘ) →
      Q._≃_ (Q._*_ (Q._+_ a b) rate)
        (Q._+_ (Q._*_ a rate) (Q._*_ b rate))
    mulRightDistributes a b rate =
      let open QSolver in
      solve 3
        (λ x y z →
          ((x ⊕ y) ⊗ z)
          ⊜ ((x ⊗ z) ⊕ (y ⊗ z)))
        QP.≃-refl a b rate

rationalMulAssociates : (w x rate : Q.ℚᵘ) →
  Q._≃_ (Q._*_ (Q._*_ w x) rate)
    (Q._*_ w (Q._*_ x rate))
rationalMulAssociates w x rate =
  let open QSolver in
  solve 3
    (λ w′ x′ r′ →
      ((w′ ⊗ x′) ⊗ r′) ⊜ (w′ ⊗ (x′ ⊗ r′)))
    QP.≃-refl w x rate

rationalDotScale :
  ∀ {n} (weight : Q.ℚᵘ)
  (row rates : V.Vec Q.ℚᵘ n) →
  Q._≃_
    (Operator.rationalDot
      (V.map (Q._*_ weight) row) rates)
    (Q._*_ weight (Operator.rationalDot row rates))
rationalDotScale weight V.[] V.[] =
  QP.≃-sym (Fubini.qMulZero weight)
rationalDotScale weight
  (V._∷_ a row) (V._∷_ rate rates) =
  QP.≃-trans
    (QP.+-cong
      (rationalMulAssociates weight a rate)
      (rationalDotScale weight row rates))
    (QP.≃-sym
      (Fubini.qMulDistributes
        weight (Q._*_ a rate) (Operator.rationalDot row rates)))

-- The genuine 29-component stoichiometry is folded over species
-- into a 12-component weighted source-column vector, not represented
-- by an independent hand-authored 12-vector.
weightedStoichiometryColumns :
  ∀ {species columns}
  (weights : V.Vec Q.ℚᵘ species)
  (stoichiometry : Operator.Matrix species columns) →
  V.Vec Q.ℚᵘ columns
weightedStoichiometryColumns {columns = columns} V.[] V.[] =
  V.replicate {n = columns} Q.0ℚᵘ
weightedStoichiometryColumns
  (V._∷_ weight weights) (V._∷_ row rows) =
  V.zipWith Q._+_
    (V.map (Q._*_ weight) row)
    (weightedStoichiometryColumns weights rows)

rationalDotZeroRow :
  ∀ {n}
  (rates : V.Vec Q.ℚᵘ n) →
  Q._≃_
    (Operator.rationalDot
      (V.replicate {n = n} Q.0ℚᵘ) rates)
    Q.0ℚᵘ
rationalDotZeroRow V.[] = QP.≃-refl
rationalDotZeroRow (V._∷_ rate rates) =
  QP.≃-trans
    (QP.+-cong
      (QP.≃-trans
        (mulZeroOnLeft rate)
        QP.≃-refl)
      (rationalDotZeroRow rates))
    (QP.+-identityˡ Q.0ℚᵘ)
  where
    mulZeroOnLeft : (rate : Q.ℚᵘ) →
      Q._≃_ (Q._*_ Q.0ℚᵘ rate) Q.0ℚᵘ
    mulZeroOnLeft rate =
      let open QSolver in
      solve 1 (λ r → ((Κ Q.0ℚᵘ) ⊗ r) ⊜ Κ Q.0ℚᵘ)
        QP.≃-refl rate

rationalDotFirstCong :
  ∀ {n}
  (left right rates : V.Vec Q.ℚᵘ n) →
  ((column : F.Fin n) →
    Q._≃_ (V.lookup left column) (V.lookup right column)) →
  Q._≃_
    (Operator.rationalDot left rates)
    (Operator.rationalDot right rates)
rationalDotFirstCong V.[] V.[] V.[] same = QP.≃-refl
rationalDotFirstCong (V._∷_ x xs)
  (V._∷_ y ys) (V._∷_ rate rates) same =
  QP.+-cong
    (QP.*-cong (same F.zero) QP.≃-refl)
    (rationalDotFirstCong xs ys rates
      (λ column → same (F.suc column)))

-- The structural finite Fubini result directly for the *selected*
-- 29 species × 12 reaction dot-product operation.
weightedStoichiometryRateFubini :
  ∀ {species columns}
  (weights : V.Vec Q.ℚᵘ species)
  (stoichiometry : Operator.Matrix species columns)
  (rates : V.Vec Q.ℚᵘ columns) →
  Q._≃_
    (Lift.sourceWeightedRow weights
      (V.map (λ row → Operator.rationalDot row rates) stoichiometry))
    (Operator.rationalDot
      (weightedStoichiometryColumns weights stoichiometry) rates)
weightedStoichiometryRateFubini V.[] V.[] rates =
  QP.≃-sym (rationalDotZeroRow rates)
weightedStoichiometryRateFubini
  (V._∷_ weight weights) (V._∷_ row rows) rates =
  QP.≃-trans
    (QP.+-cong
      (QP.≃-sym (rationalDotScale weight row rates))
      (weightedStoichiometryRateFubini weights rows rates))
    (QP.≃-sym
      (rationalDotAdd
        (V.map (Q._*_ weight) row)
        (weightedStoichiometryColumns weights rows)
        rates))

-- Once each actual source stoichiometry column has weighted
-- total zero, *every* supplied rational reaction-rate vector
-- has zero weighted reaction production, with no rate hypothesis.
weightedStoichiometryColumnsZeroRates :
  ∀ {species columns}
  (weights : V.Vec Q.ℚᵘ species)
  (stoichiometry : Operator.Matrix species columns)
  (rates : V.Vec Q.ℚᵘ columns) →
  ((column : F.Fin columns) →
    Q._≃_
      (V.lookup
        (weightedStoichiometryColumns weights stoichiometry)
        column)
      Q.0ℚᵘ) →
  Q._≃_
    (Lift.sourceWeightedRow weights
      (V.map (λ row → Operator.rationalDot row rates) stoichiometry))
    Q.0ℚᵘ
weightedStoichiometryColumnsZeroRates
  {columns = columns} weights stoichiometry rates columnZero =
  QP.≃-trans
    (weightedStoichiometryRateFubini weights stoichiometry rates)
    (QP.≃-trans
      (rationalDotFirstCong
        (weightedStoichiometryColumns weights stoichiometry)
        (V.replicate {n = columns} Q.0ℚᵘ)
        rates columnZero)
      (rationalDotZeroRow rates))

-- A finite sum of source-neutral 29-species rows is source-neutral.
qSpatialWeightedAllRowsZero :
  ∀ {sites species}
  (weights : V.Vec Q.ℚᵘ species)
  (rows : V.Vec (V.Vec Q.ℚᵘ species) sites) →
  ((site : F.Fin sites) →
    Q._≃_ (Lift.sourceWeightedRow weights
      (V.lookup rows site)) Q.0ℚᵘ) →
  Q._≃_ (Lift.sourceSpatialWeighted weights rows) Q.0ℚᵘ
qSpatialWeightedAllRowsZero weights V.[] zero = QP.≃-refl
qSpatialWeightedAllRowsZero weights (V._∷_ row rows) zero =
  QP.≃-trans
    (QP.+-cong
      (zero F.zero)
      (qSpatialWeightedAllRowsZero weights rows
        (λ site → zero (F.suc site))))
    (QP.+-identityˡ Q.0ℚᵘ)

-- Specialization to the SAME native 27×54 incidence,
-- existing computed 27×29 reaction RHS, and 29×12 S:
-- the generated source need only provide its 12 column zeros.
originalReactionAllSitesZeroFromSourceColumns :
  (fluxes : Operator.Matrix 54 29)
  (stoichiometry : Operator.Matrix 29 12)
  (rates : Operator.Matrix 27 12)
  (weights : V.Vec Q.ℚᵘ 29) →
  ((column : F.Fin 12) →
    Q._≃_
      (V.lookup (weightedStoichiometryColumns
        weights stoichiometry) column) Q.0ℚᵘ) →
  Q._≃_
    (Lift.sourceSpatialWeighted weights
      (Split.originalReactionRows
        (Native.originalNativeRationalInputs fluxes stoichiometry rates)))
    Q.0ℚᵘ
originalReactionAllSitesZeroFromSourceColumns
  fluxes stoichiometry rates weights sourceColumnZero =
  qSpatialWeightedAllRowsZero weights
    (Split.originalReactionRows inputs)
    local
  where
    inputs : Operator.Rational369SemidiscreteInputs
    inputs = Native.originalNativeRationalInputs
      fluxes stoichiometry rates

    local : (site : F.Fin 27) →
      Q._≃_
        (Lift.sourceWeightedRow weights
          (V.lookup (Split.originalReactionRows inputs) site))
        Q.0ℚᵘ
    local site =
      QP.≃-trans
        (Fubini.qWeightedDotCong weights
          (V.lookup (Split.originalReactionRows inputs) site)
          (V.map (λ row →
            Operator.rationalDot row (V.lookup rates site))
            stoichiometry)
          sameSpecies)
        (weightedStoichiometryColumnsZeroRates
          weights stoichiometry (V.lookup rates site)
          sourceColumnZero)
      where
        sameSpecies : (species : F.Fin 29) →
          Q._≃_
            (V.lookup
              (V.lookup (Split.originalReactionRows inputs) site)
              species)
            (V.lookup
              (V.map (λ row →
                Operator.rationalDot row (V.lookup rates site))
                stoichiometry)
              species)
        sameSpecies species =
          QP.≃-reflexive
            (trans
              (Split.originalReactionAt inputs site species)
              (sym (Fubini.qLookupMap
                (λ row → Operator.rationalDot row (V.lookup rates site))
                stoichiometry species)))
