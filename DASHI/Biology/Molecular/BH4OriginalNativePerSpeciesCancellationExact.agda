module DASHI.Biology.Molecular.BH4OriginalNativePerSpeciesCancellationExact where

-- Pay the first true finite RHS P0 local leaf:
-- Each one of the 29 original species has ZERO transport-only
-- total across all 27 sites, for ANY signed rational current
-- on each of the 54 original oriented native edges.
--
-- Uses the SINGLE existing 27x54 incidence, its 54 zero-column
-- rational witnesses, the canonical 27x29 operator, and the
-- weighted finite-Fubini donor. No six global conservation
-- hypotheses, no fabricated chemical source, no real SG claim.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import NonReflectiveQ as QSolver

import DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact as Lift
import DASHI.Biology.Molecular.BH4RationalFiniteFubiniExact as Fubini
import DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact as Operator
import DASHI.Biology.Molecular.BH4OriginalNative369IncidenceExact as Native
import DASHI.Biology.Molecular.BH4OriginalComputedRationalRHSSplitExact as Split

rationalMulCommutes : (x y : Q.ℚᵘ) →
  Q._≃_ (Q._*_ x y) (Q._*_ y x)
rationalMulCommutes x y =
  let open QSolver in
  solve 2 (λ x′ y′ → (x′ ⊗ y′) ⊜ (y′ ⊗ x′))
    QP.≃-refl x y

rationalDotSwapsArguments :
  ∀ {n} (left right : V.Vec Q.ℚᵘ n) →
  Q._≃_ (Operator.rationalDot left right)
    (Lift.sourceWeightedRow right left)
rationalDotSwapsArguments V.[] V.[] = QP.≃-refl
rationalDotSwapsArguments (V._∷_ x xs) (V._∷_ y ys) =
  QP.+-cong
    (rationalMulCommutes x y)
    (rationalDotSwapsArguments xs ys)

rationalSpatialDotSwapsArguments :
  ∀ {sites species}
  (rows : V.Vec (V.Vec Q.ℚᵘ species) sites)
  (weights : V.Vec Q.ℚᵘ species) →
  Q._≃_
    (Fubini.qFiniteSum
      (V.map (λ row → Operator.rationalDot row weights) rows))
    (Lift.sourceSpatialWeighted weights rows)
rationalSpatialDotSwapsArguments V.[] weights = QP.≃-refl
rationalSpatialDotSwapsArguments (V._∷_ row rows) weights =
  QP.+-cong
    (rationalDotSwapsArguments row weights)
    (rationalSpatialDotSwapsArguments rows weights)

-- Each actual 27×54 native column has exact rational zero.
-- The columnwise-sum observation comes from the generic Fin lemma,
-- not from a "sum over sites cancels" hypothesis.
nativeColumnTotalIsZero :
  (bond : F.Fin 54) →
  Q._≃_
    (V.lookup (Fubini.qColumnTotals Native.sourceNativeIncidence) bond)
    Q.0ℚᵘ
nativeColumnTotalIsZero bond =
  QP.≃-trans
    (Fubini.qColumnTotalsLookup Native.sourceNativeIncidence bond)
    (Native.sourceNativeColumnZero bond)

-- Fubini moves the original 27-site sum past all 54 native bonds;
-- the actual 54 source-incidence columns vanish exactly.
nativeIncidenceAnyFluxWeightedZero :
  (fluxColumn : V.Vec Q.ℚᵘ 54) →
  Q._≃_
    (Fubini.qFiniteSum
      (V.map (λ row → Operator.rationalDot row fluxColumn)
        Native.sourceNativeIncidence))
    Q.0ℚᵘ
nativeIncidenceAnyFluxWeightedZero fluxColumn =
  QP.≃-trans
    (rationalSpatialDotSwapsArguments
      Native.sourceNativeIncidence fluxColumn)
    (QP.≃-trans
      (Fubini.qWeightedFiniteFubini
        fluxColumn Native.sourceNativeIncidence)
      (QP.≃-trans
        (Fubini.qWeightedDotCong fluxColumn
          (Fubini.qColumnTotals Native.sourceNativeIncidence)
          (V.replicate {n = 54} Q.0ℚᵘ)
          nativeColumnTotalIsZero)
        (Fubini.qWeightedZeroRow fluxColumn)))

-- This specializes the transport-only field of the original
-- 783-coordinate RHS to the SAME source-native incidence. No
-- independently supplied "29 species transport zero" certificate.
originalNativeEverySpeciesTransportZero :
  (fluxes : Operator.Matrix 54 29)
  (stoichiometry : Operator.Matrix 29 12)
  (rates : Operator.Matrix 27 12)
  (species : F.Fin 29) →
  Q._≃_
    (V.lookup (Fubini.qColumnTotals
      (Split.originalBondRows
        (Native.originalNativeRationalInputs
          fluxes stoichiometry rates))) species)
    Q.0ℚᵘ
originalNativeEverySpeciesTransportZero fluxes stoichiometry rates species =
  QP.≃-trans
    (Fubini.qColumnTotalsLookup
      (Split.originalBondRows inputs) species)
    (QP.≃-trans
      (Fubini.qFiniteSumCong
        (V.map (λ row → V.lookup row species)
          (Split.originalBondRows inputs))
        (V.map (λ row →
          Operator.rationalDot row
            (Operator.rationalColumn fluxes species))
          Native.sourceNativeIncidence)
        sameSite)
      (nativeIncidenceAnyFluxWeightedZero
        (Operator.rationalColumn fluxes species)))
  where
    inputs : Operator.Rational369SemidiscreteInputs
    inputs = Native.originalNativeRationalInputs
      fluxes stoichiometry rates

    sameSite :
      (site : F.Fin 27) →
      Q._≃_
        (V.lookup
          (V.map (λ row → V.lookup row species)
            (Split.originalBondRows inputs)) site)
        (V.lookup
          (V.map (λ row →
            Operator.rationalDot row
              (Operator.rationalColumn fluxes species))
            Native.sourceNativeIncidence) site)
    sameSite site =
      QP.≃-reflexive
        (trans
          (Fubini.qLookupMap
            (λ row → V.lookup row species)
            (Split.originalBondRows inputs) site)
          (trans
            (Split.originalBondAt inputs site species)
            (sym (Fubini.qLookupMap
              (λ row →
                Operator.rationalDot row
                  (Operator.rationalColumn fluxes species))
              Native.sourceNativeIncidence site))))
