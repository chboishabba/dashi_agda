module DASHI.Biology.Molecular.BH4OriginalNativeComputedBishopConservationExact where

-- The SAME selected original 27×54 native incidence now pays ALL
-- 29 per-species transport zero witnesses automatically. The
-- 783-coordinate computed rational RHS is unchanged.
--
-- Only the six source-weighted 27-site REACTION neutralities remain
-- explicit; these must come from the authentic 29×12 Rhea source,
-- not from a six-global-zero/physiology authority flag.
--
-- This is source-written Agda proof composition; kernel pending.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q
import Real as R
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Embed
import DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact as Lift
import DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact as Operator
import DASHI.Biology.Molecular.BH4OriginalNative369IncidenceExact as Native
import DASHI.Biology.Molecular.BH4OriginalNativePerSpeciesCancellationExact as Transport
import DASHI.Biology.Molecular.BH4OriginalComputedRationalRHSSplitExact as Split

-- Source-dependent original reaction side input only; the transport
-- law is already the exact native one, not a free incidence matrix.
originalNativeComputedSixAxisRationalConserves :
  (fluxes : Operator.Matrix 54 29)
  (stoichiometry : Operator.Matrix 29 12)
  (rates : Operator.Matrix 27 12)
  (weights : Operator.Matrix 6 29) →
  ((axis : F.Fin 6) →
    Q._≃_
      (Lift.sourceSpatialWeighted
        (V.lookup weights axis)
        (Split.originalReactionRows
          (Native.originalNativeRationalInputs fluxes stoichiometry rates)))
      Q.0ℚᵘ) →
  (axis : F.Fin 6) →
  Q._≃_
    (Lift.sourceSpatialWeighted
      (V.lookup weights axis)
      (Operator.rational369SemidiscreteRHS
        (Native.originalNativeRationalInputs fluxes stoichiometry rates)))
    Q.0ℚᵘ
originalNativeComputedSixAxisRationalConserves
  fluxes stoichiometry rates weights reactionNeutrality =
  Split.originalComputedSixAxisZeroFromLocal
    (Native.originalNativeRationalInputs fluxes stoichiometry rates)
    weights
    (Transport.originalNativeEverySpeciesTransportZero
      fluxes stoichiometry rates)
    reactionNeutrality

originalNativeComputedSixAxisBishopConserves :
  (fluxes : Operator.Matrix 54 29)
  (stoichiometry : Operator.Matrix 29 12)
  (rates : Operator.Matrix 27 12)
  (weights : Operator.Matrix 6 29) →
  ((axis : F.Fin 6) →
    Q._≃_
      (Lift.sourceSpatialWeighted
        (V.lookup weights axis)
        (Split.originalReactionRows
          (Native.originalNativeRationalInputs fluxes stoichiometry rates)))
      Q.0ℚᵘ) →
  (axis : F.Fin 6) →
  R._≃_
    (Lift.bishopSpatialWeighted
      (V.map Embed.embed (V.lookup weights axis))
      (V.map (V.map Embed.embed)
        (Operator.rational369SemidiscreteRHS
          (Native.originalNativeRationalInputs fluxes stoichiometry rates))))
    (Embed.embed Q.0ℚᵘ)
originalNativeComputedSixAxisBishopConserves
  fluxes stoichiometry rates weights reactionNeutrality =
  Split.originalComputedSixAxisBishopFromLocal
    (Native.originalNativeRationalInputs fluxes stoichiometry rates)
    weights
    (Transport.originalNativeEverySpeciesTransportZero
      fluxes stoichiometry rates)
    reactionNeutrality
