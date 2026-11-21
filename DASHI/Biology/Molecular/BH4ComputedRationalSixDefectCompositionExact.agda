module DASHI.Biology.Molecular.BH4ComputedRationalSixDefectCompositionExact where

-- P0: exact SOURCE-MATCHED recombination into the ACTUAL computed RHS.
-- This owner *derives* all six global zero defects from two narrower
-- obligations: original transport cancels per species; original source
-- reaction term has all six weighted left-kernel coordinates zero.
-- It never assumes the six global computed-RHS zero defects directly.
--
-- The 27/54/29/12 arrays and spatial weighted sum are the existing BH4
-- mathematical chart. Source authentication, signed native incidence,
-- and Rhea-generated 12-column proofs are upstream remaining owners.
-- No kinetics, SG constitutive identity or tissue measurement is added.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import Real as BishopReal
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Embed

import DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact as Operator
import DASHI.Biology.Molecular.BH4RationalSemidiscreteBilinearityExact as Linear
import DASHI.Biology.Molecular.BH4RationalFiniteFubiniExact as Fubini
import DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact as Lift

originalTransportRHS :
  Operator.Rational369SemidiscreteInputs → Operator.Matrix 27 29
originalTransportRHS inputs =
  V.tabulate (λ site →
    V.tabulate (λ species →
      Operator.bondContribution inputs site species))

originalReactionRHS :
  Operator.Rational369SemidiscreteInputs → Operator.Matrix 27 29
originalReactionRHS inputs =
  V.tabulate (λ site →
    V.tabulate (λ species →
      Operator.reactionContribution inputs site species))

-- Only the actual underlying ORIGINAL source/geometry owners may
-- inhabit these two receipts. They do not follow from dimensions.
record OriginalSourceLocalConservation
  (inputs : Operator.Rational369SemidiscreteInputs)
  (weights : Operator.Matrix 6 29) : Set where
  field
    originalNativeTransportPerSpeciesZero :
      (species : F.Fin 29) →
      Q._≃_
        (V.lookup (Fubini.qColumnTotals (originalTransportRHS inputs))
          species)
        Q.0ℚᵘ

    originalSourceReactionPerAxisZero :
      (axis : F.Fin 6) →
      Q._≃_
        (Lift.sourceSpatialWeighted
          (V.lookup weights axis)
          (originalReactionRHS inputs))
        Q.0ℚᵘ

open OriginalSourceLocalConservation public

-- All six zero defects are now a THEOREM about the SAME computed
-- 783-coordinate RHS, not six unrelated input assumptions.
originalComputedRHSSixZeroDefects :
  (inputs : Operator.Rational369SemidiscreteInputs)
  (weights : Operator.Matrix 6 29) →
  OriginalSourceLocalConservation inputs weights →
  (axis : F.Fin 6) →
  Q._≃_
    (Lift.sourceSpatialWeighted
      (V.lookup weights axis)
      (Operator.rational369SemidiscreteRHS inputs))
    Q.0ℚᵘ
originalComputedRHSSixZeroDefects inputs weights local axis =
  QP.≃-trans
    (Linear.original369ComputedRHSWeightedSplit
      inputs (V.lookup weights axis))
    (QP.≃-trans
      (QP.+-cong
        (Fubini.qWeightedColumnZeroImpliesSpatialZero
          (V.lookup weights axis)
          (originalTransportRHS inputs)
          (originalNativeTransportPerSpeciesZero local))
        (originalSourceReactionPerAxisZero local axis))
      (QP.+-identityˡ Q.0ℚᵘ))

-- One direct result with six source-matched axes, genuine computed
-- RHS and original Bishop real setoid. No global zero assumptions.
originalComputedRHSSixBishopConservation :
  (inputs : Operator.Rational369SemidiscreteInputs)
  (weights : Operator.Matrix 6 29) →
  OriginalSourceLocalConservation inputs weights →
  (axis : F.Fin 6) →
  BishopReal._≃_
    (Lift.bishopSpatialWeighted
      (V.map Embed.embed (V.lookup weights axis))
      (V.map (V.map Embed.embed)
        (Operator.rational369SemidiscreteRHS inputs)))
    (Embed.embed Q.0ℚᵘ)
originalComputedRHSSixBishopConservation inputs weights local =
  Operator.computedRationalRHSConservationLiftsToBishop
    inputs weights (originalComputedRHSSixZeroDefects inputs weights local)
