module DASHI.Physics.QuantumVacuum.CasimirEndgameSourceBackedLocalClosureExact where

open import DASHI.Core.Prelude

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Physics.QuantumVacuum.CasimirEndgameSourceTransportBidiExact as Endgame

------------------------------------------------------------------------
-- SOURCE-BACKED LOCAL CLOSURE COMPILERS
--
-- Once an application has paid the exact same-object weld, it must not be
-- asked to re-prove the classical source theorem.  The generic BIDI transport
-- kernel already owns that implication.  This file exposes the three Casimir
-- endgame specializations directly.
------------------------------------------------------------------------

compileMaxwellCompleteness :
  (T : Endgame.MaxwellCompletenessLocalTarget) →
  Endgame.samePlateHilbertCarrierAndBoundaryDomain T →
  Endgame.LocalTETMCompleteness T
compileMaxwellCompleteness T weld =
  Transport.transportSourceBackedTheorem
    Endgame.fourierSourceClaim
    (Endgame.asMaxwellCompletenessTarget T)
    (record { Transport.objectWeld = weld })

compilePolarChangeOfVariables :
  (T : Endgame.PolarMeasureLocalTarget) →
  Endgame.sameEuclideanMapMeasureJacobianAndIntegrand T →
  Endgame.LocalPolarChangeOfVariables T
compilePolarChangeOfVariables T weld =
  Transport.transportSourceBackedTheorem
    Endgame.changeOfVariablesSourceClaim
    (Endgame.asPolarMeasureTarget T)
    (record { Transport.objectWeld = weld })

compileZetaContinuationAtMinusThree :
  (T : Endgame.ZetaContinuationLocalTarget) →
  Endgame.sameZetaFunctionBernoulliNormalisationAndRemainderIntegral T →
  Endgame.LocalContinuationAtMinusThree T
compileZetaContinuationAtMinusThree T weld =
  Transport.transportSourceBackedTheorem
    Endgame.zetaEulerMaclaurinSourceClaim
    (Endgame.asZetaContinuationTarget T)
    (record { Transport.objectWeld = weld })

record ReverseLocalWeldCutset : Set where
  field
    maxwellNeedsOnlySameCarrierBoundaryWeld : Bool
    polarNeedsOnlySameMapMeasureJacobianIntegrandWeld : Bool
    zetaNeedsOnlySameFunctionBernoulliRemainderWeld : Bool

    maxwellNeedsOnlySameCarrierBoundaryWeldIsTrue :
      maxwellNeedsOnlySameCarrierBoundaryWeld ≡ true
    polarNeedsOnlySameMapMeasureJacobianIntegrandWeldIsTrue :
      polarNeedsOnlySameMapMeasureJacobianIntegrandWeld ≡ true
    zetaNeedsOnlySameFunctionBernoulliRemainderWeldIsTrue :
      zetaNeedsOnlySameFunctionBernoulliRemainderWeld ≡ true

open ReverseLocalWeldCutset public

canonicalReverseLocalWeldCutset : ReverseLocalWeldCutset
canonicalReverseLocalWeldCutset = record
  { maxwellNeedsOnlySameCarrierBoundaryWeld = true
  ; polarNeedsOnlySameMapMeasureJacobianIntegrandWeld = true
  ; zetaNeedsOnlySameFunctionBernoulliRemainderWeld = true
  ; maxwellNeedsOnlySameCarrierBoundaryWeldIsTrue = refl
  ; polarNeedsOnlySameMapMeasureJacobianIntegrandWeldIsTrue = refl
  ; zetaNeedsOnlySameFunctionBernoulliRemainderWeldIsTrue = refl
  }
