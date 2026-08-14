module DASHI.Biology.Physical.CellBrainTransducerBridgeExact where

------------------------------------------------------------------------
-- Brains are specialized cellular networks.  This bridge does not identify a
-- tissue with an ANN; it proves that the existing bioelectric cell-network
-- update has the same stateful-transducer signature already used by the brain
-- lane: input + prior state + modulatory context -> output + successor state.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Cell.BioelectricNetwork as Bioelectric
import DASHI.Biology.StateDependentMultiplexTransducer as Multiplex

record BioelectricModulator (B : Bioelectric.BioelectricNetwork) : Set where
  constructor bioelectricModulator
  field
    environment : Bioelectric.BioelectricNetwork.Environment B
    mechanical : Bioelectric.BioelectricNetwork.MechanicalState B
    regulatory : Bioelectric.BioelectricNetwork.RegulatoryState B

open BioelectricModulator public

bioelectricNetworkAsStatefulTransducer :
  (B : Bioelectric.BioelectricNetwork) → Multiplex.StatefulTransducer
bioelectricNetworkAsStatefulTransducer B = record
  { Input = Bioelectric.BioelectricNetwork.ChemicalSignal B
  ; State = Bioelectric.BioelectricNetwork.NetworkState B
  ; Modulator = BioelectricModulator B
  ; Output = Bioelectric.BioelectricNetwork.NetworkState B
  ; step = λ chemical state modulator →
      let next =
            Bioelectric.BioelectricNetwork.update B
              (environment modulator)
              chemical
              (mechanical modulator)
              (regulatory modulator)
              state
      in next , next
  }

networkOutputEqualsSuccessor :
  (B : Bioelectric.BioelectricNetwork) →
  (chemical : Bioelectric.BioelectricNetwork.ChemicalSignal B) →
  (state : Bioelectric.BioelectricNetwork.NetworkState B) →
  (modulator : BioelectricModulator B) →
  Multiplex.runOutput (bioelectricNetworkAsStatefulTransducer B)
    chemical state modulator
  ≡
  Multiplex.runState (bioelectricNetworkAsStatefulTransducer B)
    chemical state modulator
networkOutputEqualsSuccessor B chemical state modulator = refl

-- The existing finite canonical brain/cell regression therefore sits inside
-- the same operator class without asserting identical mechanisms at all scales.
canonicalBioelectricTransducer : Multiplex.StatefulTransducer
canonicalBioelectricTransducer =
  bioelectricNetworkAsStatefulTransducer Multiplex.canonicalBioelectricNetwork
