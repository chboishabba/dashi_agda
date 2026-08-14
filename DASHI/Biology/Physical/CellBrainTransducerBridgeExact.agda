module DASHI.Biology.Physical.CellBrainTransducerBridgeExact where

------------------------------------------------------------------------
-- SOURCE-FACING MOTIVATION
--
-- David Beniaguev, Idan Segev, Michael London,
-- "Single cortical neurons as deep artificial neural networks",
-- Neuron 109 (2021). DOI: 10.1016/j.neuron.2021.07.002.
--
-- Michael London and Michael Hausser,
-- "Dendritic computation", Annual Review of Neuroscience 28 (2005),
-- 503-532. DOI: 10.1146/annurev.neuro.28.061604.135703.
--
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
