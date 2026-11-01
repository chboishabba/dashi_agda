module DASHI.Biology.Levin.NeuralFieldControlCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.NeuralFieldBiologyChemistryAdapter as Adapter

record NeuralFieldControlCore : Set where
  field
    adapter : Adapter.NeuralFieldBiologyChemistryAdapter
    mixedSelectivitySupported : Bool
    travelingFieldControlCandidate : Bool
    anesthesiaFragmentationCandidate : Bool
    analogComputationCandidate : Bool
    synapticStorageFieldExpressionSeparation : Bool
    consciousnessPromotionBlocked : Bool
    autismClinicalPromotionBlocked : Bool
    universalWaveTheoryBlocked : Bool
    interpretation : String

canonicalNeuralFieldControlCore : NeuralFieldControlCore
canonicalNeuralFieldControlCore = record
  { adapter = Adapter.canonicalNeuralFieldBiologyChemistryAdapter
  ; mixedSelectivitySupported = true
  ; travelingFieldControlCandidate = true
  ; anesthesiaFragmentationCandidate = true
  ; analogComputationCandidate = true
  ; synapticStorageFieldExpressionSeparation = true
  ; consciousnessPromotionBlocked = true
  ; autismClinicalPromotionBlocked = true
  ; universalWaveTheoryBlocked = true
  ; interpretation = "Synaptic and molecular structure stores and generates constraints; population electric fields may express, gate, coordinate, and transform activity, subject to causal perturbation and cross-scale validation"
  }
