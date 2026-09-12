module DASHI.Biology.JasonThomasSignallingFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.JasonThomasSignallingBidiExact as T

record FiniteThomasSignallingWitness : Set where
  constructor finite-thomas-signalling-witness
  field
    sourceReferences : String
    perturbations : List T.Perturbation
    signallingReadouts : List T.SignallingReadout
    autophagyObjects : List T.AutophagyObject
    finiteScreenHits : Nat
    finiteValidatedHits : Nat
    syntheticAssayCounts : Bool
    sourceAssayReproduced : Bool
    nextExactLeaf : String

open FiniteThomasSignallingWitness public

finiteThomasSignallingWitness : FiniteThomasSignallingWitness
finiteThomasSignallingWitness = finite-thomas-signalling-witness
  "DOI 10.1021/acschembio.7b01060; DOI 10.1038/ncb3053"
  (T.STINGAgonist ∷ T.candidateAntagonist ∷ T.PIKIII ∷ T.VPS34Loss ∷ [])
  (T.IRF3NuclearTranslocation ∷ T.NFkBNuclearTranslocation ∷ T.downstreamActivation ∷ [])
  (T.LC3 ∷ T.NCOA4 ∷ T.ferritin ∷ T.ironPool ∷ [])
  8
  2
  true
  false
  "replace synthetic screen counts with one Thomas-authored source assay, target-deconvolution receipt and ferritinophagy validation chain"

finiteWitnessSeparatesHitFromValidatedMechanism : Bool
finiteWitnessSeparatesHitFromValidatedMechanism = true

screenHitPaysDirectTarget : Bool
screenHitPaysDirectTarget = false

finiteWitnessPaysTherapeuticEfficacy : Bool
finiteWitnessPaysTherapeuticEfficacy = false
