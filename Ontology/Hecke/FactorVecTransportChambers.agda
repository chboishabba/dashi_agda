module Ontology.Hecke.FactorVecTransportChambers where

open import Agda.Builtin.Bool     using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.FactorVecMultiLaneTransport using
  (PairMode; pairLegal; factorVecMultiLaneTransport)
import Ontology.Hecke.TransportChambers as HC

------------------------------------------------------------------------
-- The first exact chamber carrier is the legality signature itself:
-- a state is represented by the set of pair-modes that are legal on it.
-- Later work can try to compress this exact chamber data.

PairModeSignature : Set
PairModeSignature = PairMode → Bool

pairModeSignature : FactorVec → PairModeSignature
pairModeSignature v m = pairLegal m v

pairModeLegalOnSignature : PairMode → PairModeSignature → Bool
pairModeLegalOnSignature m sig = sig m

factorVecPairChamberWitness :
  HC.ChamberWitnessOn PairMode FactorVec PairModeSignature
factorVecPairChamberWitness = record
  { transport      = factorVecMultiLaneTransport
  ; chamber        = pairModeSignature
  ; legalOnChamber = pairModeLegalOnSignature
  ; legal-sound    = λ m s → refl
  }

samePairChamber : FactorVec → FactorVec → Set
samePairChamber = HC.ChamberWitnessOn.sameChamber factorVecPairChamberWitness

samePairChamber-respects-legal :
  ∀ m x y →
  samePairChamber x y →
  pairLegal m x ≡ pairLegal m y
samePairChamber-respects-legal =
  HC.ChamberWitnessOn.legal-respects-sameChamber factorVecPairChamberWitness
