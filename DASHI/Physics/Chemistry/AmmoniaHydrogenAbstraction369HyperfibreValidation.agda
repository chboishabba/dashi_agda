module DASHI.Physics.Chemistry.AmmoniaHydrogenAbstraction369HyperfibreValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaHydrogenAbstraction369HyperfibreExact as H
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Fibre

sourceAtomWeldIsLiteral :
  Fibre.ChemistryFibre.atomMoleculeWeld H.sourceFibre ≡ refl
sourceAtomWeldIsLiteral = refl

targetAtomWeldIsLiteral :
  Fibre.ChemistryFibre.atomMoleculeWeld H.targetFibre ≡ refl
targetAtomWeldIsLiteral = refl

transportPreservesProvenance :
  Fibre.ChemistryFibreTransport.sourceProvenancePreserved H.abstractionTransport ≡ true
transportPreservesProvenance = refl

literalHyperformInhabited :
  H.HyperformBoundary.literalChemistryHyperfibreInhabited
    H.canonicalHyperformBoundary ≡ true
literalHyperformInhabited = refl

mechanismSourceAttached :
  H.HyperformBoundary.sourceBackedMechanismAttached
    H.canonicalHyperformBoundary ≡ true
mechanismSourceAttached = refl
