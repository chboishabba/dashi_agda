module DASHI.Biology.Protein.ProteinContractiveBasinBridge where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Analysis.StrictContractionUniqueness as SCU
import DASHI.Physics.YangMills.BalabanFiniteOneStepCore as BFO
import DASHI.Energy.Core as EC
import DASHI.Biology.Protein.ProteinConformationAttractor as PCA
import DASHI.Biology.Protein.ProteinFejerBasinBridge as PFB

------------------------------------------------------------------------
-- Composition of two independent certificates:
--
-- * Fejer monotonicity + sublevel identification gives basin invariance;
-- * strict contraction + irreflexive strict distance gives fixed-point
--   uniqueness on the declared contraction carrier.
--
-- The carrier may be a local certified region.  No global uniqueness claim is
-- made for the ambient conformational landscape.
------------------------------------------------------------------------

record ProteinContractiveBasinBridge
    {e d : Level}
    (P : PCA.ProteinConformationSystem)
    (Energy : Set e)
    (ES : EC.EnergySpace
      (PCA.ProteinConformationSystem.Conformation P)
      Energy)
    (Distance : Set d)
    (fejerBridge : PFB.ProteinFejerBasinBridge P Energy ES)
    : Set (lsuc (e ⊔ d)) where
  field
    contraction :
      BFO.FiniteContractionCertificate
        (PCA.ProteinConformationSystem.Conformation P)
        Distance

    contractionStepMatchesProtein :
      (x : PCA.ProteinConformationSystem.Conformation P) →
      BFO.FiniteContractionCertificate.step contraction x
        ≡ PCA.ProteinConformationSystem.step P
            (PFB.sequence fejerBridge)
            (PFB.environment fejerBridge)
            x

    strictDistance :
      SCU.IrreflexiveStrictDistance Distance
        (BFO.FiniteContractionCertificate.StrictlySmaller contraction)

    contractionFixedInBasin :
      PCA.ProteinConformationSystem.InBasin P
        (PFB.attractor fejerBridge)
        (BFO.FiniteContractionCertificate.fixedPoint contraction)

open ProteinContractiveBasinBridge public

proteinFixedConformationUnique :
  ∀ {e d P Energy ES Distance fejerBridge} →
  (B : ProteinContractiveBasinBridge
    {e} {d} P Energy ES Distance fejerBridge) →
  (candidate : PCA.ProteinConformationSystem.Conformation P) →
  PCA.ProteinConformationSystem.step P
    (PFB.sequence fejerBridge)
    (PFB.environment fejerBridge)
    candidate
    ≡ candidate →
  candidate
    ≡ BFO.FiniteContractionCertificate.fixedPoint (contraction B)
proteinFixedConformationUnique B candidate proteinFixed =
  SCU.strictContractionFixedPointUnique
    (contraction B)
    (strictDistance B)
    candidate
    (trans
      (contractionStepMatchesProtein B candidate)
      proteinFixed)

record ProteinCertifiedLocalAttractor
    {e d : Level}
    {P : PCA.ProteinConformationSystem}
    {Energy : Set e}
    {ES : EC.EnergySpace
      (PCA.ProteinConformationSystem.Conformation P)
      Energy}
    {Distance : Set d}
    {fejerBridge : PFB.ProteinFejerBasinBridge P Energy ES}
    (B : ProteinContractiveBasinBridge
      P Energy ES Distance fejerBridge)
    : Set (lsuc (e ⊔ d)) where
  field
    attractorWitness :
      PCA.ConformationalAttractorWitness P

    fixedConformation :
      PCA.ProteinConformationSystem.Conformation P

    fixedConformationInBasin :
      PCA.ProteinConformationSystem.InBasin P
        (PFB.attractor fejerBridge)
        fixedConformation

    fixedConformationChemicallyAdmissible :
      PCA.ProteinConformationSystem.ChemicallyAdmissible P
        (PFB.sequence fejerBridge)
        fixedConformation

    uniqueFixedConformation :
      (candidate : PCA.ProteinConformationSystem.Conformation P) →
      PCA.ProteinConformationSystem.step P
        (PFB.sequence fejerBridge)
        (PFB.environment fejerBridge)
        candidate
        ≡ candidate →
      candidate ≡ fixedConformation

open ProteinCertifiedLocalAttractor public

certifyProteinLocalAttractor :
  ∀ {e d P Energy ES Distance fejerBridge} →
  (B : ProteinContractiveBasinBridge
    {e} {d} P Energy ES Distance fejerBridge) →
  ProteinCertifiedLocalAttractor B
certifyProteinLocalAttractor {fejerBridge = F} B = record
  { attractorWitness = PFB.proteinFejerAttractorWitness F
  ; fixedConformation =
      BFO.FiniteContractionCertificate.fixedPoint (contraction B)
  ; fixedConformationInBasin = contractionFixedInBasin B
  ; fixedConformationChemicallyAdmissible =
      PFB.admissibleInBasin F
        (BFO.FiniteContractionCertificate.fixedPoint (contraction B))
        (contractionFixedInBasin B)
  ; uniqueFixedConformation = proteinFixedConformationUnique B
  }
