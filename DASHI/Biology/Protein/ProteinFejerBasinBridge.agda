module DASHI.Biology.Protein.ProteinFejerBasinBridge where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Energy.Core as EC
import DASHI.Energy.Fejer as FE
import DASHI.Analysis.FejerSublevelInvariant as FSI
import DASHI.Biology.Protein.ProteinConformationAttractor as PCA

------------------------------------------------------------------------
-- Protein basin invariance from Fejer monotonicity.
--
-- A folding update need not be a global contraction.  It is enough, on a
-- certified region, that distance to a basin centre is Fejer monotone and that
-- the biological basin is identified with a sublevel set of that distance.
-- The generic theorem is owned by `FejerSublevelInvariant`; this module only
-- supplies the protein interpretation and existing attractor witness.
------------------------------------------------------------------------

record ProteinFejerBasinBridge
    {e : Level}
    (P : PCA.ProteinConformationSystem)
    (Energy : Set e)
    (ES : EC.EnergySpace
      (PCA.ProteinConformationSystem.Conformation P)
      Energy)
    : Set (lsuc e) where
  field
    sequence :
      PCA.ProteinConformationSystem.Sequence P

    environment :
      PCA.ProteinConformationSystem.Environment P

    attractor :
      PCA.ProteinConformationSystem.Attractor P

    basinCentre :
      PCA.ProteinConformationSystem.Conformation P

    transition :
      PCA.ProteinConformationSystem.Conformation P →
      PCA.ProteinConformationSystem.Conformation P

    transitionMatchesProteinStep :
      (x : PCA.ProteinConformationSystem.Conformation P) →
      transition x
        ≡ PCA.ProteinConformationSystem.step P sequence environment x

    fejerPoint :
      FE.FejerPoint ES transition basinCentre

    radius : Energy

    basinToSublevel :
      (x : PCA.ProteinConformationSystem.Conformation P) →
      PCA.ProteinConformationSystem.InBasin P attractor x →
      EC.Preorder._≤_ (EC.EnergySpace.P ES)
        (FE.FejerPoint.d fejerPoint x basinCentre)
        radius

    sublevelToBasin :
      (x : PCA.ProteinConformationSystem.Conformation P) →
      EC.Preorder._≤_ (EC.EnergySpace.P ES)
        (FE.FejerPoint.d fejerPoint x basinCentre)
        radius →
      PCA.ProteinConformationSystem.InBasin P attractor x

    stable :
      PCA.ProteinConformationSystem.StableAt P
        sequence environment attractor

    admissibleInBasin :
      (x : PCA.ProteinConformationSystem.Conformation P) →
      PCA.ProteinConformationSystem.InBasin P attractor x →
      PCA.ProteinConformationSystem.ChemicallyAdmissible P sequence x

open ProteinFejerBasinBridge public

proteinSublevelInvariant :
  ∀ {e P Energy ES} →
  (B : ProteinFejerBasinBridge {e} P Energy ES) →
  FSI.FejerSublevelInvariant
    ES
    (transition B)
    (basinCentre B)
    (PCA.ProteinConformationSystem.InBasin P (attractor B))
    (radius B)
proteinSublevelInvariant B = record
  { fejerPoint = fejerPoint B
  ; memberToSublevel = basinToSublevel B
  ; sublevelToMember = sublevelToBasin B
  }

fejerTransitionStaysInBasin :
  ∀ {e P Energy ES} →
  (B : ProteinFejerBasinBridge {e} P Energy ES) →
  (x : PCA.ProteinConformationSystem.Conformation P) →
  PCA.ProteinConformationSystem.InBasin P (attractor B) x →
  PCA.ProteinConformationSystem.InBasin P
    (attractor B)
    (transition B x)
fejerTransitionStaysInBasin B =
  FSI.fejerPreservesSublevel (proteinSublevelInvariant B)

proteinStepStaysInBasin :
  ∀ {e P Energy ES} →
  (B : ProteinFejerBasinBridge {e} P Energy ES) →
  (x : PCA.ProteinConformationSystem.Conformation P) →
  PCA.ProteinConformationSystem.InBasin P (attractor B) x →
  PCA.ProteinConformationSystem.InBasin P
    (attractor B)
    (PCA.ProteinConformationSystem.step P
      (sequence B)
      (environment B)
      x)
proteinStepStaysInBasin {P = P} B x inBasin =
  subst
    (PCA.ProteinConformationSystem.InBasin P (attractor B))
    (transitionMatchesProteinStep B x)
    (fejerTransitionStaysInBasin B x inBasin)

iterateProteinStep :
  (P : PCA.ProteinConformationSystem) →
  PCA.ProteinConformationSystem.Sequence P →
  PCA.ProteinConformationSystem.Environment P →
  Nat →
  PCA.ProteinConformationSystem.Conformation P →
  PCA.ProteinConformationSystem.Conformation P
iterateProteinStep P sequence environment zero x = x
iterateProteinStep P sequence environment (suc n) x =
  iterateProteinStep P sequence environment n
    (PCA.ProteinConformationSystem.step P sequence environment x)

proteinIteratesStayInBasin :
  ∀ {e P Energy ES} →
  (B : ProteinFejerBasinBridge {e} P Energy ES) →
  (n : Nat) →
  (x : PCA.ProteinConformationSystem.Conformation P) →
  PCA.ProteinConformationSystem.InBasin P (attractor B) x →
  PCA.ProteinConformationSystem.InBasin P
    (attractor B)
    (iterateProteinStep P (sequence B) (environment B) n x)
proteinIteratesStayInBasin B zero x inBasin = inBasin
proteinIteratesStayInBasin {P = P} B (suc n) x inBasin =
  proteinIteratesStayInBasin B n
    (PCA.ProteinConformationSystem.step P (sequence B) (environment B) x)
    (proteinStepStaysInBasin B x inBasin)

proteinFejerAttractorWitness :
  ∀ {e P Energy ES} →
  ProteinFejerBasinBridge {e} P Energy ES →
  PCA.ConformationalAttractorWitness P
proteinFejerAttractorWitness B = record
  { sequence = sequence B
  ; environment = environment B
  ; attractor = attractor B
  ; stable = stable B
  ; forwardInvariant = proteinStepStaysInBasin B
  ; admissibleInBasin = admissibleInBasin B
  }
