module DASHI.Biology.TernaryMorphogeneticVisualFieldExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.MorphogeneticVisualGenerator as Morphogenesis
import DASHI.Biology.TernaryVisualMotifSemiconjugacyExact as Semiconjugacy
import DASHI.Biology.VisualMotifTransitionOperator as Motif

------------------------------------------------------------------------
-- Ternary indexing of the existing morphogenetic field states.  The trit is
-- an index/quotient coordinate, not a claim that biological chemistry is
-- intrinsically Yijing-valued.
--
-- Provenance is inherited from MorphogeneticVisualGenerator: Turing 1952,
-- Smith et al. 2006, Runions et al. 2007, and Witten--Sander 1981.

parameterOfTrit :
  Triadic.KernelTrit → Morphogenesis.ChemicalParameter
parameterOfTrit Triadic.negativeTrit = Morphogenesis.stableParameter
parameterOfTrit Triadic.zeroTrit = Morphogenesis.anisotropicParameter
parameterOfTrit Triadic.positiveTrit = Morphogenesis.branchingParameter

fieldOfTrit :
  Triadic.KernelTrit → Morphogenesis.ChemicalFieldState
fieldOfTrit t =
  Morphogenesis.evolveChemical
    (parameterOfTrit t)
    Morphogenesis.homogeneousField

phaseOfField :
  Morphogenesis.ChemicalFieldState → Triadic.KernelTrit
phaseOfField Morphogenesis.homogeneousField = Triadic.negativeTrit
phaseOfField Morphogenesis.squareModeField = Triadic.zeroTrit
phaseOfField Morphogenesis.branchingModeField = Triadic.positiveTrit

fieldSection :
  (t : Triadic.KernelTrit) →
  phaseOfField (fieldOfTrit t) ≡ t
fieldSection Triadic.negativeTrit = refl
fieldSection Triadic.zeroTrit = refl
fieldSection Triadic.positiveTrit = refl

motifOfField :
  Morphogenesis.ChemicalFieldState → Motif.MotifState
motifOfField field =
  Semiconjugacy.motifOfTrit (phaseOfField field)

tritIndexedFieldProjectsToTritMotif :
  (t : Triadic.KernelTrit) →
  motifOfField (fieldOfTrit t)
  ≡
  Semiconjugacy.motifOfTrit t
tritIndexedFieldProjectsToTritMotif Triadic.negativeTrit = refl
tritIndexedFieldProjectsToTritMotif Triadic.zeroTrit = refl
tritIndexedFieldProjectsToTritMotif Triadic.positiveTrit = refl

squareModeProjectsToTunnel :
  motifOfField Morphogenesis.squareModeField ≡ Motif.tunnelMotif
squareModeProjectsToTunnel = refl

branchingModeProjectsToFace :
  motifOfField Morphogenesis.branchingModeField ≡ Motif.faceMotif
branchingModeProjectsToFace = refl

record TernaryMorphogeneticFieldBoundary : Set where
  constructor ternaryMorphogeneticFieldBoundary
  field
    tritIndexIsChemicalMechanism : Bool
    tritIndexIsChemicalMechanismIsFalse :
      tritIndexIsChemicalMechanism ≡ false

    projectedMotifUniquelyRecoversField : Bool
    projectedMotifUniquelyRecoversFieldIsFalse :
      projectedMotifUniquelyRecoversField ≡ false

canonicalTernaryMorphogeneticFieldBoundary :
  TernaryMorphogeneticFieldBoundary
canonicalTernaryMorphogeneticFieldBoundary =
  ternaryMorphogeneticFieldBoundary false refl false refl
