module DASHI.Foundations.CandidateIndexedFiniteRestrictionFamilyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Make the finite reduction lens candidate-indexed:
--
--   j -> H_j -> Res_(H_j) V_j -> Sigma_(H_j)(j).
--
-- A fixed D4/A4/S4/A5 restriction is a constant-target special case.  The
-- regular-shift controls show that those fixed lenses are too weak to select
-- Ogg by themselves.  The frontier SSP thesis therefore lives at this richer
-- dependent-family level (or at an equivalent higher-order carrier), without
-- hard-coding the known Ogg list into the family.
--
-- The assembled FiniteRestriction is not a caller-supplied independent field:
-- it is definitionally built from the same targetFamily, branchingAt and
-- fixedSpacesAt.  This prevents a dependent-family receipt from silently
-- carrying an unrelated restriction object.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Set₂)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.FiniteRepresentationRestrictionCore as Core
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.PolyhedralFiniteRestrictionInstancesExact as Poly
import DASHI.Foundations.OctahedralSO3RestrictionJ0To35Exact as Oct
import DASHI.Foundations.IcosahedralSO3RestrictionJ0To35Exact as Ico

record CandidateIndexedFiniteRestrictionFamily : Set₂ where
  field
    targetFamily :
      Spin.AngularMomentum0To35 → Core.FiniteIrrepFamily

    branchingAt :
      (j : Spin.AngularMomentum0To35) →
      Core.BranchingSpectrum
        (Spin.continuousSO3Irrep j)
        (targetFamily j)

    fixedSpacesAt :
      Spin.AngularMomentum0To35 → Core.FixedSpaceSpectrum

    restrictionReceiptAt :
      Spin.AngularMomentum0To35 → String

    familyLabel : String

    knownOggListUsedToChooseTarget : Bool
    knownOggListUsedToChooseTargetIsFalse :
      knownOggListUsedToChooseTarget ≡ false

open CandidateIndexedFiniteRestrictionFamily public

assembledRestriction :
  (family : CandidateIndexedFiniteRestrictionFamily) →
  (j : Spin.AngularMomentum0To35) → Core.FiniteRestriction
assembledRestriction family j =
  Core.finite-restriction
    (Spin.continuousSO3Irrep j)
    (targetFamily family j)
    (branchingAt family j)
    (fixedSpacesAt family j)
    (restrictionReceiptAt family j)

------------------------------------------------------------------------
-- Fixed-group control families.
------------------------------------------------------------------------

octahedralConstantFamily : CandidateIndexedFiniteRestrictionFamily
octahedralConstantFamily =
  record
    { targetFamily = λ _ → Oct.octahedralFamily
    ; branchingAt = Oct.octahedralBranching
    ; fixedSpacesAt = Poly.octahedralFixedSpaces
    ; restrictionReceiptAt =
        λ _ → "SO(3) angular-momentum irrep restricted to rotational S4 control"
    ; familyLabel = "constant rotational-octahedral S4 control family"
    ; knownOggListUsedToChooseTarget = false
    ; knownOggListUsedToChooseTargetIsFalse = refl
    }

icosahedralConstantFamily : CandidateIndexedFiniteRestrictionFamily
icosahedralConstantFamily =
  record
    { targetFamily = λ _ → Ico.icosahedralFamily
    ; branchingAt = Ico.icosahedralBranching
    ; fixedSpacesAt = Poly.icosahedralFixedSpaces
    ; restrictionReceiptAt =
        λ _ → "SO(3) angular-momentum irrep restricted to rotational A5 control"
    ; familyLabel = "constant rotational-icosahedral A5 control family"
    ; knownOggListUsedToChooseTarget = false
    ; knownOggListUsedToChooseTargetIsFalse = refl
    }

octahedralAssemblyUsesDeclaredTarget :
  (j : Spin.AngularMomentum0To35) →
  Core.targetFamily (assembledRestriction octahedralConstantFamily j)
  ≡ Oct.octahedralFamily
octahedralAssemblyUsesDeclaredTarget j = refl

icosahedralAssemblyUsesDeclaredBranching :
  (j : Spin.AngularMomentum0To35) →
  Core.branching (assembledRestriction icosahedralConstantFamily j)
  ≡ Ico.icosahedralBranching j
icosahedralAssemblyUsesDeclaredBranching j = refl

------------------------------------------------------------------------
-- A future candidate-dependent selector must supply its own target family.
------------------------------------------------------------------------

data ConstructedExactSSPReductionFamily : Set where

noExactSSPReductionFamilyConstructedHere :
  ConstructedExactSSPReductionFamily → ⊥
noExactSSPReductionFamilyConstructedHere ()

record CandidateIndexedRestrictionBoundary : Set where
  field
    candidateDependentTargetRepresentable : Bool
    candidateDependentTargetRepresentableIsTrue :
      candidateDependentTargetRepresentable ≡ true

    assembledRestrictionCannotDriftFromDeclaredBranching : Bool
    assembledRestrictionCannotDriftFromDeclaredBranchingIsTrue :
      assembledRestrictionCannotDriftFromDeclaredBranching ≡ true

    fixedPolyhedralControlFamiliesConstructed : Bool
    fixedPolyhedralControlFamiliesConstructedIsTrue :
      fixedPolyhedralControlFamiliesConstructed ≡ true

    exactOggSelectingReductionFamilyConstructed : Bool
    exactOggSelectingReductionFamilyConstructedIsFalse :
      exactOggSelectingReductionFamilyConstructed ≡ false

    targetFamilyMayReadExternalOggLabels : Bool
    targetFamilyMayReadExternalOggLabelsIsFalse :
      targetFamilyMayReadExternalOggLabels ≡ false

canonicalCandidateIndexedRestrictionBoundary : CandidateIndexedRestrictionBoundary
canonicalCandidateIndexedRestrictionBoundary =
  record
    { candidateDependentTargetRepresentable = true
    ; candidateDependentTargetRepresentableIsTrue = refl
    ; assembledRestrictionCannotDriftFromDeclaredBranching = true
    ; assembledRestrictionCannotDriftFromDeclaredBranchingIsTrue = refl
    ; fixedPolyhedralControlFamiliesConstructed = true
    ; fixedPolyhedralControlFamiliesConstructedIsTrue = refl
    ; exactOggSelectingReductionFamilyConstructed = false
    ; exactOggSelectingReductionFamilyConstructedIsFalse = refl
    ; targetFamilyMayReadExternalOggLabels = false
    ; targetFamilyMayReadExternalOggLabelsIsFalse = refl
    }
