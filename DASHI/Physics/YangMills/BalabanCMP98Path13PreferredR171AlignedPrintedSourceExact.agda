{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13PreferredR171AlignedPrintedSourceExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): LEAST-PRIVILEGE R171-ALIGNED PRINTED-ROLE SOURCE
--
-- Independent payments:
--   * R171-aligned physical Path13 source;
--   * minimal printed dexpPlus/Jplus/Ad(exp) semantics + chart weld;
--   * direct literal 74-link budget inclusion 37/1024 <= selected cut radius;
--   * rational -> legacy-real ring embedding.
--
-- T3 and the older 1/24 cut are compatibility producers, not primitive inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13R171AlignedVariationalRouteExact as Aligned
import DASHI.Physics.YangMills.BalabanPath13SplitPhysicalStandardOperatorCutExact as Split
import DASHI.Physics.YangMills.BalabanPath13SplitPhysicalPrincipalImageRouteExact as Principal
import DASHI.Physics.YangMills.BalabanPath13DirectRelative74CutExact as Direct74
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedFamilyGeometryExact as Reduced
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedSemanticOperatorsExact as Printed
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedOperatorChartWeldExact as Weld
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedRoleSourceFamilyExact as Source
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

splitRepresentation :
  ∀ {CoarseField} →
  Aligned.R171AlignedPath13PhysicalInputs CoarseField →
  Split.SplitPath13PhysicalStandardRepresentation CoarseField
splitRepresentation = Aligned.asSplitPath13PhysicalStandardRepresentation

selectedGeometry :
  ∀ {CoarseField} →
  Aligned.R171AlignedPath13PhysicalInputs CoarseField →
  Family.Path13FamilyGeometry CoarseField
selectedGeometry inputs =
  Reduced.asPath13FamilyGeometry
    (Principal.reducedGeometry (splitRepresentation inputs))

record R171AlignedSelectedPrintedSemantics
    {CoarseField : Set}
    (physical : Aligned.R171AlignedPath13PhysicalInputs CoarseField) : Set₁ where
  field
    operators : Printed.PrintedSemanticOperators
    chartWeld : Weld.PrintedOperatorChartWeld
      (selectedGeometry physical) operators
open R171AlignedSelectedPrintedSemantics public

record PreferredR171AlignedPrintedPath13Inputs
    (CoarseField : Set) : Set₁ where
  field
    physical : Aligned.R171AlignedPath13PhysicalInputs CoarseField
    scalarEmbedding : R208.RationalRealRingEmbedding
    printedSemantics : R171AlignedSelectedPrintedSemantics physical
    relative74CutThreshold : Direct74.SplitPath13Relative74CutThreshold
      (splitRepresentation physical)
open PreferredR171AlignedPrintedPath13Inputs public

asPrintedRoleInputs :
  ∀ {CoarseField} →
  PreferredR171AlignedPrintedPath13Inputs CoarseField →
  Source.PrintedRolePath13SourceFamilyInputs CoarseField
asPrintedRoleInputs inputs =
  let
    representation = splitRepresentation (physical inputs)
    geometry = selectedGeometry (physical inputs)
    ops = operators (printedSemantics inputs)
    admission = Direct74.directRelative74InPrincipalImage
      representation (relative74CutThreshold inputs)
  in record
    { Source.PrintedRolePath13SourceFamilyInputs.geometry = geometry
    ; Source.PrintedRolePath13SourceFamilyInputs.scalarEmbedding =
        scalarEmbedding inputs
    ; Source.PrintedRolePath13SourceFamilyInputs.printedOperators = ops
    ; Source.PrintedRolePath13SourceFamilyInputs.relativeContourInPrincipalImage =
        admission
    ; Source.PrintedRolePath13SourceFamilyInputs.pointYRelevant =
        λ bond step point →
          Weld.principalPointYRelevant
            (chartWeld (printedSemantics inputs))
            (Family.erasedRelativeContour geometry bond step point)
            (admission bond step point)
    }

preferredR171AlignedPrintedPath13Equation119QPrime :
  ∀ {CoarseField} →
  PreferredR171AlignedPrintedPath13Inputs CoarseField →
  Nat → Perturbation.Path13RationalPerturbation →
  Family.Path13PositiveBond → Lie.SU2LieAlgebra
preferredR171AlignedPrintedPath13Equation119QPrime inputs =
  Source.printedRolePath13Equation119QPrime (asPrintedRoleInputs inputs)

preferredR171AlignedPrintedPath13Equation119QPrimeExact :
  ∀ {CoarseField}
    (inputs : PreferredR171AlignedPrintedPath13Inputs CoarseField)
    step perturbation bond →
  preferredR171AlignedPrintedPath13Equation119QPrime
    inputs step perturbation bond
  ≡ Source.printedRolePath13Equation119QPrime
      (asPrintedRoleInputs inputs) step perturbation bond
preferredR171AlignedPrintedPath13Equation119QPrimeExact inputs step perturbation bond = refl

preferredR171AlignedPrintedSourceCompilerLevel : ProofLevel
preferredR171AlignedPrintedSourceCompilerLevel = machineChecked

literalPreferredR171AlignedPrintedSourceInputsLevel : ProofLevel
literalPreferredR171AlignedPrintedSourceInputsLevel = conditional
