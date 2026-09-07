{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13PreferredSplitPhysicalT3SourceFamilyExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13SplitPhysicalStandardOperatorCutExact as Split
import DASHI.Physics.YangMills.BalabanPath13SplitPhysicalPrincipalImageRouteExact as Principal
import DASHI.Physics.YangMills.BalabanCMP98Path13SplitT3SelectedSemanticsExact as T3Semantics
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedRoleSourceFamilyExact as Source
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedFamilyGeometryExact as Reduced
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record PreferredSplitPhysicalT3Path13Inputs
    (CoarseField Scalar : Set) : Set₁ where
  field
    splitRepresentation :
      Split.SplitPath13PhysicalStandardRepresentation CoarseField

    scalarEmbedding : R208.RationalRealRingEmbedding

    t3Semantics :
      T3Semantics.SplitSelectedT3PrintedSemantics
        {Scalar = Scalar} splitRepresentation

    cutThreshold :
      Principal.SplitPath13CutThreshold splitRepresentation
open PreferredSplitPhysicalT3Path13Inputs public

geometry :
  ∀ {CoarseField Scalar} →
  PreferredSplitPhysicalT3Path13Inputs CoarseField Scalar →
  Family.Path13FamilyGeometry CoarseField
geometry inputs =
  Reduced.asPath13FamilyGeometry
    (Principal.reducedGeometry (splitRepresentation inputs))

asPrintedRoleInputs :
  ∀ {CoarseField Scalar} →
  PreferredSplitPhysicalT3Path13Inputs CoarseField Scalar →
  Source.PrintedRolePath13SourceFamilyInputs CoarseField
asPrintedRoleInputs inputs =
  let
    split = splitRepresentation inputs
    geom = geometry inputs
    admission = Principal.relativeContourInPrincipalImage
      split (cutThreshold inputs)
    semantics = t3Semantics inputs
  in record
    { Source.PrintedRolePath13SourceFamilyInputs.geometry = geom
    ; Source.PrintedRolePath13SourceFamilyInputs.scalarEmbedding = scalarEmbedding inputs
    ; Source.PrintedRolePath13SourceFamilyInputs.printedOperators =
        T3Semantics.operators semantics
    ; Source.PrintedRolePath13SourceFamilyInputs.relativeContourInPrincipalImage =
        admission
    ; Source.PrintedRolePath13SourceFamilyInputs.pointYRelevant =
        λ bond step point →
          T3Semantics.principalPointYRelevant semantics
            (Family.erasedRelativeContour geom bond step point)
            (admission bond step point)
    }

preferredSplitPhysicalT3Path13Equation119QPrime :
  ∀ {CoarseField Scalar} →
  PreferredSplitPhysicalT3Path13Inputs CoarseField Scalar →
  Nat → Perturbation.Path13RationalPerturbation →
  Family.Path13PositiveBond → Lie.SU2LieAlgebra
preferredSplitPhysicalT3Path13Equation119QPrime inputs =
  Source.printedRolePath13Equation119QPrime (asPrintedRoleInputs inputs)

preferredSplitPhysicalT3Path13Equation119QPrimeExact :
  ∀ {CoarseField Scalar}
    (inputs : PreferredSplitPhysicalT3Path13Inputs CoarseField Scalar)
    step perturbation bond →
  preferredSplitPhysicalT3Path13Equation119QPrime inputs step perturbation bond
  ≡ Source.printedRolePath13Equation119QPrime
      (asPrintedRoleInputs inputs) step perturbation bond
preferredSplitPhysicalT3Path13Equation119QPrimeExact inputs step perturbation bond = refl

cmp98Path13PreferredSplitPhysicalT3AdapterLevel : ProofLevel
cmp98Path13PreferredSplitPhysicalT3AdapterLevel = machineChecked

-- The old combined SelectedPath13VariationalOperatorRepresentation is not a
-- primitive payment on this route.  Physical Eq. (119) remains conditional on
-- the four split source objects above being inhabited.
literalCMP98Path13PreferredSplitPhysicalT3InputsLevel : ProofLevel
literalCMP98Path13PreferredSplitPhysicalT3InputsLevel = conditional
