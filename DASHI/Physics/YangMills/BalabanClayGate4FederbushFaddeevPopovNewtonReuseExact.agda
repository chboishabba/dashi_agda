module DASHI.Physics.YangMills.BalabanClayGate4FederbushFaddeevPopovNewtonReuseExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as Quantitative
import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeNewtonImplicitFunctionExact as Newton
import DASHI.Physics.YangMills.BalabanClayGate4CMP109GroupAverageImplicitDerivativeExact as Federbush
import DASHI.Physics.YangMills.BalabanClayGate4TreeBackgroundSliceTransitionExact as Slice
import DASHI.Physics.YangMills.BalabanClayGate4FederbushFaddeevPopovQuantitativeIFTReuseExact as Reuse

------------------------------------------------------------------------
-- Newton realization of both quantitative implicit-function applications.
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (2) (1970), 284--286.
-- DOI: 10.1137/1012051.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- Both the Federbush centre and the background-gauge slice now use a literal
-- Newton residual map.  Fixed-point/residual equivalence is supplied by the
-- common algebra, rather than by two application-specific assumptions.
------------------------------------------------------------------------

record FederbushNewtonClosure
    (Input Centre Correction Residual Bound : Set) : Set₁ where
  field
    newtonInputs : Newton.QuantitativeNewtonIFTInputs
      Input Centre Correction Residual Bound

    differential :
      Federbush.FederbushImplicitDifferential Input Centre Residual

    physicalDifferential :
      Federbush.PhysicalFederbushAverageDerivative Input Centre Residual

    physicalDifferentialUsesSelectedData :
      Federbush.implicitData physicalDifferential ≡ differential

    QuantitativeResidualIsFederbushEquation : Set
    quantitativeResidualIsFederbushEquation :
      QuantitativeResidualIsFederbushEquation

open FederbushNewtonClosure public

asFederbushQuantitativeClosure :
  ∀ {Input Centre Correction Residual Bound} →
  FederbushNewtonClosure Input Centre Correction Residual Bound →
  Reuse.FederbushQuantitativeClosure Input Centre Residual Bound
asFederbushQuantitativeClosure closure = record
  { implicitFunction =
      Newton.asQuantitativeImplicitFunctionData (newtonInputs closure)
  ; differential = differential closure
  ; physicalDifferential =
      physicalDifferential closure
  ; physicalDifferentialUsesSelectedData =
      physicalDifferentialUsesSelectedData closure
  ; QuantitativeResidualIsFederbushEquation =
      QuantitativeResidualIsFederbushEquation closure
  ; quantitativeResidualIsFederbushEquation =
      quantitativeResidualIsFederbushEquation closure
  }

record BackgroundSliceNewtonClosure
    (TreeSlice BackgroundSlice Correction Residual
      TreeTangent BackgroundTangent Bound : Set) : Set₁ where
  field
    newtonInputs : Newton.QuantitativeNewtonIFTInputs
      TreeSlice BackgroundSlice Correction Residual Bound

    transition : Slice.LocalSliceTransition
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent

    implicitSolutionIsTransition : ∀ tree
      (admissible : Quantitative.AdmissibleInput
        (Newton.asQuantitativeImplicitFunctionData newtonInputs) tree) →
      Quantitative.implicitSolution
        (Newton.asQuantitativeImplicitFunctionData newtonInputs)
        tree admissible
      ≡ Slice.toBackground transition tree

    QuantitativeResidualIsBackgroundGaugeCondition : Set
    quantitativeResidualIsBackgroundGaugeCondition :
      QuantitativeResidualIsBackgroundGaugeCondition

open BackgroundSliceNewtonClosure public

asBackgroundSliceQuantitativeClosure :
  ∀ {TreeSlice BackgroundSlice Correction Residual
      TreeTangent BackgroundTangent Bound} →
  BackgroundSliceNewtonClosure
    TreeSlice BackgroundSlice Correction Residual
    TreeTangent BackgroundTangent Bound →
  Reuse.BackgroundSliceQuantitativeClosure
    TreeSlice BackgroundSlice TreeTangent BackgroundTangent Bound
asBackgroundSliceQuantitativeClosure closure = record
  { implicitFunction =
      Newton.asQuantitativeImplicitFunctionData (newtonInputs closure)
  ; transition = transition closure
  ; implicitSolutionIsTransition =
      implicitSolutionIsTransition closure
  ; QuantitativeResidualIsBackgroundGaugeCondition =
      QuantitativeResidualIsBackgroundGaugeCondition closure
  ; quantitativeResidualIsBackgroundGaugeCondition =
      quantitativeResidualIsBackgroundGaugeCondition closure
  }

record SharedNewtonApplications
    (FederbushInput FederbushCentre FederbushCorrection FederbushResidual
      TreeSlice BackgroundSlice BackgroundCorrection BackgroundResidual
      TreeTangent BackgroundTangent Bound : Set) : Set₁ where
  field
    federbush : FederbushNewtonClosure
      FederbushInput FederbushCentre FederbushCorrection FederbushResidual Bound

    backgroundSlice : BackgroundSliceNewtonClosure
      TreeSlice BackgroundSlice BackgroundCorrection BackgroundResidual
      TreeTangent BackgroundTangent Bound

    federbushRadiusBudget backgroundSliceRadiusBudget :
      Quantitative.QuantitativeRadiusBudget Bound

    CommonNormAndScalarConvention : Set
    commonNormAndScalarConvention : CommonNormAndScalarConvention

open SharedNewtonApplications public

asSharedQuantitativeIFTApplications :
  ∀ {FederbushInput FederbushCentre FederbushCorrection FederbushResidual
      TreeSlice BackgroundSlice BackgroundCorrection BackgroundResidual
      TreeTangent BackgroundTangent Bound} →
  SharedNewtonApplications
    FederbushInput FederbushCentre FederbushCorrection FederbushResidual
    TreeSlice BackgroundSlice BackgroundCorrection BackgroundResidual
    TreeTangent BackgroundTangent Bound →
  Reuse.SharedQuantitativeIFTApplications
    FederbushInput FederbushCentre FederbushResidual
    TreeSlice BackgroundSlice TreeTangent BackgroundTangent Bound
asSharedQuantitativeIFTApplications applications = record
  { federbush =
      asFederbushQuantitativeClosure (federbush applications)
  ; backgroundSlice =
      asBackgroundSliceQuantitativeClosure (backgroundSlice applications)
  ; federbushRadiusBudget =
      federbushRadiusBudget applications
  ; backgroundSliceRadiusBudget =
      backgroundSliceRadiusBudget applications
  ; CommonNormAndScalarConvention =
      CommonNormAndScalarConvention applications
  ; commonNormAndScalarConvention =
      commonNormAndScalarConvention applications
  }

sharedFederbushNewtonIFTAssemblyLevel : ProofLevel
sharedFederbushNewtonIFTAssemblyLevel = machineChecked

sharedBackgroundSliceNewtonIFTAssemblyLevel : ProofLevel
sharedBackgroundSliceNewtonIFTAssemblyLevel = machineChecked

sharedNewtonApplicationsReuseLevel : ProofLevel
sharedNewtonApplicationsReuseLevel = machineChecked

physicalFederbushResidualAndCorrectionIdentificationInputsLevel : ProofLevel
physicalFederbushResidualAndCorrectionIdentificationInputsLevel = conditional

physicalBackgroundGaugeResidualAndCorrectionIdentificationInputsLevel : ProofLevel
physicalBackgroundGaugeResidualAndCorrectionIdentificationInputsLevel = conditional
