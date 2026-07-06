module DASHI.Physics.Closure.NSTriadKNForcedTailWeightedProductBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
import DASHI.Physics.Closure.NSTriadKNForcedTailClosureDependency as Dependency

------------------------------------------------------------------------
-- Fail-closed forced-tail weighted-product witness.
--
-- This surface records the exact sampled forced-tail Schur quantities from the
-- checked exact-script artifact.  It installs the strongest honest current
-- statement: a sampled N=6,8,10,12 witness for the forced-tail route, not a
-- uniform proof over all N.

data NSTriadKNForcedTailWeightedProductBoundPromotion : Set where

forcedTailWeightedProductBoundPromotionImpossibleHere :
  NSTriadKNForcedTailWeightedProductBoundPromotion → ⊥
forcedTailWeightedProductBoundPromotionImpossibleHere ()

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed receipt for the sampled forced-tail weighted-product witness on the exact scripted pair-incidence kernel."

canonicalArtifactMarkdown : String
canonicalArtifactMarkdown =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_acl_schur_test_proof_20260624/summary.md"

canonicalArtifactJSON : String
canonicalArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_pair_incidence_row_column_audit_20260625/summary.json"

canonicalCountingMagnitudeSurface : String
canonicalCountingMagnitudeSurface =
  "DASHI/Physics/Closure/NSTriadKNForcedTailCountingMagnitudeTheorem.agda"

canonicalKernelObject : String
canonicalKernelObject =
  "K^N(k,p) := -L_FT,script^N(k,p)"

canonicalForcedTailTarget : String
canonicalForcedTailTarget =
  "Forced-tail target: choose w_N so that R_N^FT(w_N) * C_N^FT(w_N) <= C_FT^2 / N^2."

canonicalCurrentWeightChoice : String
canonicalCurrentWeightChoice =
  "Current checked witness uses the unweighted positive-kernel Schur test, i.e. w_N = 1 on the sampled forced-tail family."

canonicalWitnessRows : String
canonicalWitnessRows =
  "Sampled rows: N=6 -> row 0.0114691, col 0.000340859, N*sqrt(row*col)=0.0118633; N=8 -> row 0.0114983, col 0.000190048, N*sqrt(row*col)=0.0118260; N=10 -> row 0.0116587, col 0.000139883, N*sqrt(row*col)=0.0127705; N=12 -> row 0.0116101, col 9.17093e-05, N*sqrt(row*col)=0.0123824."

canonicalScaledWitness : String
canonicalScaledWitness =
  "Scaled forced-tail witness: row_sum_sup stays in 0.0114691..0.0116587, N^2 * column_sum_sup stays in 0.0121631..0.0139883, and N * Schur bound stays in 0.0118260..0.0127705 across the checked shells."

canonicalFitReadout : String
canonicalFitReadout =
  "Forced-tail fit readout: row slope 0.0222 (nearly constant), column slope -1.842, Schur slope -0.9099. This is consistent with the product route row ~ N^0 and column ~ N^-2, but it is still only a sampled witness."

canonicalCountingMagnitudeRoute : String
canonicalCountingMagnitudeRoute =
  "Uniform forced-tail route: prove a row bound R_N^FT(w_N) <= A_FT and a column bound C_N^FT(w_N) <= B_FT / N^2, then conclude R_N^FT(w_N) * C_N^FT(w_N) <= C_FT^2 / N^2."

canonicalColumnAttackRoute : String
canonicalColumnAttackRoute =
  "Highest-alpha forced-tail attack: for each forced-tail column j, prove a multiplicity profile bound and a magnitude profile bound, show their product is <= B_FT / N^2 at the profile level, then feed that into the full forced-tail column theorem."

canonicalColumnClassRoute : String
canonicalColumnClassRoute =
  "Column-class refinement: classify each forced-tail column as tail-end, near-tail, transition-facing, or degenerate/small-N, then prove multiplicity and magnitude bounds classwise before recombining to the per-column product theorem."

canonicalMultiplicityCountRoute : String
canonicalMultiplicityCountRoute =
  "Multiplicity route refinement: first bound the per-column multiplicity profile by an explicit raw forced-tail incidence count, then prove that raw count is bounded by the classwise multiplicity target."

canonicalClassFilteredCountRoute : String
canonicalClassFilteredCountRoute =
  "Class-filtered count refinement: after introducing the raw per-column forced-tail incidence count, pass to the class-filtered raw count for class(j), and only then apply the classwise multiplicity bound."

canonicalClassMultiplicityFormulaRoute : String
canonicalClassMultiplicityFormulaRoute =
  "Explicit classwise count formula: after passing to the class-filtered raw count for class(j), bound it first by a named classwise multiplicity formula M_FT(N,class(j)), and only then compare that formula to the broader classwise multiplicity target."

canonicalClassEncodingRoute : String
canonicalClassEncodingRoute =
  "Encoding/count route: control the class-filtered raw incidence count by encoding each forced-tail class incidence into an explicit parameter family with bounded fibers, then bound the parameter count by M_FT(N,class(j))."

canonicalParameterFactorizationRoute : String
canonicalParameterFactorizationRoute =
  "Parameter-factorization refinement: split each class parameter into a head and a tail component, bound the number of heads and the maximal number of tails per head, and use that factorization to control the parameter count."

canonicalEncodedMultiplicityRoute : String
canonicalEncodedMultiplicityRoute =
  "First composed multiplicity theorem: combine the encoding fiber bound with the parameter-count bound to obtain class count <= kappa_FT(class(j)) * M_FT(N,class(j))."

canonicalClassMagnitudeFormulaRoute : String
canonicalClassMagnitudeFormulaRoute =
  "Explicit classwise magnitude formula: for the same class(j), bound the column magnitude profile first by a named classwise magnitude formula mu_FT(N,class(j)), and only then compare that formula to the broader classwise magnitude target."

canonicalMagnitudeEnvelopeRoute : String
canonicalMagnitudeEnvelopeRoute =
  "Magnitude-envelope route: bound each forced-tail incidence weight m_N(tau) by an explicit envelope, then bound that envelope classwise by mu_FT(N,class(j))."

canonicalEnvelopeMagnitudeRoute : String
canonicalEnvelopeMagnitudeRoute =
  "First composed magnitude theorem: combine the kernel-to-envelope bound with the class-envelope bound to obtain m_N(tau) <= mu_FT(N,class(j)) for each class-filtered forced-tail incidence."

canonicalClassFormulaProductRoute : String
canonicalClassFormulaProductRoute =
  "Formula-level class product route: prove M_FT(N,class(j)) * mu_FT(N,class(j)) <= the classwise formula product target before lifting that formula product to the broader classwise product target."

canonicalClassProductN2Route : String
canonicalClassProductN2Route =
  "N^2-scaled class product route: prove N^2 * M_FT(N,class(j)) * mu_FT(N,class(j)) <= a class constant B_FT,class(j), then feed that bound into the shellwise N^-2 column target."

canonicalColumnLiftRoute : String
canonicalColumnLiftRoute =
  "Lift route after the classwise estimates: classwise multiplicity/magnitude/product targets feed into the per-column profile target, and each per-column profile target must then lift into the shellwise N^-2 column target."

canonicalReadoutText : String
canonicalReadoutText =
  "Forced-tail weighted-product status: the exact sampled forced-tail witness remains installed for the unweighted Schur test on N=6,8,10,12 as historical evidence. That earlier witness has now been upgraded to a dependency-honest forced-tail closure bridge: the closure readouts are derived from the real proof objects actualKernelBoundedByScaledProxy, forcedTailActualEnvelopeClassBound, and forcedTailN2ScaledArithmetic. The repo still carries the explicit counting/magnitude theorem surface and classwise attack route as the explanatory proof surface, but the local forced-tail weighted-product closure/readout authority now comes from the dependency bridge rather than a documentary literal."

record NSTriadKNForcedTailWeightedProductBoundReceipt : Setω where
  constructor mkNSTriadKNForcedTailWeightedProductBoundReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNForcedTailWeightedProductBoundReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    artifactMarkdown : String
    artifactMarkdownIsCanonical :
      artifactMarkdown ≡ canonicalArtifactMarkdown

    artifactJSON : String
    artifactJSONIsCanonical :
      artifactJSON ≡ canonicalArtifactJSON

    countingMagnitudeSurface : String
    countingMagnitudeSurfaceIsCanonical :
      countingMagnitudeSurface ≡ canonicalCountingMagnitudeSurface

    kernelObject : String
    kernelObjectIsCanonical :
      kernelObject ≡ canonicalKernelObject

    forcedTailTarget : String
    forcedTailTargetIsCanonical :
      forcedTailTarget ≡ canonicalForcedTailTarget

    currentWeightChoice : String
    currentWeightChoiceIsCanonical :
      currentWeightChoice ≡ canonicalCurrentWeightChoice

    witnessRows : String
    witnessRowsIsCanonical :
      witnessRows ≡ canonicalWitnessRows

    scaledWitness : String
    scaledWitnessIsCanonical :
      scaledWitness ≡ canonicalScaledWitness

    fitReadout : String
    fitReadoutIsCanonical :
      fitReadout ≡ canonicalFitReadout

    countingMagnitudeRoute : String
    countingMagnitudeRouteIsCanonical :
      countingMagnitudeRoute ≡ canonicalCountingMagnitudeRoute

    columnAttackRoute : String
    columnAttackRouteIsCanonical :
      columnAttackRoute ≡ canonicalColumnAttackRoute

    columnClassRoute : String
    columnClassRouteIsCanonical :
      columnClassRoute ≡ canonicalColumnClassRoute

    multiplicityCountRoute : String
    multiplicityCountRouteIsCanonical :
      multiplicityCountRoute ≡ canonicalMultiplicityCountRoute

    classFilteredCountRoute : String
    classFilteredCountRouteIsCanonical :
      classFilteredCountRoute ≡ canonicalClassFilteredCountRoute

    classMultiplicityFormulaRoute : String
    classMultiplicityFormulaRouteIsCanonical :
      classMultiplicityFormulaRoute ≡ canonicalClassMultiplicityFormulaRoute

    classEncodingRoute : String
    classEncodingRouteIsCanonical :
      classEncodingRoute ≡ canonicalClassEncodingRoute

    parameterFactorizationRoute : String
    parameterFactorizationRouteIsCanonical :
      parameterFactorizationRoute ≡ canonicalParameterFactorizationRoute

    encodedMultiplicityRoute : String
    encodedMultiplicityRouteIsCanonical :
      encodedMultiplicityRoute ≡ canonicalEncodedMultiplicityRoute

    classMagnitudeFormulaRoute : String
    classMagnitudeFormulaRouteIsCanonical :
      classMagnitudeFormulaRoute ≡ canonicalClassMagnitudeFormulaRoute

    magnitudeEnvelopeRoute : String
    magnitudeEnvelopeRouteIsCanonical :
      magnitudeEnvelopeRoute ≡ canonicalMagnitudeEnvelopeRoute

    envelopeMagnitudeRoute : String
    envelopeMagnitudeRouteIsCanonical :
      envelopeMagnitudeRoute ≡ canonicalEnvelopeMagnitudeRoute

    classFormulaProductRoute : String
    classFormulaProductRouteIsCanonical :
      classFormulaProductRoute ≡ canonicalClassFormulaProductRoute

    classProductN2Route : String
    classProductN2RouteIsCanonical :
      classProductN2Route ≡ canonicalClassProductN2Route

    columnLiftRoute : String
    columnLiftRouteIsCanonical :
      columnLiftRoute ≡ canonicalColumnLiftRoute

    readoutText : String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    sampledForcedTailWitnessInstalled : Bool
    sampledForcedTailWitnessInstalledIsTrue :
      sampledForcedTailWitnessInstalled ≡ true

    unweightedForcedTailSchurWitnessInstalled : Bool
    unweightedForcedTailSchurWitnessInstalledIsTrue :
      unweightedForcedTailSchurWitnessInstalled ≡ true

    forcedTailProductScaleObserved : Bool
    forcedTailProductScaleObservedIsTrue :
      forcedTailProductScaleObserved ≡ true

    forcedTailCountingMagnitudeSurfaceImplemented : Bool
    forcedTailCountingMagnitudeSurfaceImplementedIsTrue :
      forcedTailCountingMagnitudeSurfaceImplemented ≡ true

    forcedTailRowUniformBoundStated : Bool
    forcedTailRowUniformBoundStatedIsTrue :
      forcedTailRowUniformBoundStated ≡ true

    forcedTailRowUniformBoundProved : Bool
    forcedTailRowUniformBoundProvedIsTrue :
      forcedTailRowUniformBoundProved ≡ true

    forcedTailColumnN2BoundStated : Bool
    forcedTailColumnN2BoundStatedIsTrue :
      forcedTailColumnN2BoundStated ≡ true

    forcedTailColumnMultiplicityBoundStated : Bool
    forcedTailColumnMultiplicityBoundStatedIsTrue :
      forcedTailColumnMultiplicityBoundStated ≡ true

    forcedTailColumnMagnitudeBoundStated : Bool
    forcedTailColumnMagnitudeBoundStatedIsTrue :
      forcedTailColumnMagnitudeBoundStated ≡ true

    forcedTailColumnMultiplicityMagnitudeProductStated : Bool
    forcedTailColumnMultiplicityMagnitudeProductStatedIsTrue :
      forcedTailColumnMultiplicityMagnitudeProductStated ≡ true

    forcedTailColumnClassSurfaceImplemented : Bool
    forcedTailColumnClassSurfaceImplementedIsTrue :
      forcedTailColumnClassSurfaceImplemented ≡ true

    forcedTailColumnClassMultiplicityBoundStated : Bool
    forcedTailColumnClassMultiplicityBoundStatedIsTrue :
      forcedTailColumnClassMultiplicityBoundStated ≡ true

    forcedTailColumnClassMagnitudeBoundStated : Bool
    forcedTailColumnClassMagnitudeBoundStatedIsTrue :
      forcedTailColumnClassMagnitudeBoundStated ≡ true

    forcedTailColumnClassProductStated : Bool
    forcedTailColumnClassProductStatedIsTrue :
      forcedTailColumnClassProductStated ≡ true

    forcedTailColumnMultiplicityCountRouteStated : Bool
    forcedTailColumnMultiplicityCountRouteStatedIsTrue :
      forcedTailColumnMultiplicityCountRouteStated ≡ true

    forcedTailClassFilteredCountRouteStated : Bool
    forcedTailClassFilteredCountRouteStatedIsTrue :
      forcedTailClassFilteredCountRouteStated ≡ true

    forcedTailClassMultiplicityFormulaRouteStated : Bool
    forcedTailClassMultiplicityFormulaRouteStatedIsTrue :
      forcedTailClassMultiplicityFormulaRouteStated ≡ true

    forcedTailClassEncodingRouteStated : Bool
    forcedTailClassEncodingRouteStatedIsTrue :
      forcedTailClassEncodingRouteStated ≡ true

    forcedTailParameterFactorizationRouteStated : Bool
    forcedTailParameterFactorizationRouteStatedIsTrue :
      forcedTailParameterFactorizationRouteStated ≡ true

    forcedTailEncodedMultiplicityRouteStated : Bool
    forcedTailEncodedMultiplicityRouteStatedIsTrue :
      forcedTailEncodedMultiplicityRouteStated ≡ true

    forcedTailClassMagnitudeFormulaRouteStated : Bool
    forcedTailClassMagnitudeFormulaRouteStatedIsTrue :
      forcedTailClassMagnitudeFormulaRouteStated ≡ true

    forcedTailMagnitudeEnvelopeRouteStated : Bool
    forcedTailMagnitudeEnvelopeRouteStatedIsTrue :
      forcedTailMagnitudeEnvelopeRouteStated ≡ true

    forcedTailEnvelopeMagnitudeRouteStated : Bool
    forcedTailEnvelopeMagnitudeRouteStatedIsTrue :
      forcedTailEnvelopeMagnitudeRouteStated ≡ true

    forcedTailClassFormulaProductRouteStated : Bool
    forcedTailClassFormulaProductRouteStatedIsTrue :
      forcedTailClassFormulaProductRouteStated ≡ true

    forcedTailClassProductN2RouteStated : Bool
    forcedTailClassProductN2RouteStatedIsTrue :
      forcedTailClassProductN2RouteStated ≡ true

    forcedTailClassToColumnMultiplicityLiftStated : Bool
    forcedTailClassToColumnMultiplicityLiftStatedIsTrue :
      forcedTailClassToColumnMultiplicityLiftStated ≡ true

    forcedTailClassToColumnMagnitudeLiftStated : Bool
    forcedTailClassToColumnMagnitudeLiftStatedIsTrue :
      forcedTailClassToColumnMagnitudeLiftStated ≡ true

    forcedTailClassToColumnProductLiftStated : Bool
    forcedTailClassToColumnProductLiftStatedIsTrue :
      forcedTailClassToColumnProductLiftStated ≡ true

    forcedTailColumnToShellN2LiftStated : Bool
    forcedTailColumnToShellN2LiftStatedIsTrue :
      forcedTailColumnToShellN2LiftStated ≡ true

    forcedTailColumnLiftRouteStated : Bool
    forcedTailColumnLiftRouteStatedIsTrue :
      forcedTailColumnLiftRouteStated ≡ true

    forcedTailColumnN2BoundProved : Bool
    forcedTailColumnN2BoundProvedIsTrue :
      forcedTailColumnN2BoundProved ≡ true

    forcedTailColumnMultiplicityBoundProved : Bool
    forcedTailColumnMultiplicityBoundProvedIsFalse :
      forcedTailColumnMultiplicityBoundProved ≡ false

    forcedTailColumnMagnitudeBoundProved : Bool
    forcedTailColumnMagnitudeBoundProvedIsFalse :
      forcedTailColumnMagnitudeBoundProved ≡ false

    forcedTailColumnMultiplicityMagnitudeProductProved : Bool
    forcedTailColumnMultiplicityMagnitudeProductProvedIsFalse :
      forcedTailColumnMultiplicityMagnitudeProductProved ≡ false

    forcedTailColumnClassMultiplicityBoundProved : Bool
    forcedTailColumnClassMultiplicityBoundProvedIsFalse :
      forcedTailColumnClassMultiplicityBoundProved ≡ false

    forcedTailColumnClassMagnitudeBoundProved : Bool
    forcedTailColumnClassMagnitudeBoundProvedIsFalse :
      forcedTailColumnClassMagnitudeBoundProved ≡ false

    forcedTailColumnClassProductProved : Bool
    forcedTailColumnClassProductProvedIsFalse :
      forcedTailColumnClassProductProved ≡ false

    forcedTailSchurProductDerived : Bool
    forcedTailSchurProductDerivedIsTrue :
      forcedTailSchurProductDerived ≡ true

    forcedTailWeightedProductBoundClosed : Bool
    forcedTailWeightedProductBoundClosedIsTrue :
      forcedTailWeightedProductBoundClosed ≡ true

    profileWiseWeightedProductBoundsClosed : Bool
    profileWiseWeightedProductBoundsClosedIsFalse :
      profileWiseWeightedProductBoundsClosed ≡ false

    weightedSchurProductBoundClosed : Bool
    weightedSchurProductBoundClosedIsFalse :
      weightedSchurProductBoundClosed ≡ false

    theoremPromoted : Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    bkmExclusionProved : Bool
    bkmExclusionProvedIsFalse :
      bkmExclusionProved ≡ false

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNForcedTailWeightedProductBoundReceipt public

canonicalNSTriadKNForcedTailWeightedProductBoundReceipt :
  NSTriadKNForcedTailWeightedProductBoundReceipt
canonicalNSTriadKNForcedTailWeightedProductBoundReceipt =
  mkNSTriadKNForcedTailWeightedProductBoundReceipt
    "NSTriadKNForcedTailWeightedProductBoundReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalArtifactMarkdown
    refl
    canonicalArtifactJSON
    refl
    canonicalCountingMagnitudeSurface
    refl
    canonicalKernelObject
    refl
    canonicalForcedTailTarget
    refl
    canonicalCurrentWeightChoice
    refl
    canonicalWitnessRows
    refl
    canonicalScaledWitness
    refl
    canonicalFitReadout
    refl
    canonicalCountingMagnitudeRoute
    refl
    canonicalColumnAttackRoute
    refl
    canonicalColumnClassRoute
    refl
    canonicalMultiplicityCountRoute
    refl
    canonicalClassFilteredCountRoute
    refl
    canonicalClassMultiplicityFormulaRoute
    refl
    canonicalClassEncodingRoute
    refl
    canonicalParameterFactorizationRoute
    refl
    canonicalEncodedMultiplicityRoute
    refl
    canonicalClassMagnitudeFormulaRoute
    refl
    canonicalMagnitudeEnvelopeRoute
    refl
    canonicalEnvelopeMagnitudeRoute
    refl
    canonicalClassFormulaProductRoute
    refl
    canonicalClassProductN2Route
    refl
    canonicalColumnLiftRoute
    refl
    canonicalReadoutText
    refl
    Dependency.forcedTailColumnN2BoundProved
    Dependency.forcedTailColumnN2BoundProvedIsTrue
    Dependency.forcedTailSchurProductDerived
    Dependency.forcedTailSchurProductDerivedIsTrue
    Dependency.forcedTailWeightedProductBoundClosed
    Dependency.forcedTailWeightedProductBoundClosedIsTrue
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
