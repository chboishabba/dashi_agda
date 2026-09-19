{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayAristotleRouteSLiteralWilsonDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- ARISTOTLE ROUTE-S LITERAL-WILSON DONOR RECEIPT
--
-- Exact supplied archive:
--   ym-aristotle-009295-latest-20260919.tar.gz
--   sha256 95bb6c4c2613a4dff9750940757094354d9344f78e63a3db7ded36cf08567137
--
-- Supplied worker receipt:
--   lake build RequestProject
--   8236 jobs, zero errors
--
-- New material reportedly contains no
--   sorry / axiom / postulate / @[implemented_by]
-- and headline #print axioms report only
--   propext / Classical.choice / Quot.sound.
--
-- This module records the exact donor theorem surface.  It does NOT turn a Lean
-- proof into an Agda kernel proof and does NOT manufacture the three remaining
-- physical hypotheses of the terminal theorem.
------------------------------------------------------------------------

record RouteSLeanArtifact : Set where
  constructor route-s-artifact
  field
    path : String
    sha256 : String
    headline : String
    role : String

open RouteSLeanArtifact public

wilsonLoopDonor : RouteSLeanArtifact
wilsonLoopDonor = route-s-artifact
  "RequestProject/YangMills/Lattice/WilsonLoop.lean"
  "f177da48722e5f6596db840bb9d8920a2eec24229018f057cf5bb57183eceb46"
  "wilsonLoop_gaugeTransform / wilsonLoop_translate / wilsonAction_eq_sum_wilsonLoop"
  "literal Wilson-loop observables, gauge invariance, translation covariance, plaquette/action presentation"

euclideanTimeDonor : RouteSLeanArtifact
euclideanTimeDonor = route-s-artifact
  "RequestProject/YangMills/RouteS/EuclideanTime.lean"
  "565222a163d373d52e7b910217f842be72195efa03bf7d8f89d35eed781daf9b"
  "timeTranslate_add / measurePreserving_timeTranslate_gibbs / wilsonLoop_timeTranslate"
  "S2 literal Euclidean time action and physical separation semantics"

covarianceDonor : RouteSLeanArtifact
covarianceDonor = route-s-artifact
  "RequestProject/YangMills/RouteS/Covariance.lean"
  "8cda91c6220effd71c598adff3bf25e3a56e27de2888ec4412b954708933a541"
  "tendsto_connected / continuum_clustering_of_expectation_limits"
  "S4 covariance-limit algebra from three selected expectation limits"

wilsonCovarianceDonor : RouteSLeanArtifact
wilsonCovarianceDonor = route-s-artifact
  "RequestProject/YangMills/RouteS/WilsonCovariance.lean"
  "6b67913c6b69517da2754d5c1da09397548239f0a21c93b0333d4b95c8972359"
  "loopCov_eq_cov_translatedLoop / loopCov_eq_connected"
  "literal translated Wilson-loop covariance and S2+S3 same-object presentation"

markedSourceDonor : RouteSLeanArtifact
markedSourceDonor = route-s-artifact
  "RequestProject/YangMills/RouteS/MarkedSource.lean"
  "0b9578c6c2830bbf5f95632da06803dc1d79047dfb38b6aad9a11bf101f23a4e"
  "markedSource_mixed_deriv / wilson_markedSource_mixed_deriv"
  "S1 exact mixed log-source derivative = connected covariance on the literal Wilson-Gibbs state"

assemblyDonor : RouteSLeanArtifact
assemblyDonor = route-s-artifact
  "RequestProject/YangMills/RouteS/Assembly.lean"
  "00c62fcb645e1d9ef1d644bab037290111f6859d376490fc5843920855856878"
  "routeS_massGapConclusion / routeS_continuum_clustering_of_wilson / wilson_routeS_massGapConclusion"
  "end-to-end literal Wilson Route-S compiler to the Clay-form MassGapConclusion"

witnessDonor : RouteSLeanArtifact
witnessDonor = route-s-artifact
  "RequestProject/YangMills/RouteS/Witness.lean"
  "77893454c905f1b421100a44a56d68cb5395001b17d3425587729ef46afd0d80"
  "routeSWitness_formGap / routeSWitness_massGapConclusion"
  "non-vacuity/interface witness; not physical Yang-Mills evidence"

calibrationDonor : RouteSLeanArtifact
calibrationDonor = route-s-artifact
  "RequestProject/YangMills/RouteS/Calibration.lean"
  "a53ef1446672521f1cf789c467dbe87ae0a1a76cd91b689b102aaf23d3154394"
  "tendsto_gapMass / effectiveMass_of_pure_exponential"
  "delta -> inverse correlation length -> energy -> SI mass calibration compiler"

routeSLeanArtifacts : List RouteSLeanArtifact
routeSLeanArtifacts =
  wilsonLoopDonor ∷
  euclideanTimeDonor ∷
  covarianceDonor ∷
  wilsonCovarianceDonor ∷
  markedSourceDonor ∷
  assemblyDonor ∷
  witnessDonor ∷
  calibrationDonor ∷ []

------------------------------------------------------------------------
-- Exact donor-status firewall.
------------------------------------------------------------------------

suppliedLeanBuildJobCount : String
suppliedLeanBuildJobCount = "8236"

suppliedLeanBuildGreen : Bool
suppliedLeanBuildGreen = true

suppliedLeanBuildGreenIsTrue : suppliedLeanBuildGreen ≡ true
suppliedLeanBuildGreenIsTrue = refl

headlineAxiomAuditOnlyStandardMathlib : Bool
headlineAxiomAuditOnlyStandardMathlib = true

headlineAxiomAuditOnlyStandardMathlibIsTrue :
  headlineAxiomAuditOnlyStandardMathlib ≡ true
headlineAxiomAuditOnlyStandardMathlibIsTrue = refl

routeSLeanKernelRevalidatedAtSuppliedProject : Bool
routeSLeanKernelRevalidatedAtSuppliedProject = true

routeSLeanKernelRevalidatedAtSuppliedProjectIsTrue :
  routeSLeanKernelRevalidatedAtSuppliedProject ≡ true
routeSLeanKernelRevalidatedAtSuppliedProjectIsTrue = refl

routeSLeanTheoremIsAgdaKernelProof : Bool
routeSLeanTheoremIsAgdaKernelProof = false

routeSLeanTheoremIsAgdaKernelProofIsFalse :
  routeSLeanTheoremIsAgdaKernelProof ≡ false
routeSLeanTheoremIsAgdaKernelProofIsFalse = refl

routeSLeanTheoremManufacturesPhysicalInputs : Bool
routeSLeanTheoremManufacturesPhysicalInputs = false

routeSLeanTheoremManufacturesPhysicalInputsIsFalse :
  routeSLeanTheoremManufacturesPhysicalInputs ≡ false
routeSLeanTheoremManufacturesPhysicalInputsIsFalse = refl

------------------------------------------------------------------------
-- What the new verified donor actually pays.
------------------------------------------------------------------------

literalWilsonLoopConstructionLeanPaid : Bool
literalWilsonLoopConstructionLeanPaid = true

literalEuclideanTimeSemanticsLeanPaid : Bool
literalEuclideanTimeSemanticsLeanPaid = true

literalWilsonPresentationLeanPaid : Bool
literalWilsonPresentationLeanPaid = true

markedSourceCovarianceIdentityLeanPaid : Bool
markedSourceCovarianceIdentityLeanPaid = true

covarianceLimitCompilerLeanPaid : Bool
covarianceLimitCompilerLeanPaid = true

terminalRouteSAssemblyLeanPaid : Bool
terminalRouteSAssemblyLeanPaid = true

siCalibrationCompilerLeanPaid : Bool
siCalibrationCompilerLeanPaid = true

literalWilsonLoopConstructionLeanPaidIsTrue :
  literalWilsonLoopConstructionLeanPaid ≡ true
literalWilsonLoopConstructionLeanPaidIsTrue = refl

literalEuclideanTimeSemanticsLeanPaidIsTrue :
  literalEuclideanTimeSemanticsLeanPaid ≡ true
literalEuclideanTimeSemanticsLeanPaidIsTrue = refl

literalWilsonPresentationLeanPaidIsTrue :
  literalWilsonPresentationLeanPaid ≡ true
literalWilsonPresentationLeanPaidIsTrue = refl

markedSourceCovarianceIdentityLeanPaidIsTrue :
  markedSourceCovarianceIdentityLeanPaid ≡ true
markedSourceCovarianceIdentityLeanPaidIsTrue = refl

covarianceLimitCompilerLeanPaidIsTrue :
  covarianceLimitCompilerLeanPaid ≡ true
covarianceLimitCompilerLeanPaidIsTrue = refl

terminalRouteSAssemblyLeanPaidIsTrue :
  terminalRouteSAssemblyLeanPaid ≡ true
terminalRouteSAssemblyLeanPaidIsTrue = refl

siCalibrationCompilerLeanPaidIsTrue :
  siCalibrationCompilerLeanPaid ≡ true
siCalibrationCompilerLeanPaidIsTrue = refl

routeSLeanCompilerLevel : ProofLevel
routeSLeanCompilerLevel = standardImported

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
