{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayClosedWorldResidualAudit20260917Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CLOSED-WORLD RESIDUAL AUDIT — 2026-09-17
--
-- This is not a proof substitute and not theorem authority.  It records the
-- exact theorem-bearing cuts found after searching current master, merged
-- #967/#970/#987, PR #996, the accessible dashi_lean4 branches, and the late
-- R318/R320/R322/R327/R338/R339/R342/R346/R397/R401 source-native chain.
-- Its Bool/status fields classify that repository search only; they cannot prove
-- nonexistence outside the searched state.
--
-- 2026-09-17 third recut: R318's
--
--   PublishedTwoJLocalizationForBase + SelectedBaseJApplicability
--
-- remains a valid GENERAL external-presentation adapter, but it is not the
-- least-privilege proof-search cut.  R338 already places the source theorem on
-- the canonical common CMP116 domain/rational order, while R339 isolates the
-- selected-T5 magnitude same-object and envelope calibration.  The new
-- `YMClayF1CanonicalSourceApplicationExact` composes R338 + R339 through R320
-- into R295.  Nothing in that compiler manufactures either missing inhabitant.
------------------------------------------------------------------------

data ResidualClass : Set where
  sourceTheoremInhabitant : ResidualClass
  sameObjectAttachment : ResidualClass
  physicalOperatorLimit : ResidualClass
  sameEvolutionWeld : ResidualClass

data ResidualStatus : Set where
  unpaid : ResidualStatus
  compilerOwned : ResidualStatus

record ExactResidual : Set where
  constructor exact-residual
  field
    residualClass : ResidualClass
    owner : String
    fieldOrTheorem : String
    status : ResidualStatus
    evidence : String

open ExactResidual public

------------------------------------------------------------------------
-- F1: current canonical source-native primitive cut.
------------------------------------------------------------------------

f1CanonicalCMP116SourceAlignment : ExactResidual
f1CanonicalCMP116SourceAlignment = exact-residual
  sourceTheoremInhabitant
  "DASHI/Physics/YangMills/BalabanCMP116CanonicalCommonDomainSourceRound338Exact.agda"
  "CanonicalCommonDomainCMP116Source / differentiatedLocalizationOnCanonicalCommonDomain"
  unpaid
  "R338 is the least-privilege source ABI after canonical common-domain and rational-order normalization. Exact code search finds the record definition and downstream consumers of differentiatedLocalizationOnCanonicalCommonDomain, but no concrete constructor of CanonicalCommonDomainCMP116Source on the selected physical base. CMP116 Sect. 1, DOI 10.1007/BF01239022 supplies external theorem authority; citation/status metadata does not construct the Agda inhabitant or perform the local source-carrier alignment."

f1CanonicalSelectedT5Application : ExactResidual
f1CanonicalSelectedT5Application = exact-residual
  sameObjectAttachment
  "DASHI/Physics/YangMills/BalabanCMP116CanonicalSelectedT5ApplicationRound339Exact.agda"
  "CanonicalSelectedT5CMP116Application: sourceMagnitudeIsSelectedMagnitude + sourceEnvelopeBelowSelectedRootedShell"
  unpaid
  "R339 removes independent pair-domain and abstract-order payments. The selected physical application is exactly two coordinates: the CMP116 differentiated response is the literal selected mixed-log response, and the CMP116 source envelope is bounded by the selected rooted shell. Exact search finds these fields and compiler consumers but no concrete application inhabitant on the searched tree."

f1CanonicalR338R339Compiler : ExactResidual
f1CanonicalR338R339Compiler = exact-residual
  sameObjectAttachment
  "DASHI/Physics/YangMills/YMClayF1CanonicalSourceApplicationExact.agda"
  "canonicalSourceApplicationLocalizesBaseAsR295"
  compilerOwned
  "PR #996 now composes R339.canonicalApplicationBuildsR320Payment with R320.localizeBaseDirectlyAsR295. Once R338 source alignment and R339 selected-T5 application are supplied, the exact localized R295 carrier is compiler output. Do not reopen the older R318 magnitude/root/distance presentation as three independent frontier leaves."

f1R409StageAttachment : ExactResidual
f1R409StageAttachment = exact-residual
  sameObjectAttachment
  "DASHI/Physics/YangMills/BalabanCMP99SingleMarkedFourStageRound409Exact.agda"
  "SingleChangedFourStageAgreement"
  unpaid
  "R409 compiles one marked stage plus three exact unchanged-stage equalities to the whole product bound. Exact search finds no external inhabitant selecting the actual CMP99 stage and proving the other three equalities. This is optional lower-level source replay after the canonical R338/R339 recut."

f1R406ScalarizationAttachment : ExactResidual
f1R406ScalarizationAttachment = exact-residual
  sameObjectAttachment
  "DASHI/Physics/YangMills/BalabanCMP116SelectedTermwiseLocalizationRound406Exact.agda"
  "differentiatedTermAbsoluteIsOperatorDifferenceNorm"
  unpaid
  "Exact search finds this equality only as a record field/consumer; no concrete selected source replay inhabits it on the searched current tree. This is optional lower-level source replay after the canonical R338/R339 recut."

f1R387DownstreamCompiler : ExactResidual
f1R387DownstreamCompiler = exact-residual
  sameObjectAttachment
  "DASHI/Physics/YangMills/BalabanDirectSelectedUpperToGapFinalExact.agda"
  "directSelectedUpperBuildsPositiveTransferGapCore"
  compilerOwned
  "Merged #987 already compiles a genuine R387 direct selected spectral upper plus one-sided limit closure and positive selected candidate gap into PositiveTransferGapCore. Do not rebuild this layer."

------------------------------------------------------------------------
-- F3 / F4 unchanged by the F1 source recut.
------------------------------------------------------------------------

f3VacuumRecoverySystem : ExactResidual
f3VacuumRecoverySystem = exact-residual
  physicalOperatorLimit
  "DASHI/Physics/YangMills/BalabanVacuumOrthogonalMoscoRecoveryExact.agda"
  "VacuumOrthogonalRecoverySystem"
  unpaid
  "The typed recovery system exists and its gap compiler is machine-checked. Sprint129 evidence/status booleans do not construct this record, and exact search finds no physical literal-Wilson inhabitant on the searched current tree."

f3LiteralMeasureLimit : ExactResidual
f3LiteralMeasureLimit = exact-residual
  physicalOperatorLimit
  "DASHI/Physics/YangMills/BalabanLiteralSchwingerStressRecoveryRound126Exact.agda"
  "literalFiniteMeasuresConverge"
  unpaid
  "Round126 stores the literal finite-measure continuum theorem as a physical field. Round129 exports it from a supplied recovery object but does not construct the field. Measure convergence also does not by itself supply Hamiltonian graph convergence."

f3EmbeddedGraphLimit : ExactResidual
f3EmbeddedGraphLimit = exact-residual
  physicalOperatorLimit
  "RequestProject/YangMills/Lattice/ContinuumWeld.lean"
  "embedded literal-Wilson vacuum-sector graph limit input"
  unpaid
  "Aristotle's 8220-job donor pays the varying-carrier compiler, not the physical graph-limit inhabitant. No accessible dashi_lean4 branch contains the new donor files or an additional physical instantiation branch."

f4CommonCoreActionEquality : ExactResidual
f4CommonCoreActionEquality = exact-residual
  sameEvolutionWeld
  "DASHI/Physics/YangMills/YangMillsStressWardCommonCoreGeneratorExact.agda"
  "commonCoreActionEquality"
  unpaid
  "The common-core generator equality compiler is present, but exact search finds no concrete physical constructor of its common-core action equality on the searched current tree."

f4EvolutionEquality : ExactResidual
f4EvolutionEquality = exact-residual
  sameEvolutionWeld
  "DASHI/Physics/YangMills/YMClayOutstandingPhysicalFrontierExact.agda"
  "YMOSSameObjectWitness.evolutionsEqual"
  unpaid
  "Exact search for evolutionsEqual/sameEvolution on the searched current tree finds no physical inhabitant. Round127's Schwinger-family weld is a different same-object obligation and does not imply equality of the reconstructed one-parameter evolutions."

------------------------------------------------------------------------
-- Search / frontier status.
------------------------------------------------------------------------

oldF2IndependentResearchPayment : Bool
oldF2IndependentResearchPayment = false

oldF2IndependentResearchPaymentIsFalse :
  oldF2IndependentResearchPayment ≡ false
oldF2IndependentResearchPaymentIsFalse = refl

r318ExternalPresentationPairIsPrimitiveF1Cut : Bool
r318ExternalPresentationPairIsPrimitiveF1Cut = false

r318ExternalPresentationPairIsPrimitiveF1CutIsFalse :
  r318ExternalPresentationPairIsPrimitiveF1Cut ≡ false
r318ExternalPresentationPairIsPrimitiveF1CutIsFalse = refl

canonicalR338R339CompilerObserved : Bool
canonicalR338R339CompilerObserved = true

canonicalR338R339CompilerObservedIsTrue :
  canonicalR338R339CompilerObserved ≡ true
canonicalR338R339CompilerObservedIsTrue = refl

f1PhysicalInhabitantObservedInClosedWorldSearch : Bool
f1PhysicalInhabitantObservedInClosedWorldSearch = false

f1PhysicalInhabitantObservedInClosedWorldSearchIsFalse :
  f1PhysicalInhabitantObservedInClosedWorldSearch ≡ false
f1PhysicalInhabitantObservedInClosedWorldSearchIsFalse = refl

f3PhysicalInhabitantObservedInClosedWorldSearch : Bool
f3PhysicalInhabitantObservedInClosedWorldSearch = false

f3PhysicalInhabitantObservedInClosedWorldSearchIsFalse :
  f3PhysicalInhabitantObservedInClosedWorldSearch ≡ false
f3PhysicalInhabitantObservedInClosedWorldSearchIsFalse = refl

f4PhysicalInhabitantObservedInClosedWorldSearch : Bool
f4PhysicalInhabitantObservedInClosedWorldSearch = false

f4PhysicalInhabitantObservedInClosedWorldSearchIsFalse :
  f4PhysicalInhabitantObservedInClosedWorldSearch ≡ false
f4PhysicalInhabitantObservedInClosedWorldSearchIsFalse = refl

unconditionalClayTheoremSupportedBySearchedRepositoryState : Bool
unconditionalClayTheoremSupportedBySearchedRepositoryState = false

unconditionalClayTheoremSupportedBySearchedRepositoryStateIsFalse :
  unconditionalClayTheoremSupportedBySearchedRepositoryState ≡ false
unconditionalClayTheoremSupportedBySearchedRepositoryStateIsFalse = refl

data ClosedWorldResidualAuditPresent : Set where
  closedWorldResidualAuditPresent : ClosedWorldResidualAuditPresent

closedWorldResidualAuditWitness : ClosedWorldResidualAuditPresent
closedWorldResidualAuditWitness = closedWorldResidualAuditPresent