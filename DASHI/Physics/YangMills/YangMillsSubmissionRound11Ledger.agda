module DASHI.Physics.YangMills.YangMillsSubmissionRound11Ledger where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.YangMillsSubmissionRound11Receipt as Receipt
open import DASHI.Physics.YangMills.CompactLieProofLevel

configuredIdentificationReducerClaim : NamedClaim
configuredIdentificationReducerClaim = namedClaim
  "Round 11: exact configured sine/cosine definitions imply the concrete Bishop term identification"
  (Receipt.configuredTermIdentificationReducedToDefinitions
    Receipt.round11Receipt ≡ true)
  machineChecked
  (checkedEvidence Receipt.round11TermIdentificationReducerClosed)

fullHalfBallChartReducerClaim : NamedClaim
fullHalfBallChartReducerClaim = namedClaim
  "Round 11: direct and reflected half-ball charts transport sine oddly, cosine evenly and retain representative interlacing"
  (Receipt.orientedFullHalfBallChartReducerDischarged
    Receipt.round11Receipt ≡ true)
  machineChecked
  (checkedEvidence Receipt.round11FullHalfBallChartReducerClosed)

constructiveSignSelectionOpenClaim : NamedClaim
constructiveSignSelectionOpenClaim = namedClaim
  "Round 11: selecting an oriented chart for an arbitrary Bishop real remains an explicit constructive input"
  (Receipt.constructiveSignChartSelectionDischarged
    Receipt.round11Receipt ≡ false)
  machineChecked
  (checkedEvidence Receipt.round11SignChartSelectionRemainsOpen)

directRatioTailReducerClaim : NamedClaim
directRatioTailReducerClaim = namedClaim
  "Round 11: tail seed plus direct successor absorption gives all-index polynomial domination"
  (Receipt.directRatioTailInductionDischarged
    Receipt.round11Receipt ≡ true)
  machineChecked
  (checkedEvidence Receipt.round11DirectRatioInductionClosed)

logBackendRemovalClaim : NamedClaim
logBackendRemovalClaim = namedClaim
  "Round 11: polynomial absorption does not logically require a constructive logarithm backend"
  (Receipt.logarithmBackendRequiredForPolynomialAbsorption
    Receipt.round11Receipt ≡ false)
  machineChecked
  (checkedEvidence
    Receipt.round11PolynomialAbsorptionDoesNotRequireLogBackend)

periodicDegreeEightClaim : NamedClaim
periodicDegreeEightClaim = namedClaim
  "Round 11: the periodic support carrier owns its graph, root and degree-eight bound"
  (Receipt.periodicGraphRootAndDegreeEightDischarged
    Receipt.round11Receipt ≡ true)
  machineChecked
  (checkedEvidence Receipt.round11PeriodicDegreeEightClosed)

diameterNoGoClaim : NamedClaim
diameterNoGoClaim = namedClaim
  "Round 11: bounded degree alone cannot justify affine complexity in diameter for a superlinear polymer family"
  (Receipt.unrestrictedLinearDiameterInferenceRejected
    Receipt.round11Receipt ≡ true)
  machineChecked
  (checkedEvidence Receipt.round11UnrestrictedDiameterInferenceRejected)

p11CanonicalConstantClaim : NamedClaim
p11CanonicalConstantClaim = namedClaim
  "Round 11: the lightweight P11 lane consumes the canonical P06 skeleton-decoration-fibre animal constant"
  (Receipt.lightweightP11CanonicalConstantWired
    Receipt.round11Receipt ≡ true)
  machineChecked
  (checkedEvidence Receipt.round11P11CanonicalConstantWired)

physicalEndpointOpenClaim : NamedClaim
physicalEndpointOpenClaim = namedClaim
  "Round 11: the continuum Osterwalder-Schrader and positive SI mass-gap endpoint remains open"
  (Receipt.continuumOSAndSIMassGapDischarged
    Receipt.round11Receipt ≡ false)
  machineChecked
  (checkedEvidence Receipt.round11PhysicalEndpointRemainsOpen)
