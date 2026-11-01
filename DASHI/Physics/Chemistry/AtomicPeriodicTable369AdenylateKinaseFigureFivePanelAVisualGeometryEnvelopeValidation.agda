module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFivePanelAVisualGeometryEnvelopeValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFivePanelAVisualGeometryEnvelopeExact as Owner

-- Validation root: Figure-5a may narrow named-state theta1/theta2 geometry only
-- to explicit visual envelopes.  It must not silently convert plotted locations
-- into exact printed coordinate cells, and dLN remains outside panel-a.

boundary : Owner.AdKFigureFivePanelAVisualGeometryEnvelopeBoundary
boundary = Owner.canonicalAdKFigureFivePanelAVisualGeometryEnvelopeBoundary

alphaEnvelope : Owner.NamedStateVisualEnvelope
alphaEnvelope = Owner.alphaEnvelope

betaEnvelope : Owner.NamedStateVisualEnvelope
betaEnvelope = Owner.betaEnvelope

gammaEnvelope : Owner.NamedStateVisualEnvelope
gammaEnvelope = Owner.gammaEnvelope

deltaEnvelope : Owner.NamedStateVisualEnvelope
deltaEnvelope = Owner.deltaEnvelope

epsilonEnvelope : Owner.NamedStateVisualEnvelope
epsilonEnvelope = Owner.epsilonEnvelope

etaEnvelope : Owner.NamedStateVisualEnvelope
etaEnvelope = Owner.etaEnvelope

zetaEnvelope : Owner.NamedStateVisualEnvelope
zetaEnvelope = Owner.zetaEnvelope

lambdaEnvelope : Owner.NamedStateVisualEnvelope
lambdaEnvelope = Owner.lambdaEnvelope

visualEnvelopeNarrowsButDoesNotPayExactPoint : Bool
visualEnvelopeNarrowsButDoesNotPayExactPoint =
  Owner.visualEnvelopeNarrowsButDoesNotPayExactPoint

figureFivePanelADoesNotPayDLn : Bool
figureFivePanelADoesNotPayDLn = Owner.figureFivePanelADoesNotPayDLn

sameObservableDefinitionRetained : Bool
sameObservableDefinitionRetained = Owner.sameObservableDefinitionRetained

attributionEnvelopeRetained : Bool
attributionEnvelopeRetained = Owner.attributionEnvelopeRetained
