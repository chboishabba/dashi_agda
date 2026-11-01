module DASHI.Law.ReaderVisualisationPickParityRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.ReaderVisualisationPickParityExact as Pick

boundary : Pick.ReaderVisualisationPickBoundary
boundary = Pick.canonicalReaderVisualisationPickBoundary

readerOwnsTransport :
  Pick.visualisationTransportOwnedByReaderAbi boundary ≡ true
readerOwnsTransport =
  Pick.visualisationTransportOwnedByReaderAbiIsTrue boundary

picksShareIntent :
  Pick.dioxusAndGpuPickMayCompileToSameReaderIntent boundary ≡ true
picksShareIntent =
  Pick.dioxusAndGpuPickMayCompileToSameReaderIntentIsTrue boundary

pickCreatesNoPayment :
  Pick.pickCreatesEvidencePayment boundary ≡ false
pickCreatesNoPayment =
  Pick.pickCreatesEvidencePaymentIsFalse boundary

pickCreatesNoAuthority :
  Pick.pickCreatesSemanticAuthority boundary ≡ false
pickCreatesNoAuthority =
  Pick.pickCreatesSemanticAuthorityIsFalse boundary

layoutDoesNotReconstructSemantics :
  Pick.rendererMayReconstructLegalSemanticsFromLayout boundary ≡ false
layoutDoesNotReconstructSemantics =
  Pick.rendererMayReconstructLegalSemanticsFromLayoutIsFalse boundary
