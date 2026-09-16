module DASHI.Physics.Closure.NSTriadKNLowRemoteSpectralDatumRound98Regression where

------------------------------------------------------------------------
-- RED regression for strict B-phase S2b2c2b.
--
-- This regression requires the literal low/remote R98 spectral datum to be
-- constructed from the already-owned live norm-scale and packet folds.  The
-- production owner is intentionally absent in the RED commit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNLowRemoteSpectralDatumRound98Exact as Datum

literalLowRemoteSpectralDatumConstructedIsTrue :
  Datum.literalLowRemoteSpectralDatumConstructed ≡ true
literalLowRemoteSpectralDatumConstructedIsTrue =
  Datum.literalLowRemoteSpectralDatumConstructedIsTrue

twoNuNormalizationFirewallClosedIsTrue :
  Datum.twoNuNormalizationFirewallClosed ≡ true
twoNuNormalizationFirewallClosedIsTrue =
  Datum.twoNuNormalizationFirewallClosedIsTrue

remoteSpectralCrossCoercivityConstructedIsTrue :
  Datum.remoteSpectralCrossCoercivityConstructed ≡ true
remoteSpectralCrossCoercivityConstructedIsTrue =
  Datum.remoteSpectralCrossCoercivityConstructedIsTrue

collarRemainsIndependentIsTrue :
  Datum.collarRemainsIndependent ≡ true
collarRemainsIndependentIsTrue =
  Datum.collarRemainsIndependentIsTrue
