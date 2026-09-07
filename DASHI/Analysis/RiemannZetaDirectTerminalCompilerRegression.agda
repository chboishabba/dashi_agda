module DASHI.Analysis.RiemannZetaDirectTerminalCompilerRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Analysis.RiemannZetaDirectTerminalCompilerExact as T

private
  boundary = T.canonicalDirectTerminalCompilerBoundary

analyticCoreRoutePreferred :
  T.DirectTerminalCompilerBoundary.analyticCoreRoutePreferredOverDeterminantPackaging boundary ≡ true
analyticCoreRoutePreferred = refl

lowCoverageNotManufactured :
  T.DirectTerminalCompilerBoundary.prizeFacingCompilerManufacturesLowCoverage boundary ≡ false
lowCoverageNotManufactured = refl

packetInhabitanceNotClaimed :
  T.DirectTerminalCompilerBoundary.packetInhabitanceClaimedHere boundary ≡ false
packetInhabitanceNotClaimed = refl

rhNotDerivedWithoutPacket :
  T.DirectTerminalCompilerBoundary.rhDerivedWithoutPacket boundary ≡ false
rhNotDerivedWithoutPacket = refl
