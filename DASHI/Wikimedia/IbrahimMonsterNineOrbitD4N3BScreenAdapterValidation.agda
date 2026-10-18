module DASHI.Wikimedia.IbrahimMonsterNineOrbitD4N3BScreenAdapterValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Wikimedia.IbrahimMonsterNineOrbitD4N3BScreenAdapterExact as A

nineOrbitScreenRoundTripRegression :
  (o : Triadic.NineOrbit) → A.screenPointToNineOrbit (A.nineOrbitToScreenPoint o) ≡ o
nineOrbitScreenRoundTripRegression = A.nineOrbitScreenRoundTrip

screenNineOrbitRoundTripRegression :
  (p : A.ScreenPoint5) → A.nineOrbitToScreenPoint (A.screenPointToNineOrbit p) ≡ p
screenNineOrbitRoundTripRegression = A.screenNineOrbitRoundTrip

quarterTurnEquivarianceRegression :
  (o : Triadic.NineOrbit) →
  A.nineOrbitToScreenPoint (A.kernelQuarterTurn o) ≡ A.screenQuarterTurn (A.nineOrbitToScreenPoint o)
quarterTurnEquivarianceRegression = A.quarterTurnEquivariance

axisReflectionEquivarianceRegression :
  (o : Triadic.NineOrbit) →
  A.nineOrbitToScreenPoint (A.kernelAxisReflection o) ≡ A.screenAxisReflection (A.nineOrbitToScreenPoint o)
axisReflectionEquivarianceRegression = A.axisReflectionEquivariance

adapterPaidRegression :
  A.nineOrbitToMergedScreenAdapterPaid A.currentNineOrbitScreenAdapterBoundary ≡ true
adapterPaidRegression = A.nineOrbitToMergedScreenAdapterPaidIsTrue

runtimeFirewallRegression :
  A.gapRuntimeVerdictImported A.currentNineOrbitScreenAdapterBoundary ≡ false
runtimeFirewallRegression = A.gapRuntimeVerdictImportedIsFalse

monsterActionFirewallRegression :
  A.adapterCreatesSelectedMonsterAction A.currentNineOrbitScreenAdapterBoundary ≡ false
monsterActionFirewallRegression = A.adapterCreatesSelectedMonsterActionIsFalse
