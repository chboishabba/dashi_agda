module DASHI.Core.ResidualSymmetryCollisionFibreRegression where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Residual
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.TernaryNativeMinimalityExact as Native

------------------------------------------------------------------------
-- Exact C2 action on the native signed-centre trit.
------------------------------------------------------------------------

data C2 : Set where
  c2Identity c2Flip : C2

c2Combine : C2 → C2 → C2
c2Combine c2Identity h = h
c2Combine c2Flip c2Identity = c2Flip
c2Combine c2Flip c2Flip = c2Identity

c2Inverse : C2 → C2
c2Inverse c2Identity = c2Identity
c2Inverse c2Flip = c2Flip

c2Act : C2 → SSP.SSPTrit → SSP.SSPTrit
c2Act c2Identity x = x
c2Act c2Flip x = Orbit.strictAntipode x

c2IdentityActs : (x : SSP.SSPTrit) → c2Act c2Identity x ≡ x
c2IdentityActs x = refl

c2CombineActs :
  (g h : C2) (x : SSP.SSPTrit) →
  c2Act (c2Combine g h) x ≡ c2Act g (c2Act h x)
c2CombineActs c2Identity h x = refl
c2CombineActs c2Flip c2Identity x = refl
c2CombineActs c2Flip c2Flip x = sym (Orbit.strictAntipodeInvolutive x)

c2InverseLeftActs :
  (g : C2) (x : SSP.SSPTrit) →
  c2Act (c2Inverse g) (c2Act g x) ≡ x
c2InverseLeftActs c2Identity x = refl
c2InverseLeftActs c2Flip x = Orbit.strictAntipodeInvolutive x

c2InverseRightActs :
  (g : C2) (x : SSP.SSPTrit) →
  c2Act g (c2Act (c2Inverse g) x) ≡ x
c2InverseRightActs c2Identity x = refl
c2InverseRightActs c2Flip x = Orbit.strictAntipodeInvolutive x

ternaryC2Action : Residual.InvertibleSymmetryAction SSP.SSPTrit C2
ternaryC2Action =
  Residual.invertibleSymmetryAction
    c2Identity c2Combine c2Inverse c2Act
    c2IdentityActs c2CombineActs c2InverseLeftActs c2InverseRightActs

data PoleClass : Set where
  centreClass signedClass : PoleClass

poleClass : SSP.SSPTrit → PoleClass
poleClass SSP.sspNegOne = signedClass
poleClass SSP.sspZero = centreClass
poleClass SSP.sspPosOne = signedClass

poleClassInvariant :
  (g : C2) (x : SSP.SSPTrit) →
  poleClass (c2Act g x) ≡ poleClass x
poleClassInvariant c2Identity x = refl
poleClassInvariant c2Flip SSP.sspNegOne = refl
poleClassInvariant c2Flip SSP.sspZero = refl
poleClassInvariant c2Flip SSP.sspPosOne = refl

ternaryC2PreservesPoleClass :
  Residual.ObserverPreservingSymmetry ternaryC2Action poleClass
ternaryC2PreservesPoleClass =
  Residual.observerPreservingSymmetry poleClassInvariant

negativeAndPositiveShareCoarsePole :
  poleClass SSP.sspNegOne ≡ poleClass SSP.sspPosOne
negativeAndPositiveShareCoarsePole = refl

signSectorWitness :
  Residual.ResidualSectorWitness poleClass (λ x → x)
signSectorWitness =
  Residual.residualSectorWitness
    SSP.sspNegOne SSP.sspPosOne
    negativeAndPositiveShareCoarsePole
    Native.negativeNotPositive

signRefinesAntipodalPoleClass :
  Observer.StrictRefinement
    poleClass
    (Observer.pairObserver poleClass (λ x → x))
signRefinesAntipodalPoleClass =
  Residual.sectorPairStrictlyRefinesCoarse
    poleClass (λ x → x) signSectorWitness

flipStaysInsideSignedCollisionFibre :
  poleClass
    (proj₁
      (Residual.actOnCollisionFibre
        ternaryC2PreservesPoleClass
        c2Flip signedClass
        (SSP.sspPosOne , refl)))
  ≡ signedClass
flipStaysInsideSignedCollisionFibre =
  Residual.fibreActionStaysInSamePublicValue
    ternaryC2PreservesPoleClass
    c2Flip signedClass
    (SSP.sspPosOne , refl)
