module DASHI.Physics.Plasma.MHDElsasserDerivativeFactorAntisymmetryReuseExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNCannoneTrilinearAntisymmetryAudit as Anti

------------------------------------------------------------------------
-- THE DERIVATIVE-FACTOR ANTISYMMETRY IS PDE-AGNOSTIC
--
-- For a resonant Fourier triad p+q+k=0 and any p-transverse transport mode a_p,
--
--   (a_p dot q) + (-(a_p dot k)) = 0.
--
-- The existing repository theorem was developed in the NS lane, but its proof
-- only uses resonance and transversality.  Therefore an Elsasser advector
-- z^{-alpha}_p may instantiate it without importing any NS dynamics.
------------------------------------------------------------------------

elsasserDerivativePairCancels :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    {p q k : Z3.FourierMode}
    {transportP : C3.Complex3 F} →
  Z3.Resonance p q k →
  Helical.Transverse E p transportP →
  C3.complexAdd
    (Anti.transportDerivativeFactor E transportP q)
    (Anti.conjugateTestDerivativeFactor E transportP k)
  ≡ C3.complexZero F
elsasserDerivativePairCancels =
  Anti.discreteTransportPlusConjugateTestDerivativeZero

record ElsasserDerivativeAntisymmetryBoundary : Set where
  constructor elsasser-derivative-antisymmetry-boundary
  field
    derivativeFactorAntisymmetryOwned : Bool
    derivativeFactorAntisymmetryOwnedIsTrue :
      derivativeFactorAntisymmetryOwned ≡ true

    proofUsesNavierStokesEquation : Bool
    proofUsesNavierStokesEquationIsFalse :
      proofUsesNavierStokesEquation ≡ false

    resonanceAndTransportTransversalityAreSufficient : Bool
    resonanceAndTransportTransversalityAreSufficientIsTrue :
      resonanceAndTransportTransversalityAreSufficient ≡ true

canonicalElsasserDerivativeAntisymmetryBoundary :
  ElsasserDerivativeAntisymmetryBoundary
canonicalElsasserDerivativeAntisymmetryBoundary =
  elsasser-derivative-antisymmetry-boundary true refl false refl true refl
