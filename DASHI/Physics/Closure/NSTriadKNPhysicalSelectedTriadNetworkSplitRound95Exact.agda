module DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND95 / SAME-OBJECT SELF-TRIAD VS EXTERNAL-NETWORK SPLIT
--
-- For one literal physical triad tau=(p,q->k), define its three self forcing
-- vectors from the exact symmetrised ordered-pair interaction on the k,
-- p-energy, and q-energy legs. The full forcing is the actual exhaustive
-- projected Galerkin nonlinearity. Define N_ext=N_full-N_self. Then the mode
-- forcings and the Waleffe amplitude forcing split exactly into self+external.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as Tangent
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross

cong3 :
  ∀ {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
    (f : A → B → C → D) {x x' y y' z z'} →
  x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
cong3 f refl refl refl = refl

addResidualReconstructs :
  ∀ {r} {F : C3.RealField r} (full self : C3.Complex3 F) →
  C3.complex3Add self (C3.complex3Subtract full self) ≡ full
addResidualReconstructs {F = F}
  (C3.complex3 fx fy fz) (C3.complex3 sx sy sz) =
  Algebra.complex3Ext
    (R.solve 2 (λ f s → s R.⊕ (f R.⊕ (R.⊝ s)) R.⊜ f) refl fx sx)
    (R.solve 2 (λ f s → s R.⊕ (f R.⊕ (R.⊝ s)) R.⊜ f) refl fy sy)
    (R.solve 2 (λ f s → s R.⊕ (f R.⊕ (R.⊝ s)) R.⊜ f) refl fz sz)
  where module R = Ring.Solver F

selfForcingForIncidence :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
selfForcingForIncidence {F = F} {E = E} {I = I} system tau =
  Signed.orderedPairVelocityInteraction
    (C3.complex3VelocityGalerkinLaws F E I)
    (Physical.k tau) (Physical.p tau) (Physical.q tau)
    (Audit.velocityAt system (Physical.p tau))
    (Audit.velocityAt system (Physical.q tau))

selfForcingK :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
selfForcingK system tau = selfForcingForIncidence system tau

selfForcingP :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
selfForcingP system tau = selfForcingForIncidence system (Orbit.pEnergyLeg tau)

selfForcingQ :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
selfForcingQ system tau = selfForcingForIncidence system (Orbit.qEnergyLeg tau)

fullForcingK :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
fullForcingK system tau = Audit.projectedNonlinearity system (Physical.k tau)

fullForcingP :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
fullForcingP system tau = Audit.projectedNonlinearity system (Physical.p tau)

fullForcingQ :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
fullForcingQ system tau = Audit.projectedNonlinearity system (Physical.q tau)

externalForcingK :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
externalForcingK system tau =
  C3.complex3Subtract (fullForcingK system tau) (selfForcingK system tau)

externalForcingP :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
externalForcingP system tau =
  C3.complex3Subtract (fullForcingP system tau) (selfForcingP system tau)

externalForcingQ :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
externalForcingQ system tau =
  C3.complex3Subtract (fullForcingQ system tau) (selfForcingQ system tau)

fullKIsSelfPlusExternal :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  fullForcingK system tau
  ≡ C3.complex3Add (selfForcingK system tau) (externalForcingK system tau)
fullKIsSelfPlusExternal system tau =
  sym (addResidualReconstructs (fullForcingK system tau) (selfForcingK system tau))

fullPIsSelfPlusExternal :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  fullForcingP system tau
  ≡ C3.complex3Add (selfForcingP system tau) (externalForcingP system tau)
fullPIsSelfPlusExternal system tau =
  sym (addResidualReconstructs (fullForcingP system tau) (selfForcingP system tau))

fullQIsSelfPlusExternal :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  fullForcingQ system tau
  ≡ C3.complex3Add (selfForcingQ system tau) (externalForcingQ system tau)
fullQIsSelfPlusExternal system tau =
  sym (addResidualReconstructs (fullForcingQ system tau) (selfForcingQ system tau))

networkForcingAdditiveInForcingSlots :
  ∀ {r} {F : C3.RealField r}
    (uK uP uQ selfK selfP selfQ extK extP extQ : C3.Complex3 F) →
  Tangent.networkForcing uK uP uQ
    (C3.complex3Add selfK extK)
    (C3.complex3Add selfP extP)
    (C3.complex3Add selfQ extQ)
  ≡
  C3.complexAdd
    (Tangent.networkForcing uK uP uQ selfK selfP selfQ)
    (Tangent.networkForcing uK uP uQ extK extP extQ)
networkForcingAdditiveInForcingSlots {F = F}
    uK uP uQ selfK selfP selfQ extK extP extQ =
  trans
    (cong₂ C3.complexAdd
      (cong₂ C3.complexAdd
        (Additive.hermitianPairingAddLeft selfK extK (Cross.complex3Cross uP uQ))
        (trans
          (cong (C3.hermitianPairing3 uK) (Tangent.crossAddLeft selfP extP uQ))
          (Additive.hermitianPairingAddRight uK
            (Cross.complex3Cross selfP uQ) (Cross.complex3Cross extP uQ))))
      (trans
        (cong (C3.hermitianPairing3 uK) (Tangent.crossAddRight uP selfQ extQ))
        (Additive.hermitianPairingAddRight uK
          (Cross.complex3Cross uP selfQ) (Cross.complex3Cross uP extQ))))
    regroup
  where
  a = C3.hermitianPairing3 selfK (Cross.complex3Cross uP uQ)
  b = C3.hermitianPairing3 extK (Cross.complex3Cross uP uQ)
  c = C3.hermitianPairing3 uK (Cross.complex3Cross selfP uQ)
  d = C3.hermitianPairing3 uK (Cross.complex3Cross extP uQ)
  e = C3.hermitianPairing3 uK (Cross.complex3Cross uP selfQ)
  f = C3.hermitianPairing3 uK (Cross.complex3Cross uP extQ)

  regroup :
    C3.complexAdd (C3.complexAdd (C3.complexAdd a b) (C3.complexAdd c d))
      (C3.complexAdd e f)
    ≡
    C3.complexAdd
      (C3.complexAdd (C3.complexAdd a c) e)
      (C3.complexAdd (C3.complexAdd b d) f)
  regroup =
    R.solve 6
      (λ a b c d e f →
        (((a R.⊕ b) R.⊕ (c R.⊕ d)) R.⊕ (e R.⊕ f))
        R.⊜ (((a R.⊕ c) R.⊕ e) R.⊕ ((b R.⊕ d) R.⊕ f)))
      refl a b c d e f
    where module R = Ring.Solver F

fullAmplitudeForcing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
fullAmplitudeForcing system tau =
  Tangent.networkForcing
    (Audit.velocityAt system (Physical.k tau))
    (Audit.velocityAt system (Physical.p tau))
    (Audit.velocityAt system (Physical.q tau))
    (fullForcingK system tau) (fullForcingP system tau) (fullForcingQ system tau)

selfAmplitudeForcing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
selfAmplitudeForcing system tau =
  Tangent.networkForcing
    (Audit.velocityAt system (Physical.k tau))
    (Audit.velocityAt system (Physical.p tau))
    (Audit.velocityAt system (Physical.q tau))
    (selfForcingK system tau) (selfForcingP system tau) (selfForcingQ system tau)

externalAmplitudeForcing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
externalAmplitudeForcing system tau =
  Tangent.networkForcing
    (Audit.velocityAt system (Physical.k tau))
    (Audit.velocityAt system (Physical.p tau))
    (Audit.velocityAt system (Physical.q tau))
    (externalForcingK system tau) (externalForcingP system tau) (externalForcingQ system tau)

fullAmplitudeForcingSplitsExactly :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  fullAmplitudeForcing system tau
  ≡ C3.complexAdd (selfAmplitudeForcing system tau) (externalAmplitudeForcing system tau)
fullAmplitudeForcingSplitsExactly system tau =
  trans
    (cong3
      (Tangent.networkForcing
        (Audit.velocityAt system (Physical.k tau))
        (Audit.velocityAt system (Physical.p tau))
        (Audit.velocityAt system (Physical.q tau)))
      (fullKIsSelfPlusExternal system tau)
      (fullPIsSelfPlusExternal system tau)
      (fullQIsSelfPlusExternal system tau))
    (networkForcingAdditiveInForcingSlots
      (Audit.velocityAt system (Physical.k tau))
      (Audit.velocityAt system (Physical.p tau))
      (Audit.velocityAt system (Physical.q tau))
      (selfForcingK system tau) (selfForcingP system tau) (selfForcingQ system tau)
      (externalForcingK system tau) (externalForcingP system tau) (externalForcingQ system tau))

round95PhysicalSelfExternalNetworkSplitClosed : Bool
round95PhysicalSelfExternalNetworkSplitClosed = true

round95FullAmplitudeForcingSplitsExactly : Bool
round95FullAmplitudeForcingSplitsExactly = true

round95PhysicalSelfExternalNetworkSplitClosedIsTrue :
  round95PhysicalSelfExternalNetworkSplitClosed ≡ true
round95PhysicalSelfExternalNetworkSplitClosedIsTrue = refl

round95FullAmplitudeForcingSplitsExactlyIsTrue :
  round95FullAmplitudeForcingSplitsExactly ≡ true
round95FullAmplitudeForcingSplitsExactlyIsTrue = refl
