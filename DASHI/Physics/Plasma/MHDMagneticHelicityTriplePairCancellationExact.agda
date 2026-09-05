module DASHI.Physics.Plasma.MHDMagneticHelicityTriplePairCancellationExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; trans; _≡_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3ScalarTripleOrbitRound93Exact as Triple
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeSelectedSwapAntisymmetryRound118Exact as CrossSwap
import DASHI.Physics.Closure.NSTriadKNPhysicalTransferOutputPhaseSignFlipRound88Exact as RealSign

------------------------------------------------------------------------
-- APPLICATION-NEUTRAL REAL TRIPLE-PAIR CANCELLATIONS
------------------------------------------------------------------------

realNegativeConjugateCancels :
  ∀ {r : Level} {F : C3.RealField r}
    (z : C3.Complex F) →
  C3.complexAdd
    (C3.complexRealPart z)
    (C3.complexRealPart
      (C3.complexNegate (C3.complexConjugate z)))
  ≡ C3.complexZero F
realNegativeConjugateCancels {F = F} z =
  trans
    (cong
      (C3.complexAdd (C3.complexRealPart z))
      (trans
        (RealSign.complexRealPartNegate (C3.complexConjugate z))
        (cong C3.complexNegate
          (Hermitian.complexRealPartConjugateInvariant z))))
    (Additive.complexAddInverseRight (C3.complexRealPart z))

realNegativeCancels :
  ∀ {r : Level} {F : C3.RealField r}
    (z : C3.Complex F) →
  C3.complexAdd
    (C3.complexRealPart z)
    (C3.complexRealPart (C3.complexNegate z))
  ≡ C3.complexZero F
realNegativeCancels z =
  trans
    (cong (C3.complexAdd (C3.complexRealPart z))
      (RealSign.complexRealPartNegate z))
    (Additive.complexAddInverseRight (C3.complexRealPart z))

baseAmplitude :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
baseAmplitude U Q K =
  C3.hermitianPairing3 K
    (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross U Q)

reversedRealityMateAmplitude :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
reversedRealityMateAmplitude U Q K =
  C3.hermitianPairing3 Q
    (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
      (C3.complex3Conjugate U) K)

reversedRealityMateIsNegativeConjugateBase :
  ∀ {r : Level} {F : C3.RealField r}
    (U Q K : C3.Complex3 F) →
  reversedRealityMateAmplitude U Q K
  ≡ C3.complexNegate (C3.complexConjugate (baseAmplitude U Q K))
reversedRealityMateIsNegativeConjugateBase U Q K =
  trans
    (cong (C3.hermitianPairing3 Q)
      (CrossSwap.crossAnticommutative (C3.complex3Conjugate U) K))
    (trans
      (Additive.hermitianPairingNegateRight Q
        (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
          K (C3.complex3Conjugate U)))
      (cong C3.complexNegate
        (Triple.qEnergyAmplitudeIsConjugateBase U Q K)))

realityMateRealPairCancels :
  ∀ {r : Level} {F : C3.RealField r}
    (U Q K : C3.Complex3 F) →
  C3.complexAdd
    (C3.complexRealPart (baseAmplitude U Q K))
    (C3.complexRealPart (reversedRealityMateAmplitude U Q K))
  ≡ C3.complexZero F
realityMateRealPairCancels U Q K
  rewrite reversedRealityMateIsNegativeConjugateBase U Q K =
  realNegativeConjugateCancels (baseAmplitude U Q K)

middleAmplitude :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
middleAmplitude P U Q =
  C3.hermitianPairing3 P
    (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
      U (C3.complex3Conjugate Q))

middleSwapIsNegative :
  ∀ {r : Level} {F : C3.RealField r}
    (P U Q : C3.Complex3 F) →
  middleAmplitude P U Q
  ≡ C3.complexNegate (middleAmplitude Q U P)
middleSwapIsNegative P U Q =
  trans
    (Triple.scalarTripleRotateRight
      (C3.complex3Conjugate P) U (C3.complex3Conjugate Q))
    (Triple.scalarTripleSwapLast
      (C3.complex3Conjugate Q) (C3.complex3Conjugate P) U)

middleRealPairCancels :
  ∀ {r : Level} {F : C3.RealField r}
    (P U Q : C3.Complex3 F) →
  C3.complexAdd
    (C3.complexRealPart (middleAmplitude P U Q))
    (C3.complexRealPart (middleAmplitude Q U P))
  ≡ C3.complexZero F
middleRealPairCancels P U Q =
  let
    target = middleAmplitude Q U P
  in
  trans
    (cong
      (λ first → C3.complexAdd (C3.complexRealPart first)
        (C3.complexRealPart target))
      (middleSwapIsNegative P U Q))
    (trans
      (cong
        (λ first → C3.complexAdd first (C3.complexRealPart target))
        (RealSign.complexRealPartNegate target))
      (Additive.complexAddInverseLeft (C3.complexRealPart target)))

record TriplePairCancellationBoundary : Set where
  constructor triple-pair-cancellation-boundary
  field
    realityMatePairCancellationOwned : Bool
    realityMatePairCancellationOwnedIsTrue :
      realityMatePairCancellationOwned ≡ true

    middleOddPermutationPairCancellationOwned : Bool
    middleOddPermutationPairCancellationOwnedIsTrue :
      middleOddPermutationPairCancellationOwned ≡ true

    cancellationOccursBeforeNormOrAbsoluteValue : Bool
    cancellationOccursBeforeNormOrAbsoluteValueIsTrue :
      cancellationOccursBeforeNormOrAbsoluteValue ≡ true

canonicalTriplePairCancellationBoundary : TriplePairCancellationBoundary
canonicalTriplePairCancellationBoundary =
  triple-pair-cancellation-boundary true refl true refl true refl
