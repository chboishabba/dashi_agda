module DASHI.Physics.Plasma.MHDMagneticHelicityLegTripleAmplitudeExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; _≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as Linear
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Plasma.MHDPlusMinusProjectedPseudoEnergyExact as State
import DASHI.Physics.Plasma.MHDDoubledMagneticElsasserFibreExact as Doubled
import DASHI.Physics.Plasma.MHDPhysicalInverseCurlMagneticHelicityExact as InverseCurl
import DASHI.Physics.Plasma.MHDMagneticHelicityThreeLegBidiExact as ThreeLeg
import DASHI.Physics.Plasma.MHDOrderedPairInductionCurlBidiExact as CurlPair
import DASHI.Physics.Plasma.MHDOrderedPairInductionCurlWeldExact as CurlWeld
import DASHI.Physics.Plasma.MHDMagneticHelicityCurlPairingReductionExact as PairReduce

------------------------------------------------------------------------
-- ONE LITERAL MAGNETIC-HELICITY LEG -> TWO REAL SCALAR-TRIPLE AMPLITUDES
------------------------------------------------------------------------

private
  two : ∀ {r : Level} {F : C3.RealField r} → C3.Complex F
  two {F = F} = C3.complexAdd (C3.complexOne F) (C3.complexOne F)

complex3ScaleOne :
  ∀ {r : Level} {F : C3.RealField r}
    (value : C3.Complex3 F) →
  C3.complex3Scale (C3.complexOne F) value ≡ value
complex3ScaleOne {F = F} (C3.complex3 x y z) =
  Field.complex3Ext
    (C3.complexMultiplyOneLeft F x)
    (C3.complexMultiplyOneLeft F y)
    (C3.complexMultiplyOneLeft F z)

doubleScaleIsAddSelf :
  ∀ {r : Level} {F : C3.RealField r}
    (value : C3.Complex3 F) →
  C3.complex3Scale two value ≡ C3.complex3Add value value
doubleScaleIsAddSelf value =
  trans
    (Linear.complex3ScaleScalarAdd
      (C3.complexOne _) (C3.complexOne _) value)
    (cong₂ C3.complex3Add
      (complex3ScaleOne value)
      (complex3ScaleOne value))

realPairingDoubleTangent :
  ∀ {r : Level} {F : C3.RealField r}
    (tangent test : C3.Complex3 F) →
  C3.complexAdd
    (C3.complexRealPart (C3.hermitianPairing3 tangent test))
    (C3.complexRealPart (C3.hermitianPairing3 tangent test))
  ≡
  C3.complexRealPart
    (C3.hermitianPairing3 (C3.complex3Scale two tangent) test)
realPairingDoubleTangent tangent test =
  trans
    (sym
      (Field.complexRealPartAdd
        (C3.hermitianPairing3 tangent test)
        (C3.hermitianPairing3 tangent test)))
    (cong C3.complexRealPart
      (trans
        (sym (Additive.hermitianPairingAddLeft tangent tangent test))
        (cong (λ first → C3.hermitianPairing3 first test)
          (sym (doubleScaleIsAddSelf tangent)))))

physicalVariationIsDoubleFirstPairing :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : _)
    (magnetic tangent : C3.Complex3 F) →
  Helical.Transverse E k magnetic →
  Helical.Transverse E k tangent →
  ThreeLeg.physicalMagneticHelicityDirectionalVariation E I k magnetic tangent
  ≡
  C3.complexAdd
    (C3.complexRealPart
      (C3.hermitianPairing3 tangent
        (InverseCurl.physicalVectorPotential E I k magnetic)))
    (C3.complexRealPart
      (C3.hermitianPairing3 tangent
        (InverseCurl.physicalVectorPotential E I k magnetic)))
physicalVariationIsDoubleFirstPairing
    E I S L k magnetic tangent transverseMagnetic transverseTangent =
  cong
    (C3.complexAdd
      (C3.complexRealPart
        (C3.hermitianPairing3 tangent
          (InverseCurl.physicalVectorPotential E I k magnetic))))
    secondEqualsFirst
  where
  A = InverseCurl.physicalVectorPotential E I k magnetic

  secondEqualsFirst :
    C3.complexRealPart
      (C3.hermitianPairing3 magnetic
        (InverseCurl.physicalVectorPotential E I k tangent))
    ≡ C3.complexRealPart (C3.hermitianPairing3 tangent A)
  secondEqualsFirst =
    trans
      (cong C3.complexRealPart
        (sym
          (InverseCurl.physicalVectorPotentialSelfAdjoint
            E I S L k magnetic tangent transverseMagnetic transverseTangent)))
      (trans
        (cong C3.complexRealPart
          (Hermitian.hermitianPairingConjugateSymmetric A tangent))
        (Hermitian.complexRealPartConjugateInvariant
          (C3.hermitianPairing3 tangent A)))

crossCandidate :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  State.IdealElsasserFourierState F E →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
crossCandidate state tau =
  C3.complex3Add
    (Cross.complex3Cross
      (CurlPair.doubledVelocity state (Physical.p tau))
      (Doubled.doubledMagnetic state (Physical.q tau)))
    (Cross.complex3Cross
      (CurlPair.doubledVelocity state (Physical.q tau))
      (Doubled.doubledMagnetic state (Physical.p tau)))

legTripleAmplitude :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  State.IdealElsasserFourierState F E →
  Physical.PhysicalTriadIncidence → C3.Complex F
legTripleAmplitude state tau =
  C3.complexAdd
    (C3.complexRealPart
      (C3.hermitianPairing3
        (Doubled.doubledMagnetic state (Physical.k tau))
        (Cross.complex3Cross
          (CurlPair.doubledVelocity state (Physical.p tau))
          (Doubled.doubledMagnetic state (Physical.q tau)))))
    (C3.complexRealPart
      (C3.hermitianPairing3
        (Doubled.doubledMagnetic state (Physical.k tau))
        (Cross.complex3Cross
          (CurlPair.doubledVelocity state (Physical.q tau))
          (Doubled.doubledMagnetic state (Physical.p tau)))))

magneticHelicityLegVariationIsTripleAmplitude :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  Physical.NonZeroPhysicalTriad tau →
  ThreeLeg.magneticHelicityLegVariation E I state tau
  ≡ legTripleAmplitude state tau
magneticHelicityLegVariationIsTripleAmplitude
    {F = F} E I S L state tau nonzero =
  let
    k = Physical.k tau
    magnetic = Doubled.doubledMagnetic state k
    tangent = CurlWeld.orderedPairDoubledInduction I state tau
    A = InverseCurl.physicalVectorPotential E I k magnetic
    candidate = crossCandidate state tau

    tangentTransverse : Helical.Transverse E k tangent
    tangentTransverse =
      let
        first = Doubled.doubledInductionOrderedTransverse
          I state k (Physical.p tau) (Physical.q tau)
          (Physical.kNonzero nonzero)
        second = Doubled.doubledInductionOrderedTransverse
          I state k (Physical.q tau) (Physical.p tau)
          (Physical.kNonzero nonzero)
      in
      trans
        (DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws.bilinearDot3RightAdd
          (C3.modeVector E k)
          (Doubled.doubledInductionOrderedInteraction I state k (Physical.p tau) (Physical.q tau))
          (Doubled.doubledInductionOrderedInteraction I state k (Physical.q tau) (Physical.p tau)))
        (trans
          (cong₂ C3.complexAdd first second)
          (Field.complexAddZeroLeft (C3.complexZero F)))

    symmetricVariation :
      ThreeLeg.physicalMagneticHelicityDirectionalVariation E I k magnetic tangent
      ≡ C3.complexRealPart
          (C3.hermitianPairing3 (C3.complex3Scale two tangent) A)
    symmetricVariation =
      trans
        (physicalVariationIsDoubleFirstPairing
          E I S L k magnetic tangent
          (Doubled.doubledMagneticTransverse state k)
          tangentTransverse)
        (realPairingDoubleTangent tangent A)

    tangentCurl :
      C3.complex3Scale two tangent
      ≡ Helical.curlSymbol E k candidate
    tangentCurl =
      trans
        (CurlWeld.orderedPairDoubledInductionDoublesToCurlCrosses
          E I state tau)
        (sym
          (DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws.hermitianDummy
            {F = F}))
  in
  trans
    symmetricVariation
    (trans
      (cong
        (λ first → C3.complexRealPart (C3.hermitianPairing3 first A))
        tangentCurl)
      (trans
        (PairReduce.realCurlPairingAgainstInverseCurl
          E I S L k (Physical.kNonzero nonzero)
          candidate magnetic
          (Doubled.doubledMagneticTransverse state k))
        (trans
          (cong C3.complexRealPart
            (Additive.hermitianPairingAddRight
              magnetic
              (Cross.complex3Cross
                (CurlPair.doubledVelocity state (Physical.p tau))
                (Doubled.doubledMagnetic state (Physical.q tau)))
              (Cross.complex3Cross
                (CurlPair.doubledVelocity state (Physical.q tau))
                (Doubled.doubledMagnetic state (Physical.p tau)))))
          (Field.complexRealPartAdd
            (C3.hermitianPairing3 magnetic
              (Cross.complex3Cross
                (CurlPair.doubledVelocity state (Physical.p tau))
                (Doubled.doubledMagnetic state (Physical.q tau))))
            (C3.hermitianPairing3 magnetic
              (Cross.complex3Cross
                (CurlPair.doubledVelocity state (Physical.q tau))
                (Doubled.doubledMagnetic state (Physical.p tau))))))))

record LegTripleAmplitudeBoundary : Set where
  constructor leg-triple-amplitude-boundary
  field
    oneLegReductionOwned : Bool
    oneLegReductionOwnedIsTrue : oneLegReductionOwned ≡ true

    divisionByTwoUsed : Bool
    divisionByTwoUsedIsFalse : divisionByTwoUsed ≡ false

    threeLegCancellationProvedHere : Bool
    threeLegCancellationProvedHereIsFalse : threeLegCancellationProvedHere ≡ false

canonicalLegTripleAmplitudeBoundary : LegTripleAmplitudeBoundary
canonicalLegTripleAmplitudeBoundary =
  leg-triple-amplitude-boundary true refl false refl false refl
