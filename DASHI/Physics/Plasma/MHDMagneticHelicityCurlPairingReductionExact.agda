module DASHI.Physics.Plasma.MHDMagneticHelicityCurlPairingReductionExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; _≡_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNLerayAlgebraProgram as Leray
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as LerayOut
import DASHI.Physics.Closure.NSTriadKNLeraySelfAdjointness as LerayAdjoint
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Plasma.MHDCurlLerayProjectionInvariantExact as CurlProjection
import DASHI.Physics.Plasma.MHDPhysicalInverseCurlMagneticHelicityExact as InverseCurl

------------------------------------------------------------------------
-- GENERIC OPERATOR REDUCTION FOR MAGNETIC HELICITY
------------------------------------------------------------------------

physicalVectorPotentialTransverse :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (magnetic : C3.Complex3 F) →
  Helical.Transverse E k magnetic →
  Helical.Transverse E k
    (InverseCurl.physicalVectorPotential E I k magnetic)
physicalVectorPotentialTransverse {F = F} E I S L k magnetic transverse =
  trans
    (Scaling.bilinearDot3ScaleRight
      (C3.realEmbed F (C3.inverseNormSquared I k))
      (C3.modeVector E k)
      (Helical.curlSymbol E k magnetic))
    (trans
      (cong
        (C3.complexMultiply
          (C3.realEmbed F (C3.inverseNormSquared I k)))
        (Helical.curlSymbolPreservesTransverse L k magnetic transverse))
      (Hermitian.complexMultiplyZeroRight
        (C3.realEmbed F (C3.inverseNormSquared I k))))

curlPairingAgainstInverseCurl :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode) →
  Z3.NonZeroMode k →
  (candidate magnetic : C3.Complex3 F) →
  Helical.Transverse E k magnetic →
  C3.hermitianPairing3
    (Helical.curlSymbol E k candidate)
    (InverseCurl.physicalVectorPotential E I k magnetic)
  ≡ C3.hermitianPairing3 candidate magnetic
curlPairingAgainstInverseCurl
    E I S L k nonzero candidate magnetic transverseMagnetic =
  trans
    (cong
      (λ first →
        C3.hermitianPairing3 first
          (InverseCurl.physicalVectorPotential E I k magnetic))
      (sym (CurlProjection.curlLerayProjectionInvariant E I k candidate)))
    (trans
      (Helical.curlSymbolSelfAdjointOnTransverse
        L k
        (C3.lerayProject3 E I k candidate)
        (InverseCurl.physicalVectorPotential E I k magnetic)
        (LerayOut.lerayOutputTransverseExact E I k nonzero candidate)
        (physicalVectorPotentialTransverse
          E I S L k magnetic transverseMagnetic))
      (trans
        (cong
          (C3.hermitianPairing3 (C3.lerayProject3 E I k candidate))
          (InverseCurl.physicalVectorPotentialIsCurlInverse
            E I S L k nonzero magnetic transverseMagnetic))
        (trans
          (LerayAdjoint.leraySelfAdjoint E I k candidate magnetic)
          (cong
            (C3.hermitianPairing3 candidate)
            (Leray.lerayFixesTransverse E I k magnetic transverseMagnetic)))))

realCurlPairingAgainstInverseCurl :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode) →
  Z3.NonZeroMode k →
  (candidate magnetic : C3.Complex3 F) →
  Helical.Transverse E k magnetic →
  C3.complexRealPart
    (C3.hermitianPairing3
      (Helical.curlSymbol E k candidate)
      (InverseCurl.physicalVectorPotential E I k magnetic))
  ≡
  C3.complexRealPart (C3.hermitianPairing3 magnetic candidate)
realCurlPairingAgainstInverseCurl
    E I S L k nonzero candidate magnetic transverseMagnetic =
  trans
    (cong C3.complexRealPart
      (curlPairingAgainstInverseCurl
        E I S L k nonzero candidate magnetic transverseMagnetic))
    (trans
      (cong C3.complexRealPart
        (Hermitian.hermitianPairingConjugateSymmetric candidate magnetic))
      (Hermitian.complexRealPartConjugateInvariant
        (C3.hermitianPairing3 magnetic candidate)))

record MagneticHelicityCurlPairingBoundary : Set where
  constructor magnetic-helicity-curl-pairing-boundary
  field
    curlLerayInvariantReused : Bool
    curlLerayInvariantReusedIsTrue : curlLerayInvariantReused ≡ true

    physicalInverseCurlInversionReused : Bool
    physicalInverseCurlInversionReusedIsTrue :
      physicalInverseCurlInversionReused ≡ true

    realCurlPairingReducesToMagneticAgainstCandidate : Bool
    realCurlPairingReducesToMagneticAgainstCandidateIsTrue :
      realCurlPairingReducesToMagneticAgainstCandidate ≡ true

canonicalMagneticHelicityCurlPairingBoundary : MagneticHelicityCurlPairingBoundary
canonicalMagneticHelicityCurlPairingBoundary =
  magnetic-helicity-curl-pairing-boundary true refl true refl true refl
