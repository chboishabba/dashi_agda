module DASHI.Physics.Closure.NSTriadKNComLiteralKernelScalingRound57Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 57 CONTRIBUTION
--
-- Audit an important normalization issue in the newly literal Com kernel.
-- The raw transport/odd-PQ coefficient is homogeneous of degree one in the
-- advecting velocity.  Therefore the source constants 17/64 and 65/512 cannot
-- honestly be interpreted as amplitude-free bounds on these raw coefficients;
-- they must arise only after the correct normalized Gram/energy realization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportCoefficientSkewRound40Exact as Coeff
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportMatrixSkewRound40Exact as Matrix
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQKernelRound57Exact as Odd

scaledVelocity :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F →
  (Z3.FourierMode → C3.Complex3 F) →
  Z3.FourierMode → C3.Complex3 F
scaledVelocity scalar velocity mode =
  C3.complex3Scale scalar (velocity mode)

zeroEqualsScalarTimesZero :
  ∀ {r} {F : C3.RealField r} (scalar : C3.Complex F) →
  C3.complexZero F
  ≡ C3.complexMultiply scalar (C3.complexZero F)
zeroEqualsScalarTimesZero {F = F} scalar =
  R.solve 1
    (λ scalar → R.0# R.⊜ scalar R.⊗ R.0#)
    refl scalar
  where module R = Ring.Solver F

negateScaled :
  ∀ {r} {F : C3.RealField r}
    (scalar value : C3.Complex F) →
  C3.complexNegate (C3.complexMultiply scalar value)
  ≡ C3.complexMultiply scalar (C3.complexNegate value)
negateScaled {F = F} scalar value =
  R.solve 2
    (λ scalar value →
      R.⊝ (scalar R.⊗ value)
      R.⊜ scalar R.⊗ (R.⊝ value))
    refl scalar value
  where module R = Ring.Solver F

transportCoefficientHomogeneous :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (scalar : C3.Complex F)
    (mode : Z3.FourierMode)
    (value : C3.Complex3 F) →
  Coeff.transportCoefficient E mode (C3.complex3Scale scalar value)
  ≡ C3.complexMultiply scalar (Coeff.transportCoefficient E mode value)
transportCoefficientHomogeneous {F = F} E scalar mode value =
  trans
    (cong
      (C3.complexMultiply (C3.complexI F))
      (Scaling.bilinearDot3ScaleRight
        scalar (C3.modeVector E mode) value))
    (R.solve 3
      (λ scalar i dot →
        (i R.⊗ (scalar R.⊗ dot))
        R.⊜
        (scalar R.⊗ (i R.⊗ dot)))
      refl
      scalar
      (C3.complexI F)
      (Coeff.modeDot E mode value))
  where module R = Ring.Solver F

transportEntryCoefficientHomogeneous :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (scalar : C3.Complex F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  ∀ {input output}
    (entry : Matrix.PhysicalTransportMatrixEntry input output) →
  Matrix.transportEntryCoefficient E (scaledVelocity scalar velocity) entry
  ≡ C3.complexMultiply scalar
      (Matrix.transportEntryCoefficient E velocity entry)
transportEntryCoefficientHomogeneous E scalar velocity {input} entry =
  transportCoefficientHomogeneous E scalar input
    (velocity (Matrix.advector entry))

literalOddPQEntryHomogeneous :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (cutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (scalar : C3.Complex (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  ∀ {input output}
    (entry : Matrix.PhysicalTransportMatrixEntry input output) →
  Odd.literalOddPQEntryCoefficient model cutoff E
      (scaledVelocity scalar velocity) entry
  ≡ C3.complexMultiply scalar
      (Odd.literalOddPQEntryCoefficient model cutoff E velocity entry)
literalOddPQEntryHomogeneous model cutoff E scalar velocity {input} {output} entry
  with LP.lowSelect model cutoff output | LP.lowSelect model cutoff input
... | true | false =
  transportEntryCoefficientHomogeneous E scalar velocity entry
... | true | true =
  zeroEqualsScalarTimesZero scalar
... | false | true =
  trans
    (cong C3.complexNegate
      (transportEntryCoefficientHomogeneous E scalar velocity entry))
    (negateScaled scalar (Matrix.transportEntryCoefficient E velocity entry))
... | false | false =
  zeroEqualsScalarTimesZero scalar

rawOddPQKernelIsVelocityHomogeneous : Bool
rawOddPQKernelIsVelocityHomogeneous = true

rawOddPQKernelConstantsRequireNormalizedGramMeaning : Bool
rawOddPQKernelConstantsRequireNormalizedGramMeaning = true

rawOddPQKernelIsVelocityHomogeneousIsTrue :
  rawOddPQKernelIsVelocityHomogeneous ≡ true
rawOddPQKernelIsVelocityHomogeneousIsTrue = refl

rawOddPQKernelConstantsRequireNormalizedGramMeaningIsTrue :
  rawOddPQKernelConstantsRequireNormalizedGramMeaning ≡ true
rawOddPQKernelConstantsRequireNormalizedGramMeaningIsTrue = refl
