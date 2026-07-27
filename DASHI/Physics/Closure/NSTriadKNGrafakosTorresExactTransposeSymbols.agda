module DASHI.Physics.Closure.NSTriadKNGrafakosTorresExactTransposeSymbols where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "Multilinear Calderon--Zygmund Theory".
-- Venue/year: Advances in Mathematics 165 (2002), 124--164.
-- DOI: 10.1006/aima.2001.2028.
-- Uses: equations (2)--(3), defining the j-th formal transpose by duality
-- and permuting the output kernel variable with the j-th input variable;
-- equations (15)--(16), describing transposes after one input is frozen.
-- Relationship: equation (16) is a frozen-operator transpose rule, not a
-- claim that a Fourier multiplier can be transposed without tracking
-- conjugation, projection, derivative placement, or the real pairing.
--
-- Authors: DASHI repository contributors.
-- Title: "Exact finite Galerkin transpose-symbol instantiation".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a repository-original exact instantiation.
-- Uses: the literal signed coefficient -i P_k[(u_p dot q)u_q].
-- Relationship: the three scalar trilinear symbols below are definitionally
-- the same coefficient with the tested leg rotated.  Literal vector-valued
-- adjoint formulas remain a separate algebraic obligation.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed

------------------------------------------------------------------------
-- General three-leg permutation surface.
------------------------------------------------------------------------

data OperatorLeg : Set where
  outputLeg firstInputLeg secondInputLeg : OperatorLeg

data FormalTranspose : Set where
  original firstTranspose secondTranspose : FormalTranspose

kernelOutputLeg : FormalTranspose → OperatorLeg
kernelOutputLeg original = outputLeg
kernelOutputLeg firstTranspose = firstInputLeg
kernelOutputLeg secondTranspose = secondInputLeg

firstKernelInput : FormalTranspose → OperatorLeg
firstKernelInput original = firstInputLeg
firstKernelInput firstTranspose = outputLeg
firstKernelInput secondTranspose = firstInputLeg

secondKernelInput : FormalTranspose → OperatorLeg
secondKernelInput original = secondInputLeg
secondKernelInput firstTranspose = secondInputLeg
secondKernelInput secondTranspose = outputLeg

record KernelPermutationReceipt : Set where
  constructor receipt
  field
    originalOutput : kernelOutputLeg original ≡ outputLeg
    firstTransposeOutput : kernelOutputLeg firstTranspose ≡ firstInputLeg
    secondTransposeOutput : kernelOutputLeg secondTranspose ≡ secondInputLeg
    firstTransposeFirstInput : firstKernelInput firstTranspose ≡ outputLeg
    firstTransposeSecondInput : secondKernelInput firstTranspose ≡ secondInputLeg
    secondTransposeFirstInput : firstKernelInput secondTranspose ≡ firstInputLeg
    secondTransposeSecondInput : secondKernelInput secondTranspose ≡ outputLeg

open KernelPermutationReceipt public

kernelPermutationReceipt : KernelPermutationReceipt
kernelPermutationReceipt = receipt refl refl refl refl refl refl refl

------------------------------------------------------------------------
-- Grafakos--Torres equation (16), specialized to a bilinear operator.
--
-- Freeze input 1: the remaining linear transpose is inherited from T*2.
-- Freeze input 2: the remaining linear transpose is inherited from T*1.
------------------------------------------------------------------------

data FrozenInput : Set where
  freezeFirstInput freezeSecondInput : FrozenInput

data InheritedTranspose : Set where
  inheritedFirstTranspose inheritedSecondTranspose : InheritedTranspose

transposeAfterFreeze : FrozenInput → InheritedTranspose
transposeAfterFreeze freezeFirstInput = inheritedSecondTranspose
transposeAfterFreeze freezeSecondInput = inheritedFirstTranspose

record FrozenOperatorTransposeReceipt : Set where
  constructor receipt
  field
    freezeFirstUsesSecondTranspose :
      transposeAfterFreeze freezeFirstInput ≡ inheritedSecondTranspose
    freezeSecondUsesFirstTranspose :
      transposeAfterFreeze freezeSecondInput ≡ inheritedFirstTranspose

open FrozenOperatorTransposeReceipt public

frozenOperatorTransposeReceipt : FrozenOperatorTransposeReceipt
frozenOperatorTransposeReceipt = receipt refl refl

------------------------------------------------------------------------
-- Literal scalar symbols for the repository coefficient.
------------------------------------------------------------------------

outputTrilinearSymbol :
  ∀ {r} (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Z3.FourierMode → Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex F
outputTrilinearSymbol F E I k p q uP uQ testK =
  Signed.testedSignedCoefficient
    (C3.complex3VelocityGalerkinLaws F E I)
    k p q uP uQ testK

firstTransposeTrilinearSymbol :
  ∀ {r} (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Z3.FourierMode → Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex F
firstTransposeTrilinearSymbol F E I p k q testK uQ testP =
  outputTrilinearSymbol F E I k p q testP uQ testK

secondTransposeTrilinearSymbol :
  ∀ {r} (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Z3.FourierMode → Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex F
secondTransposeTrilinearSymbol F E I q p k uP testK testQ =
  outputTrilinearSymbol F E I k p q uP testQ testK

firstTransposePairingIdentity :
  ∀ {r} (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (uP uQ testK : C3.Complex3 F) →
  firstTransposeTrilinearSymbol F E I p k q testK uQ uP
  ≡ outputTrilinearSymbol F E I k p q uP uQ testK
firstTransposePairingIdentity F E I k p q uP uQ testK = refl

secondTransposePairingIdentity :
  ∀ {r} (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (uP uQ testK : C3.Complex3 F) →
  secondTransposeTrilinearSymbol F E I q p k uP testK uQ
  ≡ outputTrilinearSymbol F E I k p q uP uQ testK
secondTransposePairingIdentity F E I k p q uP uQ testK = refl

------------------------------------------------------------------------
-- The scalar pairing identities are exact.  Turning them into vector-valued
-- formulas requires the listed laws and must not be hidden by permutation.
------------------------------------------------------------------------

record LiteralVectorTransposeCutset {r : Level}
    (F : C3.RealField r) : Set (lsuc r) where
  field
    conjugateMovesAcrossHermitianPairing : Set r
    scalarMultiplicationAdjointIdentified : Set r
    bilinearDotAdjointIdentified : Set r
    lerayProjectionSelfAdjointConsumed : Set r
    helicalProjectorSelfAdjointConsumed : Set r
    realPartPairingConventionPreserved : Set r
    firstVectorTransposeFormulaClosed : Set r
    secondVectorTransposeFormulaClosed : Set r

open LiteralVectorTransposeCutset public

formalTransposePermutationClosed : Bool
formalTransposePermutationClosed = true

formalTransposePermutationClosedIsTrue :
  formalTransposePermutationClosed ≡ true
formalTransposePermutationClosedIsTrue = refl

literalScalarTransposeSymbolsClosed : Bool
literalScalarTransposeSymbolsClosed = true

literalScalarTransposeSymbolsClosedIsTrue :
  literalScalarTransposeSymbolsClosed ≡ true
literalScalarTransposeSymbolsClosedIsTrue = refl

literalVectorTransposeFormulasClosed : Bool
literalVectorTransposeFormulasClosed = false

literalVectorTransposeFormulasClosedIsFalse :
  literalVectorTransposeFormulasClosed ≡ false
literalVectorTransposeFormulasClosedIsFalse = refl
