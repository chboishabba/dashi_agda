module DASHI.Analysis.StrictKernelMomentRatioExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Generic strict-TP2 -> strict moment-ratio architecture.
--
-- A kernel K(h,u) is strictly TP2 when ordered heights a<p and ordered
-- support points u<v give the positive 2x2 minor
--
--   K(a,u) K(p,v) - K(a,v) K(p,u) > 0.
--
-- For a positive nondegenerate measure and an increasing score q(u), the
-- corresponding low/high weighted moments inherit a strict cross-product
-- orientation.  This file owns the theorem *shape* and exact finite shadows;
-- it does not pretend DASHI's current weak real/integral interface already
-- proves the continuum composition theorem.
------------------------------------------------------------------------

record StrictTP2Kernel : Set₁ where
  field
    Height Support Scalar : Set
    Kernel : Height → Support → Scalar
    StrictHeight : Height → Height → Set
    StrictSupport : Support → Support → Set
    StrictGreater : Scalar → Scalar → Set
    multiply : Scalar → Scalar → Scalar

    tp2MinorPositive :
      (a p : Height) →
      (u v : Support) →
      StrictHeight a p →
      StrictSupport u v →
      StrictGreater
        (multiply (Kernel a u) (Kernel p v))
        (multiply (Kernel a v) (Kernel p u))

    kernelReading : String

open StrictTP2Kernel public

record StrictMomentRatioComposition
    (kernel : StrictTP2Kernel) : Set₁ where
  field
    Moment : Set
    lowHeight highHeight : Height kernel
    heightOrdered : StrictHeight kernel lowHeight highHeight

    moment0 momentQ : Height kernel → Moment
    multiplyMoment : Moment → Moment → Moment
    StrictMomentGreater : Moment → Moment → Set

    positiveNondegenerateMeasure : Set
    increasingScore : Set
    symmetrizedDoubleIntegralIdentity : Set

    strictMomentCrossProduct :
      StrictMomentGreater
        (multiplyMoment (moment0 lowHeight) (momentQ highHeight))
        (multiplyMoment (momentQ lowHeight) (moment0 highHeight))

    compositionReading : String

open StrictMomentRatioComposition public

------------------------------------------------------------------------
-- Signed-orientation carrier used by consumers such as G21.
------------------------------------------------------------------------

data DeterminantOrientation : Set where
  positiveOrientation negativeOrientation : DeterminantOrientation

record OrientedMomentDeterminant : Set₁ where
  field
    Scalar : Set
    lowMoment0 lowMomentQ highMoment0 highMomentQ : Scalar
    multiply : Scalar → Scalar → Scalar
    StrictGreater : Scalar → Scalar → Set
    orientation : DeterminantOrientation

    positiveOrientationProof :
      orientation ≡ positiveOrientation →
      StrictGreater
        (multiply lowMoment0 highMomentQ)
        (multiply lowMomentQ highMoment0)

    negativeOrientationProof :
      orientation ≡ negativeOrientation →
      StrictGreater
        (multiply lowMomentQ highMoment0)
        (multiply lowMoment0 highMomentQ)

open OrientedMomentDeterminant public

------------------------------------------------------------------------
-- Tiny finite regression: a strictly TP2 2x2 kernel produces a strictly
-- ordered moment-ratio cross product.  Nat inequalities are encoded as
-- disequalities to keep this generic owner independent of an ordered-ring
-- library.
------------------------------------------------------------------------

data H2 : Set where lowH highH : H2
data U2 : Set where innerU outerU : U2

finiteKernel : H2 → U2 → Nat
finiteKernel lowH innerU = 1
finiteKernel lowH outerU = 1
finiteKernel highH innerU = 1
finiteKernel highH outerU = 2

finiteTP2MinorDistinct :
  finiteKernel lowH innerU * finiteKernel highH outerU
  ≡ finiteKernel lowH outerU * finiteKernel highH innerU
  → ⊥
finiteTP2MinorDistinct ()

finiteLowM0 finiteLowMQ finiteHighM0 finiteHighMQ : Nat
finiteLowM0 = 2
finiteLowMQ = 3
finiteHighM0 = 3
finiteHighMQ = 5

finiteMomentCrossProductStrictlySeparated :
  finiteLowM0 * finiteHighMQ
  ≡ finiteLowMQ * finiteHighM0
  → ⊥
finiteMomentCrossProductStrictlySeparated ()

record StrictKernelMomentRatioBoundary : Set where
  constructor strictKernelMomentRatioBoundary
  field
    strictTP2InterfaceConstructed : Bool
    strictTP2InterfaceConstructedIsTrue : strictTP2InterfaceConstructed ≡ true
    signedMomentOrientationConstructed : Bool
    signedMomentOrientationConstructedIsTrue : signedMomentOrientationConstructed ≡ true
    finiteTP2WitnessConstructed : Bool
    finiteTP2WitnessConstructedIsTrue : finiteTP2WitnessConstructed ≡ true
    continuumStrictCompositionDerivedInAgda : Bool
    continuumStrictCompositionDerivedInAgdaIsFalse :
      continuumStrictCompositionDerivedInAgda ≡ false

canonicalStrictKernelMomentRatioBoundary : StrictKernelMomentRatioBoundary
canonicalStrictKernelMomentRatioBoundary =
  strictKernelMomentRatioBoundary true refl true refl true refl false refl
