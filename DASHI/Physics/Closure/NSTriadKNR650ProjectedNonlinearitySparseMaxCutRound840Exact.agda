{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650ProjectedNonlinearitySparseMaxCutRound840Exact where

------------------------------------------------------------------------
-- R840 / EXACT SPARSE MAX-CUT FOR THE LITERAL R30 NONLINEARITY
--
-- The physical projected nonlinearity is a complete ordered-pair output-fibre
-- sum.  If either input velocity of one ordered interaction is zero, that
-- interaction is exactly zero BEFORE projection and before any norm/estimate.
--
-- This owner proves:
--
--   projectedNonlinearity(system,k)
--     = fold projectedOrderedTerm over the literal physical output fibre
--     = the same fold after removing every cell certified inactive.
--
-- R829 can therefore evaluate only seed-seed interactions of the sparse
-- 3-4-5 snapshot.  No shell estimate, helical law, time trajectory, or
-- numerical approximation is introduced.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityZeroOutputRound436Exact as R436
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelEndpointZeroRound164Exact as R164
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse

orderedTermZeroFromPVelocityZero :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Audit.velocity system (Physical.p tau) ≡ C3.complex3Zero F →
  Audit.projectedOrderedTerm system tau ≡ C3.complex3Zero F
orderedTermZeroFromPVelocityZero {F = F} {E = E} {I = I}
    system tau pZero =
  let
    q = Physical.q tau
    k = Physical.k tau
    uQ = Audit.velocity system q

    dotZero :
      C3.bilinearDot3
        (Audit.velocity system (Physical.p tau))
        (C3.modeVector E q)
      ≡ C3.complexZero F
    dotZero =
      trans
        (cong
          (λ value → C3.bilinearDot3 value (C3.modeVector E q))
          pZero)
        (R164.bilinearDot3ZeroLeft (C3.modeVector E q))

    innerZero :
      C3.complex3Scale
        (C3.bilinearDot3
          (Audit.velocity system (Physical.p tau))
          (C3.modeVector E q))
        uQ
      ≡ C3.complex3Zero F
    innerZero =
      trans
        (cong
          (λ scalar → C3.complex3Scale scalar uQ)
          dotZero)
        (R106.complex3ScaleZeroScalar uQ)

    projectedZero :
      C3.lerayProject3 E I k
        (C3.complex3Scale
          (C3.bilinearDot3
            (Audit.velocity system (Physical.p tau))
            (C3.modeVector E q))
          uQ)
      ≡ C3.complex3Zero F
    projectedZero =
      trans
        (cong (C3.lerayProject3 E I k) innerZero)
        (R436.lerayZeroVector E I k)
  in
  trans
    (cong
      (C3.complex3Scale
        (C3.complexNegate (C3.complexI F)))
      projectedZero)
    (R106.complex3ScaleZeroVector
      (C3.complexNegate (C3.complexI F)))

orderedTermZeroFromQVelocityZero :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Audit.velocity system (Physical.q tau) ≡ C3.complex3Zero F →
  Audit.projectedOrderedTerm system tau ≡ C3.complex3Zero F
orderedTermZeroFromQVelocityZero {F = F} {E = E} {I = I}
    system tau qZero =
  let
    p = Physical.p tau
    q = Physical.q tau
    k = Physical.k tau
    scalar =
      C3.bilinearDot3
        (Audit.velocity system p)
        (C3.modeVector E q)

    innerZero :
      C3.complex3Scale scalar (Audit.velocity system q)
      ≡ C3.complex3Zero F
    innerZero =
      trans
        (cong (C3.complex3Scale scalar) qZero)
        (R106.complex3ScaleZeroVector scalar)

    projectedZero :
      C3.lerayProject3 E I k
        (C3.complex3Scale scalar (Audit.velocity system q))
      ≡ C3.complex3Zero F
    projectedZero =
      trans
        (cong (C3.lerayProject3 E I k) innerZero)
        (R436.lerayZeroVector E I k)
  in
  trans
    (cong
      (C3.complex3Scale
        (C3.complexNegate (C3.complexI F)))
      projectedZero)
    (R106.complex3ScaleZeroVector
      (C3.complexNegate (C3.complexI F)))

------------------------------------------------------------------------
-- The Audit map/sum definition is exactly the repository R224 vector fold.
------------------------------------------------------------------------

sumMappedTermsIsFold :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (items : List Physical.PhysicalTriadIncidence) →
  Audit.sumVectors (Audit.mapTriadTerms system items)
  ≡ R224.foldVector (Audit.projectedOrderedTerm system) items
sumMappedTermsIsFold system [] = refl
sumMappedTermsIsFold system (tau ∷ rest) =
  cong (C3.complex3Add (Audit.projectedOrderedTerm system tau))
    (sumMappedTermsIsFold system rest)

projectedNonlinearityIsLiteralFibreFold :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  Audit.projectedNonlinearity system output
  ≡
  R224.foldVector
    (Audit.projectedOrderedTerm system)
    (Output.physicalOutputFiber (Audit.cutoff system) output)
projectedNonlinearityIsLiteralFibreFold system output =
  sumMappedTermsIsFold system
    (Output.physicalOutputFiber (Audit.cutoff system) output)

data VelocityInactiveReason
    {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) : Set r where
  pVelocityZero :
    Audit.velocity system (Physical.p tau) ≡ C3.complex3Zero F →
    VelocityInactiveReason system tau
  qVelocityZero :
    Audit.velocity system (Physical.q tau) ≡ C3.complex3Zero F →
    VelocityInactiveReason system tau

pruneProjectedNonlinearity :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (select : Physical.PhysicalTriadIncidence → Bool) →
  ((tau : Physical.PhysicalTriadIncidence) →
    select tau ≡ false →
    VelocityInactiveReason system tau) →
  (output : Z3.FourierMode) →
  Audit.projectedNonlinearity system output
  ≡
  R224.foldVector
    (Audit.projectedOrderedTerm system)
    (Sparse.filterSelected select
      (Output.physicalOutputFiber (Audit.cutoff system) output))
pruneProjectedNonlinearity system select inactive output =
  trans
    (projectedNonlinearityIsLiteralFibreFold system output)
    (Sparse.foldPruneZero
      select
      (Audit.projectedOrderedTerm system)
      zero
      (Output.physicalOutputFiber (Audit.cutoff system) output))
  where
  zero :
    (tau : Physical.PhysicalTriadIncidence) →
    select tau ≡ false →
    Audit.projectedOrderedTerm system tau ≡ C3.complex3Zero _
  zero tau rejected with inactive tau rejected
  ... | pVelocityZero proof =
    orderedTermZeroFromPVelocityZero system tau proof
  ... | qVelocityZero proof =
    orderedTermZeroFromQVelocityZero system tau proof

round840OrderedTermPZeroClosed : Bool
round840OrderedTermPZeroClosed = true

round840OrderedTermQZeroClosed : Bool
round840OrderedTermQZeroClosed = true

round840ProjectedNonlinearityLiteralFoldClosed : Bool
round840ProjectedNonlinearityLiteralFoldClosed = true

round840ProjectedNonlinearitySparsePruningClosed : Bool
round840ProjectedNonlinearitySparsePruningClosed = true

round840IntroducesEstimate : Bool
round840IntroducesEstimate = false

round840ClayPromotion : Bool
round840ClayPromotion = false

round840ProjectedNonlinearitySparsePruningClosedIsTrue :
  round840ProjectedNonlinearitySparsePruningClosed ≡ true
round840ProjectedNonlinearitySparsePruningClosedIsTrue = refl
