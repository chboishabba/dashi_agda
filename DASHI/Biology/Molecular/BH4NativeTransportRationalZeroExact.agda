module DASHI.Biology.Molecular.BH4NativeTransportRationalZeroExact where

-- This bridges the ACTUAL literal 27x54 original incidence matrix to
-- arbitrary rational 54-bond currents. It is finite algebra, not PNP
-- kinetics or a second biological geometry.
-- The 54 source-native column-zero certificates come from the prior
-- BH4OriginalNative369IncidenceExact owner; no synthetic bond list.
--
-- Proof source only until Agda 2.9 acceptance.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import NonReflectiveQ as Solver
import DASHI.Biology.Molecular.BH4OriginalNative369IncidenceExact as Native
import DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact as Op
import DASHI.Biology.Molecular.BH4RationalFiniteFubiniExact as Fubini
import DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact as Lift

-- Generic lookup lemmas avoid treating symbolic Fin indices as literals.
lookupZipAdd :
  ∀ {n} (a b : V.Vec Q.ℚᵘ n) (j : F.Fin n) →
  V.lookup (V.zipWith Q._+_ a b) j ≡
  Q._+_ (V.lookup a j) (V.lookup b j)
lookupZipAdd V.[] V.[] ()
lookupZipAdd (V._∷_ a as) (V._∷_ b bs) F.zero = refl
lookupZipAdd (V._∷_ a as) (V._∷_ b bs) (F.suc j) =
  lookupZipAdd as bs j

lookupReplicateZero :
  ∀ {n} (j : F.Fin n) →
  Q._≃_
    (V.lookup (V.replicate {n = n} Q.0ℚᵘ) j)
    Q.0ℚᵘ
lookupReplicateZero F.zero = QP.≃-refl
lookupReplicateZero (F.suc j) = lookupReplicateZero j

-- The sitewise column sum is the direct, same-order finite sum
-- of the selected original bond coefficient at every site.
columnTotalsAreIndexedSiteSums :
  ∀ {sites bonds}
  (rows : V.Vec (V.Vec Q.ℚᵘ bonds) sites)
  (bond : F.Fin bonds) →
  Q._≃_
    (V.lookup (Fubini.qColumnTotals rows) bond)
    (Lift.rationalFiniteSum
      (V.map (λ row → V.lookup row bond) rows))
columnTotalsAreIndexedSiteSums V.[] bond =
  lookupReplicateZero bond
columnTotalsAreIndexedSiteSums (V._∷_ row rest) bond =
  QP.≃-trans
    (QP.≃-reflexive
      (lookupZipAdd row (Fubini.qColumnTotals rest) bond))
    (QP.+-cong
      QP.≃-refl
      (columnTotalsAreIndexedSiteSums rest bond))

-- Rational dot is additive in its first finite argument.
dotAdditiveFirst :
  ∀ {n}
  (a b currents : V.Vec Q.ℚᵘ n) →
  Q._≃_
    (Op.rationalDot (V.zipWith Q._+_ a b) currents)
    (Q._+_ (Op.rationalDot a currents)
           (Op.rationalDot b currents))
dotAdditiveFirst V.[] V.[] V.[] =
  QP.≃-sym (QP.+-identityˡ Q.0ℚᵘ)
dotAdditiveFirst
  (V._∷_ a as) (V._∷_ b bs) (V._∷_ j js) =
  QP.≃-trans
    (QP.+-cong QP.≃-refl (dotAdditiveFirst as bs js))
    (let open Solver in
     solve 5
       (λ a′ b′ j′ restA restB →
         ((a′ ⊕ b′) ⊗ j′) ⊕ (restA ⊕ restB)
         ⊜ ((a′ ⊗ j′) ⊕ restA) ⊕ ((b′ ⊗ j′) ⊕ restB))
       QP.≃-refl a b j
       (Op.rationalDot as js) (Op.rationalDot bs js))

sumRowDots :
  ∀ {sites bonds}
  (rows : V.Vec (V.Vec Q.ℚᵘ bonds) sites)
  (currents : V.Vec Q.ℚᵘ bonds) → Q.ℚᵘ
sumRowDots V.[] currents = Q.0ℚᵘ
sumRowDots (V._∷_ row rest) currents =
  Q._+_ (Op.rationalDot row currents)
         (sumRowDots rest currents)

dotZeroCoefficients :
  ∀ {n} (currents : V.Vec Q.ℚᵘ n) →
  Q._≃_
    (Op.rationalDot (V.replicate {n = n} Q.0ℚᵘ) currents)
    Q.0ℚᵘ
dotZeroCoefficients V.[] = QP.≃-refl
dotZeroCoefficients (V._∷_ j js) =
  QP.≃-trans
    (QP.+-cong
      (let open Solver in
       solve 1
         (λ j′ → (Κ Q.0ℚᵘ ⊗ j′) ⊜ Κ Q.0ℚᵘ)
         QP.≃-refl j)
      (dotZeroCoefficients js))
    (QP.+-identityˡ Q.0ℚᵘ)

sumRowDotsEqualsColumnDot :
  ∀ {sites bonds}
  (rows : V.Vec (V.Vec Q.ℚᵘ bonds) sites)
  (currents : V.Vec Q.ℚᵘ bonds) →
  Q._≃_
    (sumRowDots rows currents)
    (Op.rationalDot (Fubini.qColumnTotals rows) currents)
sumRowDotsEqualsColumnDot V.[] currents =
  QP.≃-sym (dotZeroCoefficients currents)
sumRowDotsEqualsColumnDot (V._∷_ row rest) currents =
  QP.≃-trans
    (QP.+-cong QP.≃-refl
      (sumRowDotsEqualsColumnDot rest currents))
    (QP.≃-sym (dotAdditiveFirst row
      (Fubini.qColumnTotals rest) currents))

dotCongLeft :
  ∀ {n} (a b currents : V.Vec Q.ℚᵘ n) →
  ((index : F.Fin n) →
    Q._≃_ (V.lookup a index) (V.lookup b index)) →
  Q._≃_ (Op.rationalDot a currents)
         (Op.rationalDot b currents)
dotCongLeft V.[] V.[] V.[] same = QP.≃-refl
dotCongLeft (V._∷_ a as) (V._∷_ b bs)
  (V._∷_ j js) same =
  QP.+-cong
    (QP.*-cong (same F.zero) QP.≃-refl)
    (dotCongLeft as bs js (λ k → same (F.suc k)))

-- Source-specific theorem. It uses all 54 original literal column
-- certificates rather than admitting 54 fake source zeros as fields.
original54NativeRationalTransportTotalZero :
  (currents : V.Vec Q.ℚᵘ 54) →
  Q._≃_
    (sumRowDots Native.sourceNativeIncidence currents)
    Q.0ℚᵘ
original54NativeRationalTransportTotalZero currents =
  QP.≃-trans
    (sumRowDotsEqualsColumnDot
      Native.sourceNativeIncidence currents)
    (QP.≃-trans
      (dotCongLeft
        (Fubini.qColumnTotals Native.sourceNativeIncidence)
        (V.replicate {n = 54} Q.0ℚᵘ)
        currents
        (λ bond → QP.≃-trans
          (columnTotalsAreIndexedSiteSums
            Native.sourceNativeIncidence bond)
          (Native.sourceNativeColumnZero bond)))
      (dotZeroCoefficients currents))

-- Actual original native incidence, all 29 species and 54 currents;
-- each species has its own arbitrary rational current vector.
original369AllSpeciesNativeRationalTransportZero :
  (fluxes : Op.Matrix 54 29) →
  (species : F.Fin 29) →
  Q._≃_
    (sumRowDots Native.sourceNativeIncidence
      (Op.rationalColumn fluxes species))
    Q.0ℚᵘ
original369AllSpeciesNativeRationalTransportZero fluxes species =
  original54NativeRationalTransportTotalZero
    (Op.rationalColumn fluxes species)


------------------------------------------------------------------------
-- The selected original-native incidence is the SAME operator that
-- produces the transport part of the 783-coordinate computed RHS.
------------------------------------------------------------------------

import DASHI.Biology.Molecular.BH4ComputedRationalSixDefectCompositionExact
  as Compose
import Real as BishopReal
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Embed

lookupMapExact :
  ∀ {n} {A B : Set}
  (f : A → B) (xs : V.Vec A n) (i : F.Fin n) →
  V.lookup (V.map f xs) i ≡ f (V.lookup xs i)
lookupMapExact f V.[] ()
lookupMapExact f (V._∷_ x xs) F.zero = refl
lookupMapExact f (V._∷_ x xs) (F.suc i) =
  lookupMapExact f xs i

vecExtensional :
  ∀ {n} {A : Set}
  (xs ys : V.Vec A n) →
  ((i : F.Fin n) → V.lookup xs i ≡ V.lookup ys i) →
  xs ≡ ys
vecExtensional V.[] V.[] same = refl
vecExtensional (V._∷_ x xs) (V._∷_ y ys) same =
  cong₂ V._∷_
    (same F.zero)
    (vecExtensional xs ys (λ j → same (F.suc j)))

-- Input dimensions are unchanged; chemistry/rate vectors do not enter
-- the native closed-mass transport term.
nativeComputedTransportColumnIsOriginalIncidenceDot :
  (fluxes : Op.Matrix 54 29)
  (stoichiometry : Op.Matrix 29 12)
  (rates : Op.Matrix 27 12)
  (species : F.Fin 29) →
  V.map (λ row → V.lookup row species)
    (Compose.originalTransportRHS
      (Native.originalNativeRationalInputs fluxes stoichiometry rates))
  ≡
  V.map
    (λ incidenceRow →
      Op.rationalDot incidenceRow (Op.rationalColumn fluxes species))
    Native.sourceNativeIncidence
nativeComputedTransportColumnIsOriginalIncidenceDot
  fluxes stoichiometry rates species =
  vecExtensional
    (V.map (λ row → V.lookup row species)
      (Compose.originalTransportRHS
        (Native.originalNativeRationalInputs fluxes stoichiometry rates)))
    (V.map
      (λ row → Op.rationalDot row (Op.rationalColumn fluxes species))
      Native.sourceNativeIncidence)
    λ site →
      trans
        (lookupMapExact
          (λ row → V.lookup row species)
          (Compose.originalTransportRHS
            (Native.originalNativeRationalInputs
              fluxes stoichiometry rates))
          site)
        (trans
          (cong (λ row → V.lookup row species)
            (Op.lookupTabulateExact
              (λ site′ →
                V.tabulate (λ species′ →
                  Op.bondContribution
                    (Native.originalNativeRationalInputs
                      fluxes stoichiometry rates)
                    site′ species′))
              site))
          (trans
            (Op.lookupTabulateExact
              (λ species′ →
                Op.bondContribution
                  (Native.originalNativeRationalInputs
                    fluxes stoichiometry rates)
                  site species′)
              species)
            (sym (lookupMapExact
              (λ row →
                Op.rationalDot row
                  (Op.rationalColumn fluxes species))
              Native.sourceNativeIncidence site))))

-- This is the FIRST actually source-owned local receipt field:
-- per-species 27-site transport cancellation for arbitrary original
-- signed rational currents, from the exact original incidence.
originalComputedNativeTransportPerSpeciesZero :
  (fluxes : Op.Matrix 54 29)
  (stoichiometry : Op.Matrix 29 12)
  (rates : Op.Matrix 27 12)
  (species : F.Fin 29) →
  Q._≃_
    (V.lookup
      (Fubini.qColumnTotals
        (Compose.originalTransportRHS
          (Native.originalNativeRationalInputs
            fluxes stoichiometry rates)))
      species)
    Q.0ℚᵘ
originalComputedNativeTransportPerSpeciesZero
  fluxes stoichiometry rates species =
  QP.≃-trans
    (columnTotalsAreIndexedSiteSums
      (Compose.originalTransportRHS
        (Native.originalNativeRationalInputs
          fluxes stoichiometry rates))
      species)
    (QP.≃-trans
      (QP.≃-reflexive
        (cong Lift.rationalFiniteSum
          (nativeComputedTransportColumnIsOriginalIncidenceDot
            fluxes stoichiometry rates species)))
      (original369AllSpeciesNativeRationalTransportZero
        fluxes species))


-- Native transport is now INHABITED by original source geometry.
-- Only the original finite reaction source left kernel remains to
-- inhabit the other field of the original local-conservation record.
originalNativeLocalConservationFromReactionProof :
  (fluxes : Op.Matrix 54 29)
  (stoichiometry : Op.Matrix 29 12)
  (rates : Op.Matrix 27 12)
  (weights : Op.Matrix 6 29) →
  ((axis : F.Fin 6) →
    Q._≃_
      (Lift.sourceSpatialWeighted
        (V.lookup weights axis)
        (Compose.originalReactionRHS
          (Native.originalNativeRationalInputs
            fluxes stoichiometry rates)))
      Q.0ℚᵘ) →
  Compose.OriginalSourceLocalConservation
    (Native.originalNativeRationalInputs fluxes stoichiometry rates)
    weights
originalNativeLocalConservationFromReactionProof
  fluxes stoichiometry rates weights reactionsBalanced =
  record
    { originalNativeTransportPerSpeciesZero =
        originalComputedNativeTransportPerSpeciesZero
          fluxes stoichiometry rates
    ; originalSourceReactionPerAxisZero = reactionsBalanced
    }

-- Consequent all-six-axes Bishop real conservation for the SAME
-- computed source-native 27×29 RHS. No global zero premise is assumed.
-- The remaining reaction-only proof must be independently source-paid.
originalNativeRHSSixRationalZeroGivenReactionSource :
  (fluxes : Op.Matrix 54 29)
  (stoichiometry : Op.Matrix 29 12)
  (rates : Op.Matrix 27 12)
  (weights : Op.Matrix 6 29) →
  ((axis : F.Fin 6) →
    Q._≃_
      (Lift.sourceSpatialWeighted
        (V.lookup weights axis)
        (Compose.originalReactionRHS
          (Native.originalNativeRationalInputs
            fluxes stoichiometry rates)))
      Q.0ℚᵘ) →
  (axis : F.Fin 6) →
  Q._≃_
    (Lift.sourceSpatialWeighted
      (V.lookup weights axis)
      (Op.rational369SemidiscreteRHS
        (Native.originalNativeRationalInputs
          fluxes stoichiometry rates)))
    Q.0ℚᵘ
originalNativeRHSSixRationalZeroGivenReactionSource
  fluxes stoichiometry rates weights reactionsBalanced =
  Compose.originalComputedRHSSixZeroDefects
    (Native.originalNativeRationalInputs
      fluxes stoichiometry rates)
    weights
    (originalNativeLocalConservationFromReactionProof
      fluxes stoichiometry rates weights reactionsBalanced)

-- Correct real-setoid consequence. Same original native incidence,
-- same arbitrary fluxes/rates, same original reaction source obligation.
originalNativeRHSSixBishopZeroGivenReactionSource :
  (fluxes : Op.Matrix 54 29)
  (stoichiometry : Op.Matrix 29 12)
  (rates : Op.Matrix 27 12)
  (weights : Op.Matrix 6 29) →
  ((axis : F.Fin 6) →
    Q._≃_
      (Lift.sourceSpatialWeighted
        (V.lookup weights axis)
        (Compose.originalReactionRHS
          (Native.originalNativeRationalInputs
            fluxes stoichiometry rates)))
      Q.0ℚᵘ) →
  (axis : F.Fin 6) →
  BishopReal._≃_
    (Lift.bishopSpatialWeighted
      (V.map Embed.embed (V.lookup weights axis))
      (V.map (V.map Embed.embed)
        (Op.rational369SemidiscreteRHS
          (Native.originalNativeRationalInputs
            fluxes stoichiometry rates))))
    (Embed.embed Q.0ℚᵘ)
originalNativeRHSSixBishopZeroGivenReactionSource
  fluxes stoichiometry rates weights reactionsBalanced =
  Compose.originalComputedRHSSixBishopConservation
    (Native.originalNativeRationalInputs
      fluxes stoichiometry rates)
    weights
    (originalNativeLocalConservationFromReactionProof
      fluxes stoichiometry rates weights reactionsBalanced)
