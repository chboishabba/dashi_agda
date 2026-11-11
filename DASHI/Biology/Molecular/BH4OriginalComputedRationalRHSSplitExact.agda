module DASHI.Biology.Molecular.BH4OriginalComputedRationalRHSSplitExact where

-- Exact finite source/transport decomposition for the *existing*
-- 783-coordinate BH4 original semidiscrete rational RHS, in the
-- SAME 27×54 geometry, 29×12 stoichiometric chart and Bishop
-- rational-to-real consumer. No duplicate physical operator.
--
-- The proof derives a computed-RHS six-axis global zero from
-- (1) per-species transport cancellation over all 27 sites and
-- (2) per-axis reaction neutrality over those 27 sites.
-- These are STRICTLY WEAKER inputs than an arbitrary six-axis
-- global-zero receipt and are the actual incidence/stoichiometry
-- proof seams left to close.
--
-- No Agda kernel receipt until checked in user's Nix/Agda setup.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import Real as R
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Embed
import DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact as Operator
import DASHI.Biology.Molecular.BH4RationalFiniteFubiniExact as Fubini
import DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact as Lift

-- The selected pre-existing operator is the single meaning of every
-- finite bond and reaction coordinate of these matrices.
originalBondRows : Operator.Rational369SemidiscreteInputs →
  Operator.Matrix 27 29
originalBondRows inputs =
  V.tabulate (λ site →
    V.tabulate (Operator.bondContribution inputs site))

originalReactionRows : Operator.Rational369SemidiscreteInputs →
  Operator.Matrix 27 29
originalReactionRows inputs =
  V.tabulate (λ site →
    V.tabulate (Operator.reactionContribution inputs site))

-- Lookup-after-tabulation is NOT definitionally reflexive for an
-- arbitrary symbolic Fin index. Reuse the exact lemma already proved
-- by the canonical rational operator for both site and species.
originalBondAt :
  (inputs : Operator.Rational369SemidiscreteInputs)
  (site : F.Fin 27) (species : F.Fin 29) →
  V.lookup (V.lookup (originalBondRows inputs) site) species
    ≡ Operator.bondContribution inputs site species
originalBondAt inputs site species =
  trans
    (cong (λ row → V.lookup row species)
      (Operator.lookupTabulateExact
        (λ site′ → V.tabulate
          (Operator.bondContribution inputs site′)) site))
    (Operator.lookupTabulateExact
      (Operator.bondContribution inputs site) species)

originalReactionAt :
  (inputs : Operator.Rational369SemidiscreteInputs)
  (site : F.Fin 27) (species : F.Fin 29) →
  V.lookup (V.lookup (originalReactionRows inputs) site) species
    ≡ Operator.reactionContribution inputs site species
originalReactionAt inputs site species =
  trans
    (cong (λ row → V.lookup row species)
      (Operator.lookupTabulateExact
        (λ site′ → V.tabulate
          (Operator.reactionContribution inputs site′)) site))
    (Operator.lookupTabulateExact
      (Operator.reactionContribution inputs site) species)

originalRHSPointwiseSplits :
  (inputs : Operator.Rational369SemidiscreteInputs)
  (site : F.Fin 27) (species : F.Fin 29) →
  Q._≃_
    (V.lookup (V.lookup (Operator.rational369SemidiscreteRHS inputs) site) species)
    (Q._+_
      (V.lookup (V.lookup (originalBondRows inputs) site) species)
      (V.lookup (V.lookup (originalReactionRows inputs) site) species))
originalRHSPointwiseSplits inputs site species =
  QP.≃-reflexive
    (trans
      (Operator.rational369SemidiscreteAt inputs site species)
      (sym (cong₂ Q._+_
        (originalBondAt inputs site species)
        (originalReactionAt inputs site species))))

-- Generic Vec.zipWith index identity; necessary because symbolic
-- Fin indices do not normalize by bare refl.
lookupZipWith :
  ∀ {n A B C : Set}
  (combine : A → B → C)
  (left : V.Vec A n) (right : V.Vec B n)
  (index : F.Fin n) →
  V.lookup (V.zipWith combine left right) index
    ≡ combine (V.lookup left index) (V.lookup right index)
lookupZipWith combine V.[] V.[] ()
lookupZipWith combine
  (V._∷_ left restLeft) (V._∷_ right restRight) F.zero = refl
lookupZipWith combine
  (V._∷_ left restLeft) (V._∷_ right restRight) (F.suc index) =
  lookupZipWith combine restLeft restRight index

lookupMatrixAddAt :
  ∀ {sites species}
  (left right : V.Vec (V.Vec Q.ℚᵘ species) sites)
  (site : F.Fin sites) (sp : F.Fin species) →
  V.lookup
    (V.lookup (V.zipWith (V.zipWith Q._+_) left right) site)
    sp
    ≡
  Q._+_ (V.lookup (V.lookup left site) sp)
        (V.lookup (V.lookup right site) sp)
lookupMatrixAddAt left right site sp =
  trans
    (cong (λ row → V.lookup row sp)
      (lookupZipWith (V.zipWith Q._+_) left right site))
    (lookupZipWith Q._+_ (V.lookup left site) (V.lookup right site) sp)

-- Original weighted spatial sum is pointwise-congruent, rather than
-- using propositional equality on unnormalised rational values.
qSpatialWeightedCong :
  ∀ {sites species}
  (weights : V.Vec Q.ℚᵘ species)
  (left right : V.Vec (V.Vec Q.ℚᵘ species) sites) →
  ((site : F.Fin sites) (sp : F.Fin species) →
    Q._≃_
      (V.lookup (V.lookup left site) sp)
      (V.lookup (V.lookup right site) sp)) →
  Q._≃_
    (Lift.sourceSpatialWeighted weights left)
    (Lift.sourceSpatialWeighted weights right)
qSpatialWeightedCong weights V.[] V.[] same = QP.≃-refl
qSpatialWeightedCong weights
  (V._∷_ row rows) (V._∷_ other remaining) same =
  QP.+-cong
    (Fubini.qWeightedDotCong weights row other
      (λ species → same F.zero species))
    (qSpatialWeightedCong weights rows remaining
      (λ site species → same (F.suc site) species))

qSpatialWeightedAdd :
  ∀ {sites species}
  (weights : V.Vec Q.ℚᵘ species)
  (left right : V.Vec (V.Vec Q.ℚᵘ species) sites) →
  Q._≃_
    (Lift.sourceSpatialWeighted weights
      (V.zipWith (V.zipWith Q._+_) left right))
    (Q._+_
      (Lift.sourceSpatialWeighted weights left)
      (Lift.sourceSpatialWeighted weights right))
qSpatialWeightedAdd weights V.[] V.[] =
  QP.≃-sym (QP.+-identityˡ Q.0ℚᵘ)
qSpatialWeightedAdd weights
  (V._∷_ row rows) (V._∷_ other rest) =
  QP.≃-trans
    (QP.+-cong
      (Fubini.qWeightedRowAdd weights row other)
      (qSpatialWeightedAdd weights rows rest))
    (Fubini.qShuffle
      (Lift.sourceWeightedRow weights row)
      (Lift.sourceWeightedRow weights other)
      (Lift.sourceSpatialWeighted weights rows)
      (Lift.sourceSpatialWeighted weights rest))

-- Lookup in the componentwise source+transport row is the same
-- symbolic rational term as the existing operator's exact pointwise
-- RHS, under ordinary propositional equality (for the finite Vec
-- constructors, not for unrelated unnormalised rational numerators).
originalRHSSplitLookup :
  (inputs : Operator.Rational369SemidiscreteInputs)
  (site : F.Fin 27) (species : F.Fin 29) →
  Q._≃_
    (V.lookup (V.lookup (Operator.rational369SemidiscreteRHS inputs)
      site) species)
    (V.lookup
      (V.lookup
        (V.zipWith (V.zipWith Q._+_)
          (originalBondRows inputs)
          (originalReactionRows inputs))
        site) species)
originalRHSSplitLookup inputs site species =
  QP.≃-trans
    (originalRHSPointwiseSplits inputs site species)
    (QP.≃-sym
      (QP.≃-reflexive
        (lookupMatrixAddAt
          (originalBondRows inputs) (originalReactionRows inputs)
          site species)))

originalComputedRHSWeightedSplits :
  (inputs : Operator.Rational369SemidiscreteInputs)
  (weights : V.Vec Q.ℚᵘ 29) →
  Q._≃_
    (Lift.sourceSpatialWeighted weights
      (Operator.rational369SemidiscreteRHS inputs))
    (Q._+_
      (Lift.sourceSpatialWeighted weights (originalBondRows inputs))
      (Lift.sourceSpatialWeighted weights (originalReactionRows inputs)))
originalComputedRHSWeightedSplits inputs weights =
  QP.≃-trans
    (qSpatialWeightedCong weights
      (Operator.rational369SemidiscreteRHS inputs)
      (V.zipWith (V.zipWith Q._+_)
        (originalBondRows inputs)
        (originalReactionRows inputs))
      (originalRHSSplitLookup inputs))
    (qSpatialWeightedAdd weights
      (originalBondRows inputs) (originalReactionRows inputs))

-- No six-axis global zero hypothesis here. The transport obligation
-- is per SPECIES; the reaction obligation is per original SOURCE AXIS.
-- These are the precise outputs needed from the finite native incidence
-- and same-source stoichiometric rational generator, respectively.
originalComputedSixAxisZeroFromLocal :
  (inputs : Operator.Rational369SemidiscreteInputs)
  (weights : Operator.Matrix 6 29) →
  ((species : F.Fin 29) →
    Q._≃_
      (V.lookup (Fubini.qColumnTotals (originalBondRows inputs)) species)
      Q.0ℚᵘ) →
  ((axis : F.Fin 6) →
    Q._≃_
      (Lift.sourceSpatialWeighted
        (V.lookup weights axis) (originalReactionRows inputs))
      Q.0ℚᵘ) →
  (axis : F.Fin 6) →
  Q._≃_
    (Lift.sourceSpatialWeighted
      (V.lookup weights axis)
      (Operator.rational369SemidiscreteRHS inputs))
    Q.0ℚᵘ
originalComputedSixAxisZeroFromLocal
  inputs weights nativePerSpeciesZero reactionsZero axis =
  QP.≃-trans
    (originalComputedRHSWeightedSplits inputs (V.lookup weights axis))
    (QP.≃-trans
      (QP.+-cong
        (Fubini.qWeightedColumnZeroImpliesSpatialZero
          (V.lookup weights axis)
          (originalBondRows inputs) nativePerSpeciesZero)
        (reactionsZero axis))
      (QP.+-identityˡ Q.0ℚᵘ))

-- The existing rational-to-Bishop six-axis consumer is now fed from
-- the derived *local* producer, not from a prescribed global defect.
originalComputedSixAxisBishopFromLocal :
  (inputs : Operator.Rational369SemidiscreteInputs)
  (weights : Operator.Matrix 6 29) →
  ((species : F.Fin 29) →
    Q._≃_
      (V.lookup (Fubini.qColumnTotals (originalBondRows inputs)) species)
      Q.0ℚᵘ) →
  ((axis : F.Fin 6) →
    Q._≃_
      (Lift.sourceSpatialWeighted
        (V.lookup weights axis) (originalReactionRows inputs))
      Q.0ℚᵘ) →
  (axis : F.Fin 6) →
  R._≃_
    (Lift.bishopSpatialWeighted
      (V.map Embed.embed (V.lookup weights axis))
      (V.map (V.map Embed.embed)
        (Operator.rational369SemidiscreteRHS inputs)))
    (Embed.embed Q.0ℚᵘ)
originalComputedSixAxisBishopFromLocal
  inputs weights nativePerSpeciesZero reactionsZero =
  Operator.computedRationalRHSConservationLiftsToBishop
    inputs weights
    (originalComputedSixAxisZeroFromLocal
      inputs weights nativePerSpeciesZero reactionsZero)
