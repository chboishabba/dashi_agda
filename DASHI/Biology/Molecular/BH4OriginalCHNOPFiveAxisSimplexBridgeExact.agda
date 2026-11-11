module DASHI.Biology.Molecular.BH4OriginalCHNOPFiveAxisSimplexBridgeExact where

-- Exact five-axis CHNOP invariant for the original 27-site / 29-species /
-- 12-finite-reaction spatial source.  This reuses the existing source
-- certificate and RATE-WEIGHTED original stoichiometry proof, not a new
-- simplex or stoichiometric implementation.
--
-- Five nonnegative mass coordinates form an invariant finite accounting
-- chart.  They are NOT yet the compact real weighted simplex required
-- by Brouwer: positivity of the aggregate weight of all 29 species,
-- topology/compactness and an actual fixed-point theorem remain unpaid.
--
-- Original chemistry: Rhea/ChEBI, source-authenticated by separate owner.
-- DASHI's 369 material geometry and source matrix are pre-existing.
-- This is assistant-authored theorem composition, not measured kinetics.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F

import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Panel
import DASHI.Biology.Molecular.BH4PanelRateWeightedConservationExact as Rate

-- All five original CHNOP invariants for ONE SAME 27-site vector of
-- source-indexed reaction multiplicities.
record OriginalFiveAxisSpatialReactionBalance
    (certificate : Panel.SourceCertifiedOriginal29x12)
    (siteMultiplicities : V.Vec (V.Vec Nat 12) 27) : Set where
  field
    carbonConserved :
      Rate.spatialRateWeightedReactants
        (Panel.sourceElementWeights certificate Panel.carbonElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities
      ≡
      Rate.spatialRateWeightedProducts
        (Panel.sourceElementWeights certificate Panel.carbonElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities

    hydrogenConserved :
      Rate.spatialRateWeightedReactants
        (Panel.sourceElementWeights certificate Panel.hydrogenElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities
      ≡
      Rate.spatialRateWeightedProducts
        (Panel.sourceElementWeights certificate Panel.hydrogenElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities

    nitrogenConserved :
      Rate.spatialRateWeightedReactants
        (Panel.sourceElementWeights certificate Panel.nitrogenElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities
      ≡
      Rate.spatialRateWeightedProducts
        (Panel.sourceElementWeights certificate Panel.nitrogenElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities

    oxygenConserved :
      Rate.spatialRateWeightedReactants
        (Panel.sourceElementWeights certificate Panel.oxygenElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities
      ≡
      Rate.spatialRateWeightedProducts
        (Panel.sourceElementWeights certificate Panel.oxygenElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities

    phosphorusConserved :
      Rate.spatialRateWeightedReactants
        (Panel.sourceElementWeights certificate Panel.phosphorusElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities
      ≡
      Rate.spatialRateWeightedProducts
        (Panel.sourceElementWeights certificate Panel.phosphorusElement)
        (Panel.sourceFiniteColumns certificate) siteMultiplicities

open OriginalFiveAxisSpatialReactionBalance public

original369x29x12FiveAxisSpatialBalance :
  (certificate : Panel.SourceCertifiedOriginal29x12)
  (siteMultiplicities : V.Vec (V.Vec Nat 12) 27) →
  OriginalFiveAxisSpatialReactionBalance certificate siteMultiplicities
original369x29x12FiveAxisSpatialBalance certificate multiplicities = record
  { carbonConserved =
      Rate.original369x29x12SpatialRateCHNOPBalance
        certificate Panel.carbonElement multiplicities
  ; hydrogenConserved =
      Rate.original369x29x12SpatialRateCHNOPBalance
        certificate Panel.hydrogenElement multiplicities
  ; nitrogenConserved =
      Rate.original369x29x12SpatialRateCHNOPBalance
        certificate Panel.nitrogenElement multiplicities
  ; oxygenConserved =
      Rate.original369x29x12SpatialRateCHNOPBalance
        certificate Panel.oxygenElement multiplicities
  ; phosphorusConserved =
      Rate.original369x29x12SpatialRateCHNOPBalance
        certificate Panel.phosphorusElement multiplicities
  }

-- The original owner already yields EVERY source CHNOP coordinate,
-- rather than merely the selected carbon one. The five-coordinate
-- package is an application-specific consumer convenience.
original369x29x12EveryCHNOPBalance :
  (certificate : Panel.SourceCertifiedOriginal29x12)
  (multiplicities : V.Vec (V.Vec Nat 12) 27)
  (element : Panel.OriginalCHNOPElement) →
  Rate.spatialRateWeightedReactants
    (Panel.sourceElementWeights certificate element)
    (Panel.sourceFiniteColumns certificate) multiplicities
  ≡
  Rate.spatialRateWeightedProducts
    (Panel.sourceElementWeights certificate element)
    (Panel.sourceFiniteColumns certificate) multiplicities
original369x29x12EveryCHNOPBalance =
  Rate.original369x29x12SpatialRateCHNOPBalance

------------------------------------------------------------------------
-- The original Brouwer positive-weight simplex uses ONE aggregate mass
-- coordinate. Build it from the five source CHNOP coordinates; do not
-- invent a sixth chemical invariant or infer positivity from atom counts.
------------------------------------------------------------------------

panelWeightedAddWeights :
  ∀ {n} (left right counts : V.Vec Nat n) →
  Panel.panelWeighted (Panel.panelAdd left right) counts
    ≡ Panel.panelWeighted left counts + Panel.panelWeighted right counts
panelWeightedAddWeights V.[] V.[] V.[] = refl
panelWeightedAddWeights
  (V._∷_ a left) (V._∷_ b right) (V._∷_ count counts) =
  trans
    (cong (λ t → (a + b) * count + t)
      (panelWeightedAddWeights left right counts))
    (trans
      (cong (λ t → t +
        (Panel.panelWeighted left counts +
         Panel.panelWeighted right counts))
        (*-distribʳ-+ count a b))
      (Panel.panelShuffle
        (a * count) (b * count)
        (Panel.panelWeighted left counts)
        (Panel.panelWeighted right counts)))

combineOriginalLeftKernel :
  ∀ {n}
  (left right : V.Vec Nat n)
  (reaction : Panel.OriginalFiniteReaction n) →
  Panel.panelWeighted left (Panel.originalReactants reaction)
    ≡ Panel.panelWeighted left (Panel.originalProducts reaction) →
  Panel.panelWeighted right (Panel.originalReactants reaction)
    ≡ Panel.panelWeighted right (Panel.originalProducts reaction) →
  Panel.panelWeighted (Panel.panelAdd left right)
    (Panel.originalReactants reaction)
    ≡ Panel.panelWeighted (Panel.panelAdd left right)
      (Panel.originalProducts reaction)
combineOriginalLeftKernel left right reaction leftBalance rightBalance =
  trans
    (panelWeightedAddWeights left right
      (Panel.originalReactants reaction))
    (trans
      (cong₂ _+_ leftBalance rightBalance)
      (sym (panelWeightedAddWeights left right
        (Panel.originalProducts reaction))))

-- Build the original 29-component aggregate without assigning any
-- measured rates, source concentrations, or independent physiology.
totalCHNOPSourceWeights :
  (certificate : Panel.SourceCertifiedOriginal29x12) →
  V.Vec Nat 29
totalCHNOPSourceWeights certificate =
  Panel.panelAdd
    (Panel.sourceElementWeights certificate Panel.carbonElement)
    (Panel.panelAdd
      (Panel.sourceElementWeights certificate Panel.hydrogenElement)
      (Panel.panelAdd
        (Panel.sourceElementWeights certificate Panel.nitrogenElement)
        (Panel.panelAdd
          (Panel.sourceElementWeights certificate Panel.oxygenElement)
          (Panel.sourceElementWeights certificate Panel.phosphorusElement))))

sourceTotalCHNOPLeftKernel :
  (certificate : Panel.SourceCertifiedOriginal29x12)
  (column : F.Fin 12) →
  Panel.panelWeighted (totalCHNOPSourceWeights certificate)
    (Panel.originalReactants
      (V.lookup (Panel.sourceFiniteColumns certificate) column))
    ≡
  Panel.panelWeighted (totalCHNOPSourceWeights certificate)
    (Panel.originalProducts
      (V.lookup (Panel.sourceFiniteColumns certificate) column))
sourceTotalCHNOPLeftKernel certificate column =
  combineOriginalLeftKernel
    (Panel.sourceElementWeights certificate Panel.carbonElement)
    (Panel.panelAdd
      (Panel.sourceElementWeights certificate Panel.hydrogenElement)
      (Panel.panelAdd
        (Panel.sourceElementWeights certificate Panel.nitrogenElement)
        (Panel.panelAdd
          (Panel.sourceElementWeights certificate Panel.oxygenElement)
          (Panel.sourceElementWeights certificate Panel.phosphorusElement))))
    (V.lookup (Panel.sourceFiniteColumns certificate) column)
    (Panel.sourceColumnLeftKernel certificate Panel.carbonElement column)
    (combineOriginalLeftKernel
      (Panel.sourceElementWeights certificate Panel.hydrogenElement)
      (Panel.panelAdd
        (Panel.sourceElementWeights certificate Panel.nitrogenElement)
        (Panel.panelAdd
          (Panel.sourceElementWeights certificate Panel.oxygenElement)
          (Panel.sourceElementWeights certificate Panel.phosphorusElement)))
      (V.lookup (Panel.sourceFiniteColumns certificate) column)
      (Panel.sourceColumnLeftKernel certificate Panel.hydrogenElement column)
      (combineOriginalLeftKernel
        (Panel.sourceElementWeights certificate Panel.nitrogenElement)
        (Panel.panelAdd
          (Panel.sourceElementWeights certificate Panel.oxygenElement)
          (Panel.sourceElementWeights certificate Panel.phosphorusElement))
        (V.lookup (Panel.sourceFiniteColumns certificate) column)
        (Panel.sourceColumnLeftKernel certificate Panel.nitrogenElement column)
        (combineOriginalLeftKernel
          (Panel.sourceElementWeights certificate Panel.oxygenElement)
          (Panel.sourceElementWeights certificate Panel.phosphorusElement)
          (V.lookup (Panel.sourceFiniteColumns certificate) column)
          (Panel.sourceColumnLeftKernel certificate Panel.oxygenElement column)
          (Panel.sourceColumnLeftKernel certificate Panel.phosphorusElement column))))

-- This is the exact original 27-site x 12-column aggregate CHNOP
-- conservation used by a weighted-mass simplex, for arbitrary natural
-- reaction multiplicity at each site. The actual positive-species
-- hypothesis is deliberately NOT produced here.
original369x29x12AggregateCHNOPBalance :
  (certificate : Panel.SourceCertifiedOriginal29x12)
  (multiplicities : V.Vec (V.Vec Nat 12) 27) →
  Rate.spatialRateWeightedReactants
    (totalCHNOPSourceWeights certificate)
    (Panel.sourceFiniteColumns certificate) multiplicities
    ≡
  Rate.spatialRateWeightedProducts
    (totalCHNOPSourceWeights certificate)
    (Panel.sourceFiniteColumns certificate) multiplicities
original369x29x12AggregateCHNOPBalance certificate multiplicities =
  Rate.allSitesRateWeightedConserve
    (totalCHNOPSourceWeights certificate)
    (Panel.sourceFiniteColumns certificate) multiplicities
    (sourceTotalCHNOPLeftKernel certificate)

------------------------------------------------------------------------
-- Exact strict-positivity source seam for the original 29 molecular
-- species. The Rhea certificate provides CHNOP conservation but does
-- NOT, on its own, establish that every selected molecular species
-- contains at least one of those atoms. An electron-only carrier or a
-- source with an unresolved formula must not inhabit this witness.
--
-- A strictly positive Nat is given constructively as suc its
-- predecessor; this does not appeal to a floating-point threshold.
------------------------------------------------------------------------

record SourcePositiveAggregateCHNOP
    (certificate : Panel.SourceCertifiedOriginal29x12) : Set where
  field
    sourceWeightPositive :
      (species : F.Fin 29) →
      Σ Nat (λ predecessor →
        V.lookup (totalCHNOPSourceWeights certificate) species
          ≡ suc predecessor)

open SourcePositiveAggregateCHNOP public

record Original369PositiveWeightedSimplexAdmission : Set where
  constructor original369-positive-weighted-simplex-admission
  field
    originalSource : Panel.SourceCertifiedOriginal29x12
    positiveCHNOP : SourcePositiveAggregateCHNOP originalSource

open Original369PositiveWeightedSimplexAdmission public

-- The two actual admissibility obligations travel together: every
-- species weight is positive, and the SAME source column conserves the
-- aggregate weight. Neither a five-class colour simplex nor a
-- Nash mixed-strategy probability law is substituted for source data.
original369SimplexWeightAndLeftKernel :
  (admission : Original369PositiveWeightedSimplexAdmission)
  (species : F.Fin 29)
  (column : F.Fin 12) →
  (Σ Nat (λ predecessor →
    V.lookup (totalCHNOPSourceWeights (originalSource admission)) species
      ≡ suc predecessor))
  ×
  (Panel.panelWeighted
    (totalCHNOPSourceWeights (originalSource admission))
    (Panel.originalReactants
      (V.lookup
        (Panel.sourceFiniteColumns (originalSource admission))
        column))
    ≡
    Panel.panelWeighted
      (totalCHNOPSourceWeights (originalSource admission))
      (Panel.originalProducts
        (V.lookup
          (Panel.sourceFiniteColumns (originalSource admission))
          column)))
original369SimplexWeightAndLeftKernel admission species column =
  sourceWeightPositive (positiveCHNOP admission) species
  , sourceTotalCHNOPLeftKernel (originalSource admission) column

-- All 27 original sites share exactly the same admitted source and
-- positive weights; a different source or site-specific synthetic
-- stoichiometric matrix is not introduced.
original369PositiveSimplexAllSitesCHNOPInvariant :
  (admission : Original369PositiveWeightedSimplexAdmission)
  (multiplicities : V.Vec (V.Vec Nat 12) 27) →
  Rate.spatialRateWeightedReactants
    (totalCHNOPSourceWeights (originalSource admission))
    (Panel.sourceFiniteColumns (originalSource admission))
    multiplicities
  ≡
  Rate.spatialRateWeightedProducts
    (totalCHNOPSourceWeights (originalSource admission))
    (Panel.sourceFiniteColumns (originalSource admission))
    multiplicities
original369PositiveSimplexAllSitesCHNOPInvariant admission multiplicities =
  original369x29x12AggregateCHNOPBalance
    (originalSource admission) multiplicities

-- A zero-atom source species is an exact obstruction. The proof does
-- not rely on an empirical tolerance, an unproved generic positivity
-- axiom or a source reference string.
zeroCHNOPWeightBlocksPositiveSource :
  (certificate : Panel.SourceCertifiedOriginal29x12)
  (species : F.Fin 29) →
  V.lookup (totalCHNOPSourceWeights certificate) species ≡ 0 →
  SourcePositiveAggregateCHNOP certificate →
  ⊥
zeroCHNOPWeightBlocksPositiveSource certificate species zeroWeight positive
  with sourceWeightPositive positive species
... | predecessor , strictlyPositive =
  zeroIsNotSuccessor
    (trans (sym zeroWeight) strictlyPositive)
  where
    zeroIsNotSuccessor : ∀ {n} → 0 ≡ suc n → ⊥
    zeroIsNotSuccessor ()

------------------------------------------------------------------------
-- P0 computational completeness: decide source CHNOP positivity at
-- EVERY index, constructing evidence instead of admitting a string flag.
--
-- Unlike the missing generated Rhea source, this is fully generic and
-- constructive over the existing Vec/Fin/Nat proof carriers.
-- The right branch supplies a concrete index whose source weight is
-- exactly zero and therefore blocks positive-simplex admission.
------------------------------------------------------------------------

positiveNatOrZero :
  (weight : Nat) →
  (Σ Nat (λ predecessor → weight ≡ suc predecessor))
    ⊎ (weight ≡ 0)
positiveNatOrZero zero = inj₂ refl
positiveNatOrZero (suc predecessor) =
  inj₁ (predecessor , refl)

allPositiveOrZeroIndex :
  ∀ {n}
  (weights : V.Vec Nat n) →
  ((species : F.Fin n) →
     Σ Nat (λ predecessor →
       V.lookup weights species ≡ suc predecessor))
  ⊎
  (Σ (F.Fin n) (λ species → V.lookup weights species ≡ 0))
allPositiveOrZeroIndex V.[] = inj₁ (λ ())
allPositiveOrZeroIndex (V._∷_ weight weights)
  with positiveNatOrZero weight
... | inj₂ isZero = inj₂ (F.zero , isZero)
... | inj₁ positive with allPositiveOrZeroIndex weights
...   | inj₁ allTailPositive =
        inj₁ λ { F.zero → positive
               ; (F.suc species) → allTailPositive species }
...   | inj₂ (species , isZero) =
        inj₂ (F.suc species , isZero)

-- The source certificate alone need not imply positivity. Nevertheless
-- EVERY inhabitable original source certificate has an exact decidable
-- outcome: a complete positive-weight witness or an explicit zero
-- species obstruction, with no excluded middle or fake source data.
decideOriginal369SourcePositiveCHNOP :
  (certificate : Panel.SourceCertifiedOriginal29x12) →
  SourcePositiveAggregateCHNOP certificate
    ⊎
  (Σ (F.Fin 29)
    (λ species →
      V.lookup (totalCHNOPSourceWeights certificate) species ≡ 0))
decideOriginal369SourcePositiveCHNOP certificate
  with allPositiveOrZeroIndex (totalCHNOPSourceWeights certificate)
... | inj₁ everyPositive =
      inj₁ record { sourceWeightPositive = everyPositive }
... | inj₂ obstruction = inj₂ obstruction

-- Once the generated original source is available, the success branch
-- supplies the SAME PNP simplex admission without asking a researcher
-- to manually fill in 29 positivity proofs.
decideOriginal369WeightedSimplexAdmission :
  (certificate : Panel.SourceCertifiedOriginal29x12) →
  Original369PositiveWeightedSimplexAdmission
    ⊎
  (Σ (F.Fin 29)
    (λ species →
      V.lookup (totalCHNOPSourceWeights certificate) species ≡ 0))
decideOriginal369WeightedSimplexAdmission certificate
  with decideOriginal369SourcePositiveCHNOP certificate
... | inj₁ evidence =
      inj₁ (original369-positive-weighted-simplex-admission
              certificate evidence)
... | inj₂ obstruction = inj₂ obstruction

------------------------------------------------------------------------
-- Genuine decidability of the exact original-source positive-weight
-- proposition. The negative result is a contradiction function for
-- THAT SAME source certificate, rather than an unattached zero label.
------------------------------------------------------------------------

decideOriginal369SourcePositiveCHNOPWithRefutation :
  (certificate : Panel.SourceCertifiedOriginal29x12) →
  SourcePositiveAggregateCHNOP certificate
    ⊎ (SourcePositiveAggregateCHNOP certificate → ⊥)
decideOriginal369SourcePositiveCHNOPWithRefutation certificate
  with decideOriginal369SourcePositiveCHNOP certificate
... | inj₁ witness = inj₁ witness
... | inj₂ (species , zeroWeight) =
  inj₂ (zeroCHNOPWeightBlocksPositiveSource
    certificate species zeroWeight)

-- If the source already supplies an explicit positive witness, a
-- zero coordinate is impossible. Unlike a cached Boolean, this proof
-- works for every selected 29x12 source inhabitant.
positiveOriginalSourceExcludesEveryZeroCoordinate :
  (certificate : Panel.SourceCertifiedOriginal29x12) →
  SourcePositiveAggregateCHNOP certificate →
  (species : F.Fin 29) →
  V.lookup (totalCHNOPSourceWeights certificate) species ≡ 0 →
  ⊥
positiveOriginalSourceExcludesEveryZeroCoordinate certificate
  witness species zeroWeight =
  zeroCHNOPWeightBlocksPositiveSource
    certificate species zeroWeight witness
