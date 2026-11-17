module DASHI.Biology.Molecular.BH4PanelRateWeightedConservationExact where

-- P0.04 finite-panel extension: simultaneous nonnegative integer reaction
-- multiplicities preserve every certified left-kernel coordinate.
--
-- Source attribution: the selected 29x12 Rhea matrix and all charge/CHNOP
-- identities are supplied by the existing SourceCertifiedOriginal29x12 owner.
-- This proof is conditional on that actual certificate. Its Nat-valued
-- multiplicities are NOT measured reaction rates or a mass-action ODE.
--
-- The formal extension is assistant-authored implementation assistance
-- over the user's existing BH4/369 stoichiometric programme.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Panel

------------------------------------------------------------------------
-- Sum over simultaneously fired, source-indexed finite columns.
------------------------------------------------------------------------

rateWeightedReactants :
  ∀ {n r} →
  V.Vec Nat n →
  V.Vec (Panel.OriginalFiniteReaction n) r →
  V.Vec Nat r → Nat
rateWeightedReactants weights V.[] V.[] = 0
rateWeightedReactants weights (V._∷_ reaction reactions)
  (V._∷_ multiplicity multiplicities) =
  multiplicity * Panel.panelWeighted weights
    (Panel.originalReactants reaction)
  + rateWeightedReactants weights reactions multiplicities

rateWeightedProducts :
  ∀ {n r} →
  V.Vec Nat n →
  V.Vec (Panel.OriginalFiniteReaction n) r →
  V.Vec Nat r → Nat
rateWeightedProducts weights V.[] V.[] = 0
rateWeightedProducts weights (V._∷_ reaction reactions)
  (V._∷_ multiplicity multiplicities) =
  multiplicity * Panel.panelWeighted weights
    (Panel.originalProducts reaction)
  + rateWeightedProducts weights reactions multiplicities

-- Every certified column may occur any natural number of times.
-- This is the linear algebra S*k in its Nat-valued reactant/product
-- encoding, avoiding fictitious subtraction of unavailable molecules.
allFiniteColumnsRateWeightedConserve :
  ∀ {n r}
  (weights : V.Vec Nat n)
  (reactions : V.Vec (Panel.OriginalFiniteReaction n) r)
  (multiplicities : V.Vec Nat r) →
  ((column : F.Fin r) →
    Panel.panelWeighted weights
      (Panel.originalReactants (V.lookup reactions column))
      ≡ Panel.panelWeighted weights
        (Panel.originalProducts (V.lookup reactions column))) →
  rateWeightedReactants weights reactions multiplicities
    ≡ rateWeightedProducts weights reactions multiplicities
allFiniteColumnsRateWeightedConserve weights V.[] V.[] balanced = refl
allFiniteColumnsRateWeightedConserve weights
  (V._∷_ reaction reactions)
  (V._∷_ multiplicity multiplicities) balanced =
  cong₂ _+_
    (cong (λ total → multiplicity * total) (balanced F.zero))
    (allFiniteColumnsRateWeightedConserve weights reactions
      multiplicities (λ column → balanced (F.suc column)))

------------------------------------------------------------------------
-- Signed-charge cross-sums; neither sign is conserved independently.
------------------------------------------------------------------------

allFiniteColumnsRateWeightedSignedConserve :
  ∀ {n r}
  (positiveWeights negativeWeights : V.Vec Nat n)
  (reactions : V.Vec (Panel.OriginalFiniteReaction n) r)
  (multiplicities : V.Vec Nat r) →
  ((column : F.Fin r) →
    (Panel.panelWeighted positiveWeights
      (Panel.originalReactants (V.lookup reactions column))
      + Panel.panelWeighted negativeWeights
        (Panel.originalProducts (V.lookup reactions column)))
    ≡
    (Panel.panelWeighted positiveWeights
      (Panel.originalProducts (V.lookup reactions column))
      + Panel.panelWeighted negativeWeights
        (Panel.originalReactants (V.lookup reactions column)))) →
  (rateWeightedReactants positiveWeights reactions multiplicities
    + rateWeightedProducts negativeWeights reactions multiplicities)
    ≡
  (rateWeightedProducts positiveWeights reactions multiplicities
    + rateWeightedReactants negativeWeights reactions multiplicities)
allFiniteColumnsRateWeightedSignedConserve positiveWeights
  negativeWeights V.[] V.[] balanced = refl
allFiniteColumnsRateWeightedSignedConserve positiveWeights
  negativeWeights (V._∷_ reaction reactions)
  (V._∷_ multiplicity multiplicities) balanced =
  trans
    (Panel.panelShuffle
      (multiplicity * Panel.panelWeighted positiveWeights
        (Panel.originalReactants reaction))
      (rateWeightedReactants positiveWeights reactions multiplicities)
      (multiplicity * Panel.panelWeighted negativeWeights
        (Panel.originalProducts reaction))
      (rateWeightedProducts negativeWeights reactions multiplicities))
    (trans
      (cong₂ _+_
        (trans
          (sym (*-distribˡ-+ multiplicity
            (Panel.panelWeighted positiveWeights
              (Panel.originalReactants reaction))
            (Panel.panelWeighted negativeWeights
              (Panel.originalProducts reaction))))
          (trans
            (cong (λ total → multiplicity * total) (balanced F.zero))
            (*-distribˡ-+ multiplicity
              (Panel.panelWeighted positiveWeights
                (Panel.originalProducts reaction))
              (Panel.panelWeighted negativeWeights
                (Panel.originalReactants reaction)))))
        (allFiniteColumnsRateWeightedSignedConserve
          positiveWeights negativeWeights reactions multiplicities
          (λ column → balanced (F.suc column))))
      (sym (Panel.panelShuffle
        (multiplicity * Panel.panelWeighted positiveWeights
          (Panel.originalProducts reaction))
        (rateWeightedProducts positiveWeights reactions multiplicities)
        (multiplicity * Panel.panelWeighted negativeWeights
          (Panel.originalReactants reaction))
        (rateWeightedReactants negativeWeights reactions multiplicities))))

------------------------------------------------------------------------
-- Source-conditional 29x12 specializations.
------------------------------------------------------------------------

original29x12RateWeightedCHNOPBalance :
  (certificate : Panel.SourceCertifiedOriginal29x12)
  (element : Panel.OriginalCHNOPElement)
  (multiplicities : V.Vec Nat 12) →
  rateWeightedReactants (Panel.sourceElementWeights certificate element)
    (Panel.sourceFiniteColumns certificate) multiplicities
    ≡
  rateWeightedProducts (Panel.sourceElementWeights certificate element)
    (Panel.sourceFiniteColumns certificate) multiplicities
original29x12RateWeightedCHNOPBalance certificate element multiplicities =
  allFiniteColumnsRateWeightedConserve
    (Panel.sourceElementWeights certificate element)
    (Panel.sourceFiniteColumns certificate) multiplicities
    (Panel.sourceColumnLeftKernel certificate element)

original29x12RateWeightedSignedChargeBalance :
  (certificate : Panel.SourceCertifiedOriginal29x12)
  (multiplicities : V.Vec Nat 12) →
  (rateWeightedReactants (Panel.sourcePositiveChargeWeights certificate)
    (Panel.sourceFiniteColumns certificate) multiplicities
    + rateWeightedProducts (Panel.sourceNegativeChargeWeights certificate)
      (Panel.sourceFiniteColumns certificate) multiplicities)
    ≡
  (rateWeightedProducts (Panel.sourcePositiveChargeWeights certificate)
    (Panel.sourceFiniteColumns certificate) multiplicities
    + rateWeightedReactants (Panel.sourceNegativeChargeWeights certificate)
      (Panel.sourceFiniteColumns certificate) multiplicities)
original29x12RateWeightedSignedChargeBalance certificate multiplicities =
  allFiniteColumnsRateWeightedSignedConserve
    (Panel.sourcePositiveChargeWeights certificate)
    (Panel.sourceNegativeChargeWeights certificate)
    (Panel.sourceFiniteColumns certificate) multiplicities
    (Panel.sourceColumnSignedCharge certificate)


------------------------------------------------------------------------
-- All 27 original sites may simultaneously have different multiplicities.
-- Independent source columns are used at every site. This is the finite
-- reaction accounting needed by the 27x29 spatial mass-action source term,
-- NOT a proof that measured rates or a physical time step exist.
------------------------------------------------------------------------

spatialRateWeightedReactants :
  ∀ {n sites r} →
  V.Vec Nat n →
  V.Vec (Panel.OriginalFiniteReaction n) r →
  V.Vec (V.Vec Nat r) sites → Nat
spatialRateWeightedReactants weights reactions V.[] = 0
spatialRateWeightedReactants weights reactions
  (V._∷_ atSite remaining) =
  rateWeightedReactants weights reactions atSite
    + spatialRateWeightedReactants weights reactions remaining

spatialRateWeightedProducts :
  ∀ {n sites r} →
  V.Vec Nat n →
  V.Vec (Panel.OriginalFiniteReaction n) r →
  V.Vec (V.Vec Nat r) sites → Nat
spatialRateWeightedProducts weights reactions V.[] = 0
spatialRateWeightedProducts weights reactions
  (V._∷_ atSite remaining) =
  rateWeightedProducts weights reactions atSite
    + spatialRateWeightedProducts weights reactions remaining

allSitesRateWeightedConserve :
  ∀ {n r sites}
  (weights : V.Vec Nat n)
  (reactions : V.Vec (Panel.OriginalFiniteReaction n) r)
  (siteMultiplicities : V.Vec (V.Vec Nat r) sites) →
  ((column : F.Fin r) →
    Panel.panelWeighted weights
      (Panel.originalReactants (V.lookup reactions column))
      ≡ Panel.panelWeighted weights
        (Panel.originalProducts (V.lookup reactions column))) →
  spatialRateWeightedReactants weights reactions siteMultiplicities
    ≡ spatialRateWeightedProducts weights reactions siteMultiplicities
allSitesRateWeightedConserve weights reactions V.[] balanced = refl
allSitesRateWeightedConserve weights reactions
  (V._∷_ atSite remaining) balanced =
  cong₂ _+_
    (allFiniteColumnsRateWeightedConserve
      weights reactions atSite balanced)
    (allSitesRateWeightedConserve weights reactions remaining balanced)

allSitesRateWeightedSignedConserve :
  ∀ {n r sites}
  (positiveWeights negativeWeights : V.Vec Nat n)
  (reactions : V.Vec (Panel.OriginalFiniteReaction n) r)
  (siteMultiplicities : V.Vec (V.Vec Nat r) sites) →
  ((column : F.Fin r) →
    (Panel.panelWeighted positiveWeights
      (Panel.originalReactants (V.lookup reactions column))
      + Panel.panelWeighted negativeWeights
        (Panel.originalProducts (V.lookup reactions column)))
    ≡
    (Panel.panelWeighted positiveWeights
      (Panel.originalProducts (V.lookup reactions column))
      + Panel.panelWeighted negativeWeights
        (Panel.originalReactants (V.lookup reactions column)))) →
  (spatialRateWeightedReactants positiveWeights reactions siteMultiplicities
    + spatialRateWeightedProducts negativeWeights reactions siteMultiplicities)
    ≡
  (spatialRateWeightedProducts positiveWeights reactions siteMultiplicities
    + spatialRateWeightedReactants negativeWeights reactions siteMultiplicities)
allSitesRateWeightedSignedConserve positiveWeights negativeWeights
  reactions V.[] balanced = refl
allSitesRateWeightedSignedConserve positiveWeights negativeWeights
  reactions (V._∷_ atSite remaining) balanced =
  trans
    (Panel.panelShuffle
      (rateWeightedReactants positiveWeights reactions atSite)
      (spatialRateWeightedReactants positiveWeights reactions remaining)
      (rateWeightedProducts negativeWeights reactions atSite)
      (spatialRateWeightedProducts negativeWeights reactions remaining))
    (trans
      (cong₂ _+_
        (allFiniteColumnsRateWeightedSignedConserve positiveWeights
          negativeWeights reactions atSite balanced)
        (allSitesRateWeightedSignedConserve positiveWeights
          negativeWeights reactions remaining balanced))
      (sym (Panel.panelShuffle
        (rateWeightedProducts positiveWeights reactions atSite)
        (spatialRateWeightedProducts positiveWeights reactions remaining)
        (rateWeightedReactants negativeWeights reactions atSite)
        (spatialRateWeightedReactants negativeWeights reactions remaining))))

original369x29x12SpatialRateCHNOPBalance :
  (certificate : Panel.SourceCertifiedOriginal29x12)
  (element : Panel.OriginalCHNOPElement)
  (siteMultiplicities : V.Vec (V.Vec Nat 12) 27) →
  spatialRateWeightedReactants
    (Panel.sourceElementWeights certificate element)
    (Panel.sourceFiniteColumns certificate) siteMultiplicities
    ≡
  spatialRateWeightedProducts
    (Panel.sourceElementWeights certificate element)
    (Panel.sourceFiniteColumns certificate) siteMultiplicities
original369x29x12SpatialRateCHNOPBalance
  certificate element siteMultiplicities =
  allSitesRateWeightedConserve
    (Panel.sourceElementWeights certificate element)
    (Panel.sourceFiniteColumns certificate) siteMultiplicities
    (Panel.sourceColumnLeftKernel certificate element)

original369x29x12SpatialRateSignedChargeBalance :
  (certificate : Panel.SourceCertifiedOriginal29x12)
  (siteMultiplicities : V.Vec (V.Vec Nat 12) 27) →
  (spatialRateWeightedReactants
    (Panel.sourcePositiveChargeWeights certificate)
    (Panel.sourceFiniteColumns certificate) siteMultiplicities
    + spatialRateWeightedProducts
      (Panel.sourceNegativeChargeWeights certificate)
      (Panel.sourceFiniteColumns certificate) siteMultiplicities)
    ≡
  (spatialRateWeightedProducts
    (Panel.sourcePositiveChargeWeights certificate)
    (Panel.sourceFiniteColumns certificate) siteMultiplicities
    + spatialRateWeightedReactants
      (Panel.sourceNegativeChargeWeights certificate)
      (Panel.sourceFiniteColumns certificate) siteMultiplicities)
original369x29x12SpatialRateSignedChargeBalance
  certificate siteMultiplicities =
  allSitesRateWeightedSignedConserve
    (Panel.sourcePositiveChargeWeights certificate)
    (Panel.sourceNegativeChargeWeights certificate)
    (Panel.sourceFiniteColumns certificate) siteMultiplicities
    (Panel.sourceColumnSignedCharge certificate)
