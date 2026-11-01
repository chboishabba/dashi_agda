module DASHI.Physics.Closure.NSTriadKNLuoCoreSourceFidelityInventoryExact where

------------------------------------------------------------------------
-- PURPOSE
-- Machine-readable source inventory for the principal published and official
-- results used by the Luo continuation and final submission lanes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Physics.Closure.NSTriadKNLuoSubmissionAuditReceiptExact as Audit

luoSource : Audit.SourceFidelityEntry
luoSource = record
  { authorOrAuthors = "Xiaoyutao Luo"
  ; title = "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal Localization"
  ; venueAndYear = "Journal of Mathematical Fluid Mechanics 21 (2019), article 1"
  ; doiOrStableIdentifier = "10.1007/s00021-019-0411-z; 10.48550/arXiv.1803.05569"
  ; theoremOrLemmaNumber = "Proposition 3.1, equation (4.2), and Section 4 continuation argument"
  ; exactHypotheses = "Periodic incompressible Navier--Stokes solution regular before a candidate terminal time, with Luo's localized frequency-time criterion"
  ; domainConvention = "Three-dimensional periodic domain"
  ; fourierConvention = "Dyadic Littlewood--Paley decomposition; exact normalization audited in DASHI"
  ; viscosityConvention = "Normalized positive viscosity; repository adapter records the exact coefficient"
  ; endpointConvention = "The selected alpha lies in (1,2); DASHI selects alpha = 3/2"
  ; proofStatus = "Published analytic source; individual imported and machine-checked obligations tracked separately"
  }

leraySource : Audit.SourceFidelityEntry
leraySource = record
  { authorOrAuthors = "Jean Leray"
  ; title = "Sur le mouvement d'un liquide visqueux emplissant l'espace"
  ; venueAndYear = "Acta Mathematica 63 (1934), 193--248"
  ; doiOrStableIdentifier = "10.1007/BF02547354"
  ; theoremOrLemmaNumber = "Leray weak-solution and energy framework"
  ; exactHypotheses = "Finite-energy divergence-free initial data and positive viscosity"
  ; domainConvention = "Original whole-space result; periodic specialization must be identified explicitly"
  ; fourierConvention = "Not the repository finite coefficient convention"
  ; viscosityConvention = "Positive viscosity"
  ; endpointConvention = "Weak solution and regular-before-terminal interfaces separated"
  ; proofStatus = "Published analytic source; periodic carrier interface formalized in-repo"
  }

bcdSource : Audit.SourceFidelityEntry
bcdSource = record
  { authorOrAuthors = "Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin"
  ; title = "Fourier Analysis and Nonlinear Partial Differential Equations"
  ; venueAndYear = "Springer Grundlehren 343 (2011)"
  ; doiOrStableIdentifier = "10.1007/978-3-642-16830-7"
  ; theoremOrLemmaNumber = "Littlewood--Paley, Bernstein, paraproduct, convolution and Sobolev tools"
  ; exactHypotheses = "Function-space hypotheses are recorded at each imported theorem boundary"
  ; domainConvention = "Euclidean and periodic versions distinguished explicitly"
  ; fourierConvention = "Source convention translated to the official DASHI periodic convention"
  ; viscosityConvention = "Not applicable to purely harmonic-analysis lemmas"
  ; endpointConvention = "Endpoint exclusions remain explicit"
  ; proofStatus = "Published standard analysis; exact imported leaves remain visible"
  }

youngSource : Audit.SourceFidelityEntry
youngSource = record
  { authorOrAuthors = "William Henry Young"
  ; title = "On the Multiplication of Successions of Fourier Constants"
  ; venueAndYear = "Proceedings of the Royal Society of London A 87 (1912)"
  ; doiOrStableIdentifier = "10.1098/rspa.1912.0086"
  ; theoremOrLemmaNumber = "Young convolution inequality ancestry"
  ; exactHypotheses = "Finite signed convolution form proved directly in DASHI"
  ; domainConvention = "Finite sequence reduction, then periodic realization"
  ; fourierConvention = "Exact finite coefficient convention"
  ; viscosityConvention = "Not applicable"
  ; endpointConvention = "Finite sums; no hidden infinite-limit step"
  ; proofStatus = "Finite reducer machine checked; physical receipt still explicit"
  }

grafakosTorresSource : Audit.SourceFidelityEntry
grafakosTorresSource = record
  { authorOrAuthors = "Loukas Grafakos; Rodolfo H. Torres"
  ; title = "A Multilinear Schur Test and Multiplier Operators"
  ; venueAndYear = "Journal of Functional Analysis 187 (2001), 1--24"
  ; doiOrStableIdentifier = "10.1006/jfan.2001.3804"
  ; theoremOrLemmaNumber = "Multilinear Schur-test framework"
  ; exactHypotheses = "Nonnegative kernel-profile bounds and finite shell incidence data"
  ; domainConvention = "Repository specialization is finite periodic"
  ; fourierConvention = "Official physical pair-incidence convention"
  ; viscosityConvention = "Not applicable"
  ; endpointConvention = "All shell constants and support offsets recorded explicitly"
  ; proofStatus = "Finite weighted-Schur algebra machine checked; physical identifications remain explicit"
  }

constantinETitiSource : Audit.SourceFidelityEntry
constantinETitiSource = record
  { authorOrAuthors = "Peter Constantin; Weinan E; Edriss S. Titi"
  ; title = "Onsager's Conjecture on the Energy Conservation for Solutions of Euler's Equation"
  ; venueAndYear = "Communications in Mathematical Physics 165 (1994), 207--209"
  ; doiOrStableIdentifier = "10.1007/BF02099744"
  ; theoremOrLemmaNumber = "Increment/commutator identity ancestry"
  ; exactHypotheses = "Smooth or suitably regular periodic fields for the exact increment identity"
  ; domainConvention = "Periodic adaptation explicitly represented"
  ; fourierConvention = "Repository sign and normalization audited"
  ; viscosityConvention = "Euler identity; viscosity not applicable"
  ; endpointConvention = "Regularity hypotheses must not import the target conclusion"
  ; proofStatus = "Algebraic multiplier identity machine checked; integration realization remains explicit"
  }

feffermanSource : Audit.SourceFidelityEntry
feffermanSource = record
  { authorOrAuthors = "Charles L. Fefferman; Clay Mathematics Institute"
  ; title = "Existence and Smoothness of the Navier--Stokes Equation"
  ; venueAndYear = "Millennium Prize Problems (2000)"
  ; doiOrStableIdentifier = "Official problem description; no DOI assigned"
  ; theoremOrLemmaNumber = "Periodic existence and smoothness statement"
  ; exactHypotheses = "Smooth divergence-free finite-energy initial data and positive viscosity"
  ; domainConvention = "Periodic and whole-space formulations distinguished"
  ; fourierConvention = "Final theorem must be invariant under the selected unitary normalization"
  ; viscosityConvention = "Positive viscosity; normalized form must be justified"
  ; endpointConvention = "Global-in-time smooth existence and uniqueness"
  ; proofStatus = "Target statement only; never an imported theorem"
  }

coreSourceFidelityInventory : List Audit.SourceFidelityEntry
coreSourceFidelityInventory =
  luoSource ∷
  leraySource ∷
  bcdSource ∷
  youngSource ∷
  grafakosTorresSource ∷
  constantinETitiSource ∷
  feffermanSource ∷
  []

coreSourceFidelityInventoryConstructed : Bool
coreSourceFidelityInventoryConstructed = true

coreSourceFidelityInventoryConstructedIsTrue :
  coreSourceFidelityInventoryConstructed ≡ true
coreSourceFidelityInventoryConstructedIsTrue = refl
