# P0 Yang–Mills: solve positive physical length before inverse length

22 November 2026. Owner: master-based PR #1536, cross-referenced by original #1444 and indexed #1291. This is an original-source geometry and CONDITIONAL full-Wilson D1 reverse solve, NOT proof of the Clay mass gap.

## Original geometry, not a negative distance

BIPM's SI metre [m] is length. A reciprocal metre [m^-1] is the dimension of inverse length, NOT a negative geometric length. Original R445 positive bond pair from YMClayR445OriginalAxialBondParityInjectiveExact goes, on the side-four positive-axis torus:

    (2X,mu) -> (2X+e_mu,mu) -> (2X+2e_mu,mu)  mod 4.

These are two genuine original axial fine steps, so L_native=a+a=2a>0 [m] for positive fine spacing a. Reversing the path gives a signed displacement -2a along the axis, but path length remains +2a. The opposite endpoints on the four-cycle admit +2 and -2 routes of equal positive length. The finite torus circumference is 4a. The SU(N) inverse link U^-1 is a reversed transport, not negative SI length. No infinite-separation claim is inferred from this finite torus.

Binary 369 eight-sheet original 1024-bond address = original 128 native coarse/axial addresses times 8 transverse bit sheets, with selected 000 (128 bonds), seven spectators (896). These eight sheets are *alternatives*, NOT eight physical axial steps. The selected link occupies four orientation-specific independent 32-link classes. Exactly 384 of 1536 original Wilson plaquettes contain two selected links, so all 128 do not factorize over the 896 spectators.

## Existing original source already expresses positive physical geometry

YMClayPhysicalCubeDobrushinFromGibbsExact.OriginalPhysicalCubeConditionals requires 0<a_n, fixed 0<L_cube and cells(n)*a_n=L_cube, plus true original Gibbs relative-boundary influence estimates. YMClayRGDriftOriginalGibbsInstantiationExact retains original source physical-cube calibration conditionally. This is the existing physical CUBE, not a claim that two cells at every cutoff span the fixed cube.

BalabanPhysicalClusteringScaleAlgebraExact.PhysicalScaleData instead requires a>=0, aInv>=0 and a*aInv=1. These three statements MATHEMATICALLY imply a>0 and aInv>0: neither can vanish by the product law; combined with nonnegativity both are strictly positive.

New PR #1536 YMClayR445PositiveSIBlockGeometryExact.agda consumes the original source's strict positive spacing proof and derives 0<a_n+a_n using rational strict-addition monotonicity. It constructs SIIndexedQuantity rational SI.Length with a separate positivity proof; the SI dimension tag alone is NOT a positive-magnitude certificate. It also imports original selected R445 positive-bond equality from the full 1024-bond binary 369 source. Source-written Agda, pinned kernel not run.

## Positive correlation length: reverse solve original full-Gibbs D1

YMClayD1OriginalFullWilsonSmallLargeFieldExact.OriginalSmallLargePhysicalSource demands, at every original Wilson cutoff n and volume, a common fixed positive real physical cube length L, original normalized two-mark connected Wilson covariance, genuine small CMP116 and large-field response and a shared 0<=q<1:

    abs(Cov_original,n(F,G)) <= (A_small+A_large) * q^d,
    d = original fixed-physical-cube block distance (Nat).

This record is NOT currently supplied with the actual full original interacting Wilson physical estimates, including large-field corrections. It allows q=0. To obtain a strictly positive finite envelope length while preserving its ORIGINAL conditional covariance conclusion, set

    qbar=(1+q)/2.   Then 0<qbar<1, q<=qbar and
    q^d <= qbar^d for every d>=0, including d=0.

Define the positive clustering **UPPER-BOUND length**

    xi_bound=L/(-ln qbar) [m]  > 0.

Then the SAME conditional original D1 covariance is bounded by

    abs(Cov_original,n(F,G))
      <= (A_small + A_large) * exp[-L*d/xi_bound].

The log and exp order/positivity must be instantiated over the actual REAL original Wilson scalar; rational arithmetic or an invented logarithm does not create that source. Physical interpretation r=L*d additionally needs the source test-support/time-distance identification. This provides an UPPER CLUSTERING ENVELOPE length if D1 is inhabited, not equality to the actual lightest excitation correlation length. Faster decay is allowed. The original one-cube Dobrushin row q<1 does not automatically yield q^d across arbitrary distances; original source spatial propagation, W1/W3 marked J and full large-field estimates remain to prove.

Previous YMClayR445Base2SIPhysicalRateBIDIExact defines coarse exponent as twice fine as a *comparison target*. It is tautological geometric calibration, NOT proof that the actual interacting coarse Wilson exponent doubles. A physical blocking source must separately pay that identification.

## Negative-length and failed continuum controls

Negative signed coordinate or path orientation does not mean negative metric length. A hypothetical negative xi produces exp(-r/xi)=exp(+r/abs(xi)), increasing with nonnegative r, and cannot be the decaying exponential clustering envelope. A signed or oscillating connected covariance itself can be negative; D1 correctly bounds its ABSOLUTE VALUE. q=1 implies no rate and infinite xi; q=0 has a zero naive-log length and is safely overbounded by qbar.

Original YangMillsFixedSpacingGapScaleCounterexampleExact shows Delta_lattice(a)=a^2>0, but Delta_physical=Delta_lattice/a=a ->0; corresponding correlation length a/Delta_lattice=1/a -> infinity. Positive native a and a positive lattice finite-cutoff gap are not enough for a finite continuum spectral gap.

## Important SI conversion audit correction

Same physical Euclidean inverse decay length mu=1/xi has SI unit m^-1, whereas m_SI=(hbar/c)*mu has unit kg and E_SI=(hbar*c)*mu has unit J (once the SAME OS spectrum and Euclidean time/space calibration are proved). Both require BIPM SI conversion authority and selected physical normalisation.

YangMillsClayPinnedPhysicalConstructionExact.literalGapIsSIMassMagnitude and YangMillsClayPinnedPhysicalGapAttachmentExact.physicalRateIsSIMassMagnitude project differently SI-typed quantities to bare rational magnitudes and compare them using additional record fields. Those statements are CONDITIONAL NUMERICAL normalizations; their naked numerical equalities are not general SI conversion laws. In ordinary SI, hbar/c is not the dimensionless number 1. Do NOT identify numerical inverse-length and SI mass magnitudes without an explicitly selected conversion convention. Original YangMillsSIScalingEndpointExact.NaturalUnitConversion remains the owner of the actual unit conversion contract. This audit does not modify or promote those original sources.

## Local validation and trust

The locally executed file check_ym_r445_positive_length_source_geometry_20261122.py uses SymPy 1.14.0: 64 true original two-link periodic coarse paths and selected 128+896 partition, ±2 torus positive lengths, 384/1536 two-selected plaquettes; strict rational a and 2a under reciprocal scale; exact rational qbar monotonic for q=0,1/10,1/2,99/100 and d=0..149; positive log-defined xi and original qbar inversion; negative xi/oscillating covariance counterexamples; finite gap a² vanishing physical inverse rate and divergent physical correlation length; and BIPM hbar/c and hbar*c SI dimensions. This is an executed mathematical reference, not an Agda kernel receipt or actual full Wilson D1 estimate.

Genuine next proof: original CMP116/W1/W3 marked-J small+large Gibbs response, exact same original Wilson test support and REAL scalar, cutoff/volume uniform full physical cube q<1, continuous E1 noncollapse, and dense same-H OS spectral gap. No source at this commit proves this final analytic payment.

External original authority: BIPM SI Brochure 9th edition 4.01 (June 2026), https://www.bipm.org/en/publications/si-brochure/ ; Clay Jaffe-Witten Yang–Mills problem statement https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf.
