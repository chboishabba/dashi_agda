# Bioacoustic Situated Performance-Energy Design

## Goal

Extend the existing birdsong energy owner into a situated, time-indexed multi-axis performance carrier that can represent acoustic, respiratory/syringeal, cardiophysiological, movement/display, energetic, and social-context coordinates without collapsing any one axis into a proxy for the others.

## Existing repo machinery reused

- `DASHI.Core.IntersectionalNonFactorability`: single-axis or post-composed observers cannot recover information already erased by a coarse projection; products of separately useful axes are not automatically intersectionally sufficient.
- `DASHI.Core.SituatedFibreDynamicsEverything`: rollup for multi-axis incidence, history/path dependence, consumer-indexed adequacy, trajectory recovery and fibre refinement.
- `DASHI.Biology.BioacousticSongEnergyExpenditureBidiExact`: empirical metabolic-power/energy calibration and energetic fibre separation.
- `DASHI.Physics.Units.SI`: SI dimensions, units, scales and measurement metadata.
- existing attribution/snowball and N-dimensional Pareto owners on PR #884.

No new global planner, new unit system, or parallel factorisation abstraction is introduced.

## Situated state

The application carrier is a time-indexed song-performance state

`Sigma_t = (A_t, R_t, C_t, M_t, E_t, S_t)`

where:

- `A_t` acoustic state: pitch/fundamental/spectral coordinates, amplitude/SPL, timbre and breathiness-related acoustic descriptors when source-defined;
- `R_t` respiratory/vocal-mechanical state: air-sac pressure, airflow, inspiratory/expiratory phase, syringeal effort and minibreath structure;
- `C_t` cardiophysiological state: heart rate and future metabolic/thermal/oxygenation signals;
- `M_t` movement/display state: beak gape, head/body movement, stepping, bobbing and dance;
- `E_t` energetic state: whole-animal metabolic power, respiratory/mechanical proxies, acoustic-radiated energy proxies and accumulated excess energy;
- `S_t` situated context: species, individual, social context, directed/undirected song, noise, temperature, trial and physical time.

Each coordinate remains optional/source-relative at the empirical layer; the formal owner records semantics and non-collapse boundaries, not invented measurements.

## Consumer-indexed projections

Consumers may request acoustic quality, respiratory effort, cardiovascular arousal, movement/display intensity, metabolic expenditure, or a situated composite. A projection is sufficient only with an application-supplied factorisation witness for that consumer.

The owner must state explicit non-promotions:

- high pitch does not imply high energetic expenditure;
- high amplitude/SPL does not imply higher whole-animal metabolic cost;
- respiratory pressure/airflow does not equal whole-animal metabolic power;
- breathiness/timbre does not by itself identify airflow, pathology, or energy expenditure;
- high heart rate does not by itself identify song-production cost;
- dance/display intensity does not by itself identify vocal effort;
- products of separately calibrated axes do not automatically determine condition, effort, fitness signal, or display cost.

## Empirical source roles

Retain source identity/role and proposition scope for the following empirical families:

- Zollinger et al. 2011, DOI `10.1371/journal.pone.0023198`: louder zebra-finch song requires higher subsyringeal pressure but did not show measurable oxygen-consumption increase in that experiment.
- Franz & Goller 2003, DOI `10.1242/jeb.00196`: song respiration, airflow, air-sac pressure and oxygen-consumption timing are jointly measured; metabolic cost is related to song duration.
- Goller et al. 2004, DOI `10.1002/neu.10327`: beak gape covaries with acoustic frequency, pressure and often amplitude.
- Cooper & Goller 2006, DOI `10.1152/jn.01123.2005`: heart rate differs with social context during directed versus undirected zebra-finch song and covaries with song timing.
- Ota et al. 2015, DOI `10.1038/srep16614`: courtship can combine singing with simultaneous stepping/bobbing dance in both sexes of blue-capped cordon-bleus.

These sources motivate and calibrate specific fibres; citation does not create cross-species authority or same-object identity.

## Intersectional nonfactorability

The new owner must reuse `FactorsThrough` and `NonFactorabilityWitness` rather than creating a new sufficiency type. At minimum it will provide finite witnesses showing that equal acoustic projection can coexist with different physiological/movement state and that equal energetic projection can coexist with different situated display state. These witnesses establish that downstream consumers cannot infer the richer situated phenomenon from the flattened axis alone.

## Pareto/debt behavior

Do not add another universal scalar score. Reuse the existing N-dimensional infrastructure and expose consumer-relative calibration debt labels such as acoustic, respiratory, cardiac, movement and energetic calibration debt only when the consumer requires them. Existing ROI/MaleCNS scientific frontiers must not be reordered merely because new song-performance fibres exist.

## Validation

Add a focused static contract and import the new owner into `BioacousticFlyStateSpaceValidation.agda` and `AnimalexicEverything.agda`. An exact-head Agda claim is permitted only with a fresh build/workflow receipt.
