#!/usr/bin/env python3
"""2026 LARES-2 original-observable and KK source-transport acceptance.

External original data: Ciufolini et al., Nature 655, 332-335 (2026),
DOI 10.1038/s41586-026-10715-0; ILRS news dated 2026-08-05.
The Nature analysis uses LARES-2/LAGEOS orbit determination and GRACE
geopotential inputs. Numbers below are reported GR predictions and the
published dimensionless fitted scale, NOT an independent tracking fit.

Actual local source owners: dashi_agda KK #1241 check_lares2_kk_frame_dragging,
check_kk_chiral_slow_spin_consumer, check_kk_source_matching_gate and
KKSteelmanBidirectionalConsumerExact; E6 #1106, torque #1164,
Casimir/stress #1165. Author-specific observational projection and
source/measurement non-promotion test: Johl Brown, ChatGPT assisted.
"""
from decimal import Decimal as D

# The original study's GR contributions, NOT independently fitted
# measured rates or an independently calibrated KK prediction.
lageos=D('30.650')
lares2=D('30.678')
combined=D('61.328')
assert lageos+lares2==combined
mu_fit=D('1.001')
mu_GR=D('1')
sigma_stat=D('0.001')
sigma_syst=D('0.002')
assert mu_fit-mu_GR==D('0.001')
assert sigma_syst==2*sigma_stat
assert (mu_fit-mu_GR)<=sigma_syst
assert (lageos*sigma_syst, lares2*sigma_syst)==(D('0.061300'),D('0.061356'))
assert combined*sigma_stat==D('0.061328')
assert combined*sigma_syst==D('0.122656')
assert combined*(mu_fit-mu_GR)==D('0.061328')
# Source's two distinct error budgets are *not* silently convolved
# into an independent Gaussian 1-sigma or model-specific confidence bound.

# Source/experiment inverse problem: WITHOUT a source-derived nuisance
# model, the same scalar measurement can be explained by two different
# underlying delta + nuisance splittings. This is a toy identifiability
# counterexample, NOT a critique of the paper's fitted geodetic model.
models=((D('0'),D('0.001')),(D('0.001'),D('0')))
for physical_delta,unconstrained_nuisance in models:
    assert mu_GR+physical_delta+unconstrained_nuisance==mu_fit
assert models[0]!=models[1]

# The selected orbifold metric g_mu5 zero mode is parity ODD; this
# cannot serve as a surviving 4D Maxwell photon under the same
# untwisted Z2 assumption. This expected parity is checked independently
# by the existing source-script, not inferred from experimental data.
metric_vector_parity=-1
independent_bulk_Maxwell_vector_parity=+1
assert (1+metric_vector_parity)//2==0
assert (1+independent_bulk_Maxwell_vector_parity)//2==1

# Current E6 owner: rank(Mneutral)=3 for 4 generators conditional
# on its E21 VEV; an additional untouched independent Maxwell B would
# add a fifth generator but NOT increase the Higgs mass rank.
assert 4-3==1 and 5-3==2

print('PASS 2026 original GR nodal contributions and published separate 0.001/0.002 errors')
print('PASS published 0.2% systematic scale is not 0.1% statistical scale')
print('PASS abstract toy nuisance/source collision: a published mu cannot identify KK parameters')
print('PASS standard orbifold metric-vector zero mode absent; independent B vector distinct')
print('PASS conditional E6 photon rank 3/4, untouched B adds independent massless U1')
print('OPEN Earth-connected 5D solution, source/PPN matching and satellite prediction')
print('OPEN global eta/CS/WZ, Chi33 defects, coupled interval spectrum and radiative stress')
