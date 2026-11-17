#!/usr/bin/env python3
"""A-H/Ω loaded/unloaded × recovery electromechanical intervention.

Every result is a *countermodel or proposed experimental certificate*, NOT a
measurement of @madscience369 V2. Fractions avoid numerical leakage between
motor shaft work and generator work. Signed storage rates may be negative.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from fractions import Fraction as F
from itertools import product
import json, math


def Q(x):
    return x if isinstance(x,F) else F(str(x))

@dataclass(frozen=True)
class Ports:
    motor_input: F
    auxiliary_input: F
    shaft_to_generator: F
    electric_load: F
    other_output: F
    motor_loss: F
    generator_loss: F
    motor_storage_rate: F=F(0)
    generator_storage_rate: F=F(0)
    rotor_storage_rate: F=F(0)

    @property
    def motor_residual(self):
        return self.motor_input-self.shaft_to_generator-self.motor_loss-self.motor_storage_rate

    @property
    def gen_residual(self):
        return (self.shaft_to_generator+self.auxiliary_input-self.electric_load-
                self.other_output-self.generator_loss-self.generator_storage_rate-
                self.rotor_storage_rate)

    @property
    def whole_residual(self):
        return self.motor_input+self.auxiliary_input-self.electric_load-self.other_output-self.motor_loss-self.generator_loss-self.motor_storage_rate-self.generator_storage_rate-self.rotor_storage_rate

    def validate(self, allow_depletion=True):
        for key in ('motor_input','auxiliary_input','shaft_to_generator','electric_load',
                    'other_output','motor_loss','generator_loss'):
            if getattr(self,key)<0: raise ValueError(f'negative physical port {key}')
        if not allow_depletion and (self.motor_storage_rate!=0 or self.generator_storage_rate!=0 or self.rotor_storage_rate!=0):
            raise ValueError('storage endpoints not matched')
        if any(v!=0 for v in (self.motor_residual,self.gen_residual,self.whole_residual)):
            raise ValueError('energy ledger does not close')
        return self

    def serialized(self):
        return {k:str(v) for k,v in asdict(self).items()}


def arm(load:int,recovery:int)->Ports:
    """A deliberately constructed counterworld, not an identified motor map.

    Pmotor=286 always; loading changes shaft transfer from 200 to 245 W,
    while motor dissipation falls 86->41 W. Recovery transfers 7 W of
    generator losses to useful load, with 0.4 W auxiliary supply separately
    counted and consumed at no load. Other mechanical output is 120 W.
    """
    if load not in (0,1) or recovery not in (0,1):raise ValueError('binary treatment')
    shaft=Q(200+45*load)
    aux=Q('0.4')*recovery
    output=Q(45*load+7*load*recovery)
    generator_loss=shaft+aux-output-Q(120)
    return Ports(Q(286),aux,shaft,output,Q(120),Q(286)-shaft,generator_loss).validate(allow_depletion=False)


def interaction(rows:dict, field:str)->F:
    return (getattr(rows[(1,1)],field)-getattr(rows[(1,0)],field)-
            getattr(rows[(0,1)],field)+getattr(rows[(0,0)],field))


def contrasts()->dict:
    rows={(l,r):arm(l,r) for l,r in product((0,1),repeat=2)}
    cols=['motor_input','auxiliary_input','electric_load','other_output','motor_loss',
          'generator_loss','motor_storage_rate','generator_storage_rate','rotor_storage_rate','shaft_to_generator']
    I={k:interaction(rows,k) for k in cols}
    # Shaft is internal, cancels when the motor and generator are both accounted.
    combined=I['motor_input']+I['auxiliary_input']-I['electric_load']-I['other_output']-I['motor_loss']-I['generator_loss']-I['motor_storage_rate']-I['generator_storage_rate']-I['rotor_storage_rate']
    assert combined==0
    assert I['electric_load']==7 and I['generator_loss']==-7 and I['shaft_to_generator']==0
    return {'arms':{f'load{l}_recovery{r}':v.serialized() for (l,r),v in rows.items()},
            'interaction_w':{k:str(v) for k,v in I.items()},
            'whole_interaction_residual_w':str(combined),
            'interpretation':'synthetic 7 W interaction from displaced generator heat, not 7 W new energy',
            'actual_v2_evidence':False}


def alternative_45w_counterworlds()->dict:
    """Same nominal motor-input and load displays, incompatible causal paths."""
    base=Ports(Q(286),Q(0),Q(200),Q(0),Q(120),Q(86),Q(80)).validate(False)
    cases={
        'reduced_generator_loss':Ports(Q(286),Q(0),Q(200),Q(45),Q(120),Q(86),Q(35)),
        'increased_shaft_at_constant_motor_input':Ports(Q(286),Q(0),Q(245),Q(45),Q(120),Q(41),Q(80)),
        'unmeasured_auxiliary':Ports(Q(286),Q(45),Q(200),Q(45),Q(120),Q(86),Q(80)),
        'depleting_rotor_or_other_storage':Ports(Q(286),Q(0),Q(200),Q(45),Q(120),Q(86),Q(80),rotor_storage_rate=Q(-45)),
        'displaced_other_output':Ports(Q(286),Q(0),Q(200),Q(45),Q(75),Q(86),Q(80)),
    }
    for p in cases.values():p.validate()
    for p in cases.values():
        assert p.motor_input==base.motor_input and p.electric_load-base.electric_load==45
    return {'baseline':base.serialized(), 'alternatives':{name:v.serialized() for name,v in cases.items()},
            'physical_note':'constructed counterworlds; losses, auxiliary and hidden other outputs not measured on V2'}


def motor_generator_intervention_signature(load=1,recovery=0,rpm=2354.0)->dict:
    p=arm(load,recovery); off=arm(0,recovery)
    speed=2*math.pi*rpm/60
    return {'motor_electrical_change_w':float(p.motor_input-off.motor_input),
            'shaft_change_w':float(p.shaft_to_generator-off.shaft_to_generator),
            'shaft_torque_change_nm':float(p.shaft_to_generator-off.shaft_to_generator)/speed,
            'motor_loss_change_w':float(p.motor_loss-off.motor_loss),
            'generator_loss_change_w':float(p.generator_loss-off.generator_loss),
            'load_change_w':float(p.electric_load-off.electric_load),
            'shaft_independent_meter_required':True}


def sensor_discriminator()->dict:
    """Five unknown deltas: aux, total losses, storage, other, shaft.

    Whole-system meter row ignores shaft (internal). Shaft torque is not
    uniquely deducible from the whole-system balance and must be measured.
    The proposed independent aux/storage/other/shaft sensors make all five
    unknowns identifiable; loss follows from the whole balance.
    """
    import sympy as sp
    basic=sp.Matrix([[1,-1,-1,-1,0]])
    sensor_rows={'auxiliary_port':[1,0,0,0,0],
                 'storage_endpoints':[0,0,1,0,0],
                 'other_outputs':[0,0,0,1,0],
                 'torque_times_speed':[0,0,0,0,1],
                 'duplicate_electrical_meter':[1,-1,-1,-1,0]}
    full=basic.col_join(sp.Matrix([sensor_rows[k] for k in ('auxiliary_port','storage_endpoints','other_outputs','torque_times_speed')]))
    assert basic.rank()==1 and full.rank()==5
    return {'unknown_deltas':['auxiliary','dissipation','storage_rate','other_output','shaft_transfer'],
            'basic_rank':1,'basic_nullity':4,'full_rank':5,'full_nullity':0,
            'shaft_unidentifiable_from_electrical_meters':True,
            'sensor_rows':sensor_rows,
            'caveat':'calibrated shaft measurement is an independent mechanical observable; unknown total loss is inferred, not separately calorimetrically proven'}


def worst_case_interaction_error(errors:dict)->dict:
    """Worst-case independent absolute errors for the four 2×2 arm means.

    Each difference-in-differences combines four arm measurements with +/-1,
    so its deterministic bound is the sum of four per-arm absolute bounds.
    Not a confidence interval and not protection against systematic drift.
    """
    if set(errors)!={'00','01','10','11'}:raise ValueError('need four arms')
    if any(x<0 for x in errors.values()):raise ValueError('negative error')
    total=sum(map(Q,errors.values()),F(0))
    return {'absolute_bound_w':str(total),'nominal_interaction_w':'7',
            'interval_w':[str(Q(7)-total),str(Q(7)+total)],
            'sign_certified':total<7,'confidence':None}


def run():
    return {'schema':'DASHI.V2.Omega.load-intervention.v1',
            'four_arm':contrasts(),
            'rival_worlds':alternative_45w_counterworlds(),
            'loaded_signature':motor_generator_intervention_signature(),
            'measurement_rank':sensor_discriminator(),
            'interaction_error':worst_case_interaction_error({'00':1,'01':1,'10':1,'11':1}),
            'status':'restricted exact toy construction; V2 apparatus not measured',
            'agda_kernel':'NOT RUN'}

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
