#!/usr/bin/env python3
"""Independent event-ledger referee for Kozyrev 2D optical torque.

Original implementation: DASHI PR #1404. Physics: conventional
P/c momentum flux, cross-product torque about a fixed origin.
Not a proof of anomalous torsion, a physical experiment, or an Agda proof.
Input JSON event stream must supply source rays and terminal records.
"""
from __future__ import annotations
import json
import math
from dataclasses import dataclass
C = 299792458.0

def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]

def sub(a, b):
    return (a[0]-b[0], a[1]-b[1])

def add(a, b):
    return (a[0]+b[0], a[1]+b[1])

def scale(k, a):
    return (k*a[0], k*a[1])

def unit(v, tolerance=1e-9):
    return abs(v[0]*v[0]+v[1]*v[1]-1) <= tolerance

@dataclass
class RayLedger:
    position: tuple
    direction: tuple
    power_w: float
    source_position: tuple
    source_direction: tuple
    source_power_w: float
    wall_force: tuple=(0., 0.)
    wall_torque: float=0.
    wall_absorption_w: float=0.
    event_count: int=0

    @classmethod
    def emit(cls, position, direction, power_w):
        if not unit(direction) or not 0 <= power_w < float('inf'):
            raise ValueError('source must have unit direction and finite nonnegative power')
        return cls(tuple(position), tuple(direction), power_w,
                   tuple(position), tuple(direction), power_w)

    def hit(self, point, outgoing_direction, reflectivity, *, path_tolerance=1e-7):
        """Conventional reflection plus local absorption at each wall event."""
        if not 0 <= reflectivity <= 1 or not unit(outgoing_direction):
            raise ValueError('invalid reflectivity or outgoing direction')
        segment=sub(point,self.position)
        distance=math.hypot(*segment)
        if distance <= path_tolerance or abs(cross(segment,self.direction)) > path_tolerance*max(distance,1):
            raise ValueError('wall event does not lie on the forward ray')
        if segment[0]*self.direction[0]+segment[1]*self.direction[1] <= 0:
            raise ValueError('wall collision lies behind ray')
        pin=scale(self.power_w/C,self.direction)
        pout=scale(self.power_w*reflectivity/C,outgoing_direction)
        impulse=sub(pin,pout)
        self.wall_force=add(self.wall_force,impulse)
        self.wall_torque+=cross(point,impulse)
        self.wall_absorption_w+=self.power_w*(1-reflectivity)
        self.power_w*=reflectivity
        self.position=tuple(point)
        self.direction=tuple(outgoing_direction)
        self.event_count+=1

    def close(self, kind, terminal_point, origin=(0.,0.), *, path_tolerance=1e-7):
        """Terminal event escaped/target/unresolved (never call unresolved 'escape')."""
        if kind not in ('escape','target','unresolved'):
            raise ValueError('invalid terminal state')
        segment=sub(terminal_point,self.position)
        distance=math.hypot(*segment)
        if distance > path_tolerance:
            if abs(cross(segment,self.direction)) > path_tolerance*max(distance,1):
                raise ValueError('terminal event is off outgoing ray')
            if segment[0]*self.direction[0]+segment[1]*self.direction[1] < 0:
                raise ValueError('terminal lies behind ray')
        pin=scale(self.source_power_w/C,self.source_direction)
        pout=scale(self.power_w/C,self.direction)
        target= pout if kind=='target' else (0.,0.)
        unresolved=pout if kind=='unresolved' else (0.,0.)
        escape=pout if kind=='escape' else (0.,0.)
        delta=sub(pin,add(self.wall_force,add(target,add(unresolved,escape))))
        # Source position and termination position account for angular momentum.
        # The wall events' moment must be taken about the exact same origin.
        input_L=cross(sub(self.source_position,origin),pin)
        output_L=cross(sub(terminal_point,origin),pout)
        target_L=output_L if kind=='target' else 0.
        escape_L=output_L if kind=='escape' else 0.
        unresolved_L=output_L if kind=='unresolved' else 0.
        lres=input_L-self.wall_torque-target_L-escape_L-unresolved_L
        energy=self.source_power_w-self.wall_absorption_w-self.power_w
        return dict(kind=kind,source_W=self.source_power_w,wall_absorption_W=self.wall_absorption_w,
                    output_W=self.power_w,wall_force_N=self.wall_force,
                    wall_torque_Nm=self.wall_torque,momentum_residual_N=math.hypot(*delta),
                    angular_residual_Nm=lres,energy_residual_W=energy,
                    terminal_power_W=self.power_w,event_count=self.event_count)

def specular(direction, normal):
    if not unit(normal):
        raise ValueError('surface normal not unit')
    projection=direction[0]*normal[0]+direction[1]*normal[1]
    out=sub(direction,scale(2*projection,normal))
    if not unit(out): raise ValueError('specular energy failure')
    return out

def same_scale_example(scale_length):
    r=RayLedger.emit((-2*scale_length,0),(1.,0.),9000.)
    hit=(0.,0.)
    r.hit(hit,(0.,1.),0.95)
    # This is a purely mathematical event-ledger fixture; physically a
    # free path from source to hit must separately be established.
    return r.close('escape',(0.,3*scale_length))

if __name__=='__main__':
    print(json.dumps({'example':same_scale_example(1.0)},indent=2))
