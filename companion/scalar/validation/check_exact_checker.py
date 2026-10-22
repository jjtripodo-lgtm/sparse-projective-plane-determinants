#!/usr/bin/env python3
"""Independent exact enclosure and symbolic identity controls for the publication checker.

These controls corroborate the implementation and formula translation. They do
not replace the all-degree coverage argument or a Lean source rebuild.
"""
import argparse
import hashlib
import importlib.util
import itertools
import json
from fractions import Fraction as F
from pathlib import Path
import sympy as s

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('checker', type=Path, help='Path to the exact family checker being reviewed')
SOURCE = parser.parse_args().checker.resolve()
before = hashlib.sha256(SOURCE.read_bytes()).hexdigest()
spec = importlib.util.spec_from_file_location('publication_checker', SOURCE)
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)

def require(condition, message):
    if not condition:
        raise ArithmeticError(message)

def contains(interval, value):
    return F(interval.lo, c.S) <= value <= F(interval.hi, c.S)

# Exact rational test points, deliberately covering negative values, zero,
# sign-crossing products and nonterminating reciprocal decimals.
values = [F(a,b) for a in range(-7,8) for b in (1,3,7)]
count = 0
for a,b in itertools.product(values, repeat=2):
    A,B = c.I.of(a), c.I.of(b)
    require(contains(A+B, a+b), 'addition enclosure')
    require(contains(A-B, a-b), 'subtraction enclosure')
    require(contains(A*B, a*b), 'multiplication enclosure')
    count += 3
    if b:
        require(contains(A/B, a/b), 'division enclosure')
        count += 1
for lo,hi in ((-9,-2),(-7,4),(0,1),(2,11)):
    A = c.I.of(lo)
    A = c.I(A.lo, c.I.of(hi).hi)
    for n in range(6):
        for k in range(11):
            value=F((10-k)*lo+k*hi,10)
            require(contains(A**n, value**n),'power enclosure')
            count += 1

# Algebra from the original vertex deficit, independent of the checker's T.
x,y,ax,ay,r,R,gamma,b,alpha,beta,F0 = s.symbols('x y ax ay r R gamma b alpha beta F0', nonzero=True)
d,u = s.symbols('d u', nonzero=True)
vertex_F = (b*R/2+gamma*R**2/(2*d**2))*u-gamma*R**2*u**2+s.log(d/r)
q = F0+alpha*(d-r)+beta*(d*u-1)-vertex_F
# Replace the literal logarithmic term by its known x*log(r*x) equivalent;
# compare the polynomial parts, leaving the logs unchanged on both sides.
q_poly = q+s.log(d/r)
def tangent(X,Y,A):
    return s.expand(X*(q_poly.subs({d:1/X,u:A})+s.diff(q_poly,u).subs({d:1/X,u:A})*(Y-A)))
from_vertices=tangent(x,y,ax)+tangent(y,x,ay)
from_checker=2*alpha+(F0-r*alpha)*(x+y)-b*R*x*y+gamma*R**2*(2*x*y*(ax+ay)-x*ax**2-y*ay**2-s.Rational(1,2)*x*y*(x*x+y*y))
require(s.simplify(from_vertices-from_checker)==0,'vertex-to-edge symbolic identity')
F0_actual=vertex_F.subs({d:r,u:1/r,R:r*r})
F0_checker=(b*R/(2*r)-gamma*(2*R-r)/2).subs(R,r*r)
require(s.simplify(F0_actual-F0_checker)==0,'F0 transcription identity')

# Each declared anchor passes exactly through the plane point.
anchor_checks=0
for rr,(name,K) in c.PLAN.items():
    xx=s.Rational(1,rr)
    if name=='linear':
        exact=s.Rational(2,5*rr)+s.Rational(3,5)*xx
    elif name=='quadratic':
        exact=-s.Rational(1,100)+s.Rational(6,5)*xx-xx*xx
    else:
        h=xx-s.Rational(1,rr)
        exact=xx-s.Rational(2,3)*h*h-s.Rational(3,2)*h*h*h
    require(exact==xx,'anchor plane tangency')
    anchor_checks += 1

after=hashlib.sha256(SOURCE.read_bytes()).hexdigest()
require(before==after,'checker changed during independent audit')
print(json.dumps({'status':'passed','checker_source_sha256':before,
  'exact_interval_containment_controls':count,
  'symbolic_vertex_to_edge_identity':True,'symbolic_F0_identity':True,
  'exact_anchor_tangency_controls':anchor_checks,
  'scope':'Exact sampled interval controls and universal symbolic formula identities; full certificate replay and manuscript coverage argument remain separately required'},indent=2,sort_keys=True))
