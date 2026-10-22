#!/usr/bin/env python3
"""Exact symbolic derivation of every constant in the total-rn determinant framework, for symbolic r.

Definitions (t=r-1, R=r^2, v=R-t):
  gamma = (v/t - log(R/t))/v^2,  b = 1/t + 2*gamma*t,  a = log t - b*t + gamma*t^2
  q(z) = a + b z - gamma z^2   (Hermite: q(t)=log t, q'(t)=1/t, q(R)=log R)
  F(d,u) = (b R/2 + gamma R^2/(2 d^2)) u - gamma R^2 u^2 + log(d/r)
  beta and alpha are DERIVED below from the two tangency conditions at the plane point (d,u)=(r,1/r).
Checks: Hermite interpolation conditions, a+2F(r,1/r)=2*ell with ell=(log r+((v-1)/2) log t)/v,
and that the derived alpha, beta equal the closed forms used by the verifier."""
import sympy as sp
r=sp.symbols('r',positive=True)
d,u,z=sp.symbols('d u z',positive=True)
t=r-1; R=r**2; v=R-t
gamma=(v/t-sp.log(R/t))/v**2
b=1/t+2*gamma*t
a=sp.log(t)-b*t+gamma*t**2
q=a+b*z-gamma*z**2
F=(b*R/2+gamma*R**2/(2*d**2))*u-gamma*R**2*u**2+sp.log(d/r)
F0=F.subs({d:r,u:1/r})
ell=(sp.log(r)+(v-1)/2*sp.log(t))/v
alpha,beta=sp.symbols('alpha beta')
qdef=F0+alpha*(d-r)+beta*(d*u-1)-F
sol=sp.solve([sp.diff(qdef,u).subs({d:r,u:1/r}),sp.diff(qdef,d).subs({d:r,u:1/r})],[alpha,beta],dict=True)[0]
al_closed=1/r-1/(2*t)+(r-sp.Rational(1,2))*gamma
be_closed=r/(2*t)-gamma*(R+r/2)
checks={
 "q(t)=log t": sp.simplify(sp.expand_log(q.subs(z,t)-sp.log(t),force=True)),
 "q'(t)=1/t": sp.simplify(sp.diff(q,z).subs(z,t)-1/t),
 "q(R)=log R": sp.simplify(sp.expand_log(q.subs(z,R)-sp.log(R),force=True)),
 "a+2F0=2ell": sp.simplify(sp.expand_log(a+2*F0-2*ell,force=True)),
 "alpha derived=closed": sp.simplify(sp.expand_log(sol[alpha]-al_closed,force=True)),
 "beta derived=closed": sp.simplify(sp.expand_log(sol[beta]-be_closed,force=True)),
 "q(r,1/r)=0": sp.simplify(sp.expand_log(qdef.subs(sol).subs({d:r,u:1/r}),force=True)),
 "d2q/du2 = 2 gamma R^2": sp.simplify(sp.diff(qdef,u,2)-2*gamma*R**2),
}
ok=all(v==0 for v in checks.values())
for k,val in checks.items(): print(f"{k:28s} residual = {val}")
print("ALL SYMBOLIC IDENTITIES HOLD" if ok else "FAILURE"); raise SystemExit(0 if ok else 1)
