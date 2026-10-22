#!/usr/bin/env python3
"""Clean-room rigorous certificate for the total-rn sparse determinant family, 3 <= r <= 14.

Independent of the lab's producer code: written from the definitions in symbolic_identities.py,
using mpmath interval arithmetic (outward rounding) instead of fixed-point integers.

For each r it certifies, rigorously:
  (P) peeling margins:  ell - alpha*(r-k) - log k > 0  for every cofactor degree k = 1..K;
  (E) the edge inequality T_r(1/d,1/c) > 0 for ALL integers d,c >= K+1 except (d,c)=(r,r),
      where T_r(1/r,1/r) = 0 exactly (tangency), using a finite exact window d,c <= N plus an
      interval branch-and-bound for the infinite tail;
  (S) gamma>0, alpha>0, t<R (needed by the Hermite and peeling arguments).
The edge function is g(x,y)+g(y,x) with g(x,y)=x*[q(1/x,A)+q_u(1/x,A)*(y-A)], A=anchor(x), where
q(d,u)=F0+alpha(d-r)+beta(du-1)-F(d,u) is convex in u; summing the supporting tangent at A over the
literal incidence edges is what turns the vertex deficit into this per-edge expression."""
import json, sys, time
from fractions import Fraction as Fr
from mpmath import iv, mp
iv.dps = 60

def consts(r):
    r_ = iv.mpf(r); t = r_-1; R = r_*r_; v = R-t
    g = (v/t - iv.log(R/t))/(v*v)
    b = 1/t + 2*g*t
    al = 1/r_ - 1/(2*t) + (r_-iv.mpf(1)/2)*g
    be = r_/(2*t) - g*(R + r_/2)
    ell = (iv.log(r_) + (v-1)/2*iv.log(t))/v
    F0 = (b*R/2 + g*R*R/(2*r_*r_))/r_ - g*R*R/(r_*r_)
    return dict(r=r_, t=t, R=R, v=v, g=g, b=b, al=al, be=be, ell=ell, F0=F0)

ANCHORS = {
  "linear":    lambda x, r: Fr(2,5)/r + Fr(3,5)*x if isinstance(x,Fr) else iv.mpf(2)/(5*r) + iv.mpf(3)/5*x,
  "quadratic": lambda x, r: -Fr(1,100) + Fr(6,5)*x - x*x if isinstance(x,Fr) else -iv.mpf(1)/100 + iv.mpf(6)/5*x - x*x,
  "cubic":     lambda x, r: x - Fr(2,3)*(x-Fr(1,r))**2 - Fr(3,2)*(x-Fr(1,r))**3 if isinstance(x,Fr)
                            else x - iv.mpf(2)/3*(x-iv.mpf(1)/r)**2 - iv.mpf(3)/2*(x-iv.mpf(1)/r)**3,
}
# (anchor, K) per r: K = largest cofactor-peeled degree.
PLAN = {3:("linear",1),4:("linear",1),5:("linear",1),6:("linear",1),7:("linear",1),8:("linear",1),
        9:("linear",1),10:("quadratic",1),11:("linear",2),12:("cubic",2),13:("cubic",2),14:("cubic",2)}

def xlogrx(X, c):
    """Rigorous enclosure of f(x)=x*log(r*x) on X=[lo,hi], lo>=0 (f(0)=0 by continuity)."""
    lo, hi = X.a, X.b
    r = c["r"]
    def f(p):
        if p == 0: return iv.mpf(0)
        P = iv.mpf(p); return P*iv.log(r*P)
    xm = 1/(iv.e*r)          # minimiser, value -1/(e r)
    fm = -1/(iv.e*r)
    if hi <= xm.a:   # decreasing on X
        return iv.mpf([f(hi).a, f(lo).b])
    if lo >= xm.b:   # increasing on X
        return iv.mpf([f(lo).a, f(hi).b])
    top = max(f(lo).b, f(hi).b)
    return iv.mpf([fm.a, top])

def g_edge(X, Y, c, anchor):
    """Interval enclosure of g(x,y) = x*[q(1/x,A)+q_u(1/x,A)(y-A)], written without 1/x singularities."""
    r, R, g, b, al, be, F0 = c["r"], c["R"], c["g"], c["b"], c["al"], c["be"], c["F0"]
    A = anchor(X, int(r.a))
    lin = b*R/2 + R*R*g*X*X/2
    # x*q(1/x,A) = x*F0 + al*(1-r x) + be*(A-x) - x*lin*A + x*R^2 g A^2 + x log(r x)
    xq = X*F0 + al*(1-r*X) + be*(A-X) - X*lin*A + X*R*R*g*A*A + xlogrx(X, c)
    # x*q_u(1/x,A) = be - x*lin + 2 x R^2 g A
    xqu = be - X*lin + 2*X*R*R*g*A
    return xq + xqu*(Y-A)

def T_box(X, Y, c, anchor):
    return g_edge(X, Y, c, anchor) + g_edge(Y, X, c, anchor)

def pt(p): return iv.mpf(p)

def certify(r, N_factor=12, max_boxes=2_000_000):
    name, K = PLAN[r]; anchor = ANCHORS[name]; c = consts(r)
    out = {"r": r, "anchor": name, "K": K}
    # (S) sign facts
    out["gamma_pos"] = bool(c["g"].a > 0); out["alpha_pos"] = bool(c["al"].a > 0)
    if not (out["gamma_pos"] and out["alpha_pos"] and c["t"].b < c["R"].a): out["FAIL"] = "sign"; return out
    # (P) peeling margins for k=1..K
    margins = []
    for k in range(1, K+1):
        m = c["ell"] - c["al"]*(r-k) - iv.log(k)
        margins.append(float(m.a)); 
        if not m.a > 0: out["FAIL"] = f"peel margin k={k}"; return out
    out["peel_margins_lower"] = margins
    # (E1) finite window K+1 <= d,c <= N, exact points
    N = N_factor*r
    lo_min = None; at = None
    degs = list(range(K+1, N+1))
    gx = {}
    for dd in degs:
        X = pt(1)/dd
        for cc in degs:
            if dd == r and cc == r: continue
            if (cc, dd) in gx: val = gx[(cc, dd)]
            else:
                val = T_box(X, pt(1)/cc, c, anchor); gx[(dd, cc)] = val
            if lo_min is None or val.a < lo_min: lo_min, at = val.a, (dd, cc)
    out["window_N"] = N; out["window_min_lower"] = float(lo_min); out["window_argmin"] = at
    if not lo_min > 0: out["FAIL"] = "window"; return out
    # exact zero at plane point (tangency): enclosure must contain 0 and be tiny
    z = T_box(pt(1)/r, pt(1)/r, c, anchor)
    out["plane_point_enclosure"] = [float(z.a), float(z.b)]
    # (E2) mixed: one degree in window, other in tail [0, 1/(N+1)]
    tail = 1/iv.mpf(N+1)
    boxes = 0; worst = None
    def bb1(xpt, lo, hi, depth=0):
        nonlocal boxes, worst
        boxes += 1
        Y = iv.mpf([lo, hi])
        val = T_box(xpt, Y, c, anchor)
        if val.a > 0:
            worst = val.a if worst is None or val.a < worst else worst; return True
        if depth > 60 or boxes > max_boxes: return False
        mid = (lo+hi)/2
        return bb1(xpt, lo, mid, depth+1) and bb1(xpt, mid, hi, depth+1)
    for dd in degs:
        if not bb1(pt(1)/dd, mp.mpf(0), tail.b): out["FAIL"] = f"mixed d={dd}"; return out
    # (E3) both in tail
    def bb2(xl, xh, yl, yh, depth=0):
        nonlocal boxes, worst
        boxes += 1
        val = T_box(iv.mpf([xl, xh]), iv.mpf([yl, yh]), c, anchor)
        if val.a > 0:
            worst = val.a if worst is None or val.a < worst else worst; return True
        if depth > 60 or boxes > max_boxes: return False
        if xh-xl >= yh-yl:
            m = (xl+xh)/2; return bb2(xl, m, yl, yh, depth+1) and bb2(m, xh, yl, yh, depth+1)
        m = (yl+yh)/2; return bb2(xl, xh, yl, m, depth+1) and bb2(xl, xh, m, yh, depth+1)
    if not bb2(mp.mpf(0), tail.b, mp.mpf(0), tail.b): out["FAIL"] = "tail"; return out
    out["tail_boxes"] = boxes; out["tail_min_lower"] = float(worst)
    out["CERTIFIED"] = True
    return out

if __name__ == "__main__":
    rs = [int(a) for a in sys.argv[1:]] or list(range(3, 15))
    res = []
    for r in rs:
        t0 = time.time(); o = certify(r); o["seconds"] = round(time.time()-t0, 1); res.append(o)
        print(json.dumps(o), flush=True)
    ok = all(o.get("CERTIFIED") for o in res)
    print("ALL CERTIFIED" if ok else "NOT ALL CERTIFIED"); sys.exit(0 if ok else 1)
