#!/usr/bin/env python3
"""Controls. (1) Mutations that MUST make the certificate fail. (2) Exhaustive n<=4 matrix check of the all-e
bound for every r=3..14. (3) Hill-climbing attack for n=5..16 at r=3,4,6,8."""
import json, math, random, itertools, sys
import numpy as np
import certify_family as C
res={}
# (1) mutations
def run(r, anchor, K):
    saved=C.PLAN[r] if r in C.PLAN else None
    C.PLAN[r]=(anchor,K)
    try: o=C.certify(r, N_factor=6)
    finally:
        if saved: C.PLAN[r]=saved
        else: del C.PLAN[r]
    return o
muts={"r10_linear_anchor":(10,"linear",1),"r13_without_degree2_cofactor":(13,"cubic",1),
      "r15_cubic_K2_outside_family":(15,"cubic",2),"r16_cubic_K2_outside_family":(16,"cubic",2),
      "r12_linear_anchor":(12,"linear",2)}
mres={}
for k,(r,a,K) in muts.items():
    o=run(r,a,K); mres[k]={"certified":bool(o.get("CERTIFIED")),"fail":o.get("FAIL"),"window_min":o.get("window_min_lower"),"argmin":o.get("window_argmin")}
res["mutations_must_fail"]=mres
mut_ok=all(not v["certified"] for v in mres.values())
# (2) exhaustive n<=4
def consts_f(r):
    t=r-1;R=r*r;v=R-t;g=(v/t-math.log(R/t))/v**2
    al=1/r-1/(2*t)+(r-0.5)*g; ell=(math.log(r)+(v-1)/2*math.log(t))/v
    return al,ell
worst={}
mats=[]
for n in range(1,5):
    for bits in range(1<<(n*n)):
        A=np.array([(bits>>k)&1 for k in range(n*n)],dtype=float).reshape(n,n)
        s,ld=np.linalg.slogdet(A)
        if s!=0: mats.append((n,int(A.sum()),ld))
for r in range(3,15):
    al,ell=consts_f(r)
    worst[r]=max(ld-(n*ell+al*(e-r*n)) for n,e,ld in mats)
res["exhaustive_n_le_4_max_slack"]={r:round(w,6) for r,w in worst.items()}
exh_ok=all(w<0 for w in worst.values())
# (3) hill climb
random.seed(7); np.random.seed(7); hc={}
for r in (3,4,6,8):
    al,ell=consts_f(r); best=-1e9
    for n in range(5,17):
        for rep in range(25):
            A=(np.random.rand(n,n)<random.choice([.15,.25,.35,.5])).astype(int)
            def sl(A):
                s,ld=np.linalg.slogdet(A.astype(float))
                return -1e9 if s==0 else ld-(n*ell+al*(A.sum()-r*n))
            cur=sl(A)
            for it in range(2500):
                i,j=random.randrange(n),random.randrange(n); A[i,j]^=1
                s=sl(A)
                if s>=cur or random.random()<0.002: cur=s
                else: A[i,j]^=1
                best=max(best,cur)
    hc[r]=round(best,6)
res["hill_climb_best_slack"]=hc
hc_ok=all(v<=1e-9 for v in hc.values())
res["ALL_OK"]=mut_ok and exh_ok and hc_ok
print(json.dumps(res,indent=1)); sys.exit(0 if res["ALL_OK"] else 1)
