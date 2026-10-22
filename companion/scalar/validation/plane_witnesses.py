#!/usr/bin/env python3
"""Equality witnesses: incidence matrices of PG(2,q) over GF(q), q = r-1, built from scratch.
GF(p^k) via an explicit irreducible polynomial; checks A A^T = (r-1) I + J, every row/column has r ones,
e = r*v, and |det A| = D_r = r (r-1)^((v-1)/2) by exact integer Bareiss elimination."""
import itertools, json, sys
IRRED = {4:(2,[1,1]), 8:(2,[1,1,0]), 9:(3,[1,0])}   # non-leading coeffs low->high of monic x^2+x+1, x^3+x+1, x^2+1
class GF:
    def __init__(s,q):
        s.q=q
        if q in IRRED:
            s.p,mod=IRRED[q]; s.k=len(mod)
            s.mod=mod+[1]  # monic
        else: s.p,s.k,s.mod=q,1,None
        s.els=list(itertools.product(range(s.p),repeat=s.k))
    def add(s,a,b): return tuple((x+y)%s.p for x,y in zip(a,b))
    def mul(s,a,b):
        if s.k==1: return ((a[0]*b[0])%s.p,)
        prod=[0]*(2*s.k-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b): prod[i+j]=(prod[i+j]+x*y)%s.p
        for deg in range(len(prod)-1,s.k-1,-1):      # reduce by monic modulus
            c=prod[deg]
            if c:
                for i,m in enumerate(s.mod): prod[deg-s.k+i]=(prod[deg-s.k+i]-c*m)%s.p
        return tuple(prod[:s.k])
    def zero(s): return (0,)*s.k
    def one(s): return (1,)+(0,)*(s.k-1)
def check_field(F):
    nz=[a for a in F.els if a!=F.zero()]
    for a in nz:  # every nonzero has an inverse => field
        if not any(F.mul(a,b)==F.one() for b in nz): return False
    return True
def points(F):
    pts=[]
    for v in itertools.product(F.els,repeat=3):
        if all(c==F.zero() for c in v): continue
        first=next(c for c in v if c!=F.zero())
        if first==F.one(): pts.append(v)
    return pts
def dot(F,a,b):
    s=F.zero()
    for x,y in zip(a,b): s=F.add(s,F.mul(x,y))
    return s
def bareiss_det(M):
    M=[row[:] for row in M]; n=len(M); sign=1; prev=1
    for k in range(n-1):
        if M[k][k]==0:
            sw=next((i for i in range(k+1,n) if M[i][k]!=0),None)
            if sw is None: return 0
            M[k],M[sw]=M[sw],M[k]; sign=-sign
        for i in range(k+1,n):
            for j in range(k+1,n):
                M[i][j]=(M[i][j]*M[k][k]-M[i][k]*M[k][j])//prev
        prev=M[k][k]
    return sign*M[n-1][n-1]
out=[]; ok=True
for q in [2,3,4,5,7,8,9,11,13]:
    F=GF(q); assert check_field(F), q
    P=points(F); n=len(P); r=q+1; v=r*r-r+1
    A=[[1 if dot(F,l,p)==F.zero() else 0 for p in P] for l in P]
    rows=all(sum(row)==r for row in A); cols=all(sum(A[i][j] for i in range(n))==r for j in range(n))
    gram=all(sum(A[i][k]*A[j][k] for k in range(n))==((r-1)+1 if i==j else 1) for i in range(n) for j in range(n))
    det=abs(bareiss_det(A)); D=r*(r-1)**((v-1)//2)
    rec=dict(q=q,r=r,v=v,n=n,ones=sum(map(sum,A)),regular=rows and cols,gram_tI_plus_J=gram,abs_det_equals_D=(det==D),det_digits=len(str(det)))
    ok&=(n==v and rows and cols and gram and det==D and rec["ones"]==r*v)
    out.append(rec); print(json.dumps(rec),flush=True)
print("ALL PLANE WITNESSES EXACT" if ok else "WITNESS FAILURE"); sys.exit(0 if ok else 1)
