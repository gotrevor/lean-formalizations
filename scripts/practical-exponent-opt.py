#!/usr/bin/env python3
"""Minimize Weingartner (2021) Thm 2 exponent beta(k,l) = (5k+l+2)/(6(k+1)) over known exponent pairs.

Vertices: Trudgian-Yang 2023 (arXiv:2306.05599) eq. (1.14) k0..k4; Tao-Trudgian-Yang 2025 (arXiv:2501.16779) Thm 20.
Closed under the A and B processes. Known-answer control: Bourgain alone must give 605/1242 (Weingartner Cor. 4).
"""
from fractions import Fraction as F

def A(p): k,l=p; return (k/(2*k+2),(k+l+1)/(2*k+2))
def B(p): k,l=p; return (l-F(1,2),k+F(1,2))
def beta(p): k,l=p; return (5*k+l+2)/(6*(k+1))
TY={'k0 Bourgain':(F(13,84),F(55,84)),'k1':(F(4742,38463),F(35731,51284)),'k2':(F(18,199),F(593,796)),
    'k3':(F(2779,38033),F(58699,76066)),'k4':(F(715,10238),F(7955,10238))}
TTY={'TTY1':(F(89,1282),F(997,1282)),'TTY2':(F(652397,9713986),F(7599781,9713986)),
     'TTY3':(F(10769,351096),F(609317,702192)),'TTY4':(F(89,3478),F(15327,17390))}
def closure(base,depth=5):
    out={}
    frontier=dict(base)
    for d in range(depth):
        new={}
        for name,p in frontier.items():
            out[name]=p
            for tag,f in (('A',A),('B',B)):
                q=f(p); n=tag+'·'+name
                if n not in out: new[n]=q
        frontier=new
    out.update(frontier); return out
for label,base in (('pre-2021 (Bourgain only)',{'k0 Bourgain':TY['k0 Bourgain']}),('TY23 hull',TY),('TY23+TTY25',{**TY,**TTY})):
    c=closure(base)
    best=min(c.items(),key=lambda kv:beta(kv[1]))
    print(f"{label:28s} best {best[0]:20s} beta={float(beta(best[1])):.6f} = {beta(best[1])}  pair={best[1]}")
c=closure({**TY,**TTY})
for n,p in sorted(c.items(),key=lambda kv:beta(kv[1]))[:8]: print(f"  {n:22s} {float(beta(p)):.6f}  ({float(p[0]):.5f},{float(p[1]):.5f})")
assert min(beta(p) for p in closure({'k0':TY['k0 Bourgain']}).values()) == F(605,1242)
assert min(beta(p) for p in closure({**TY,**TTY}).values()) == F(15144869,31099149)
print("checks ok")
