from itertools import product
S0=[t for t in product(range(5),repeat=4) if sum(t)==8]
pins=[(0,4-l,l,4) for l in range(5)]
# S+ eq at e (sum 7): sum_i (e_i+1) phi(e+d_i) for e_i<4 ; S- eq at e (sum 9): sm1 f m = (5-m) f(m-1) if m>0
eqs=[]; eqs_d={}
for e in product(range(5),repeat=4):
    if sum(e)==7:
        eqs.append(('p',e,[tuple(e[j]+(j==i) for j in range(4)) for i in range(4) if e[i]<4])); eqs_d[('p',e)]=eqs[-1][2]
    if sum(e)==9:
        eqs.append(('m',e,[tuple(e[j]-(j==i) for j in range(4)) for i in range(4) if e[i]>0])); eqs_d[('m',e)]=eqs[-1][2]
known=set(pins); steps=[]
ch=True
while ch:
    ch=False
    for kind,e,vs in eqs:
        unk=[v for v in vs if v not in known]
        if len(unk)==1:
            known.add(unk[0]); steps.append((kind,e,unk[0])); ch=True
print(len(known), len(S0), len(steps))
print(sum(1 for s in steps if s[0]=='p'))
