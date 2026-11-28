# Numerical cross-checks (DISPROVER frontier round): tanh bound/sharpness, archive Lambda numbers n(q_obs)=291.937, 1+pi/50 residual.
# Evidence only, not a Lean proof. Run: python3 -I lambda_archive_numbers.py
import math, random
# tanh sharpness
random.seed(1)
worst=0
for _ in range(2000):
    a=random.uniform(0,5); x=random.uniform(0.01,5); y=x+random.uniform(0,5)
    ex,ey=math.exp(-a*x),math.exp(-a*y); c=2*ex*ey/(ex+ey)
    th=math.tanh(a*(y-x)/2)
    errs=[abs((c/t)/(math.exp(-a*t)/t)-1) for t in [x+(y-x)*i/200 for i in range(201)]]
    worst=max(worst,max(errs)-th)
    assert abs(errs[0]-th)<1e-9 and abs(errs[-1]-th)<1e-9
print("sharpness: max(err)-tanh =",worst)
# lower bound: random positive atomic rho, check sup rel err on [x,y] >= tanh
viol=0
for _ in range(2000):
    a=random.uniform(0.1,3); x=random.uniform(0.1,3); y=x+random.uniform(0.01,3)
    k=random.randint(1,4); s=[random.uniform(0,5)*random.random() for _ in range(k)]; w=[random.uniform(0,3) for _ in range(k)]
    # best scalar multiple: scale to minimise endpoint error (cheap search)
    def G(t): return sum(wi/(t+si) for wi,si in zip(w,s))
    best=1e9
    for lam in [10**(e/50) for e in range(-300,300)]:
        e=max(abs(lam*G(t)*t*math.exp(a*t)-1) for t in [x+(y-x)*i/50 for i in range(51)])
        best=min(best,e)
    if best < math.tanh(a*(y-x)/2)-1e-6: viol+=1
print("lower-bound violations:",viol)
# archive number
c=2.99792458e8; Mpc=3.0856775814913673e22
H0=67.4e3/Mpc; OL=0.685; lP=1.616255e-35
Lam=3*H0**2*OL/c**2
q=3*math.pi/(lP**2*Lam)
phi=(1+5**.5)/2
n=math.log(math.sqrt(q/math.pi))/math.log(phi)
print("Lambda_obs=%.6e m^-2  q_obs=%.6e  n=%.6f round=%d"%(Lam,q,n,round(n)))
# sensitivity
for H in (67.0,67.4,67.8,73.0):
  for O in (0.68,0.685,0.69):
    L=3*(H*1e3/Mpc)**2*O/c**2; qq=3*math.pi/(lP**2*L); print(H,O,"%.4f"%(math.log(math.sqrt(qq/math.pi))/math.log(phi)))
