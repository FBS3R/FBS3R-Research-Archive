import math
c=2.99792458e8; Mpc=3.0856775814913673e22; lP=1.616255e-35; phi=(1+5**.5)/2
def q_of(H0,OL): L=3*(H0*1e3/Mpc)**2*OL/c**2; return 3*math.pi/(lP**2*L)
n=lambda q: math.log(math.sqrt(q/math.pi))/math.log(phi)
qo=q_of(67.4,0.685); print("q_obs=%.10e n=%.6f"%(qo,n(qo)))
eps=math.pi*phi**584/qo-1; print("eps=%.7f pi/50=%.7f diff=%.3e"%(eps,math.pi/50,eps-math.pi/50))
q0=math.pi*phi**584/(1+math.pi/50); print("q0=%.10e q0/qobs-1=%.3e"%(q0,q0/qo-1))
Xi=math.exp(-0.000831065239070442); u=math.log(q0/Xi); print("u_run=%.10f bg2=%.16f"%(u,16*math.pi**2/u))
for Xi2 in (0.5,1.0,2.0): u=math.log(q0/Xi2); print(" Xi=%g -> bg2=%.10f, reproduces q0: %s"%(Xi2,16*math.pi**2/u, abs(Xi2*math.exp(u)/q0-1)<1e-12))
for H,O in [(67.4,0.685),(73.04,0.685),(67.4,0.70),(60,0.685)]: print(H,O,"n=%.4f"%n(q_of(H,O)))
# phi-shell spacing in Lambda: factor phi^-2 per shell
print("Lambda ratio between adjacent shells phi^2=%.4f"%phi**2)
# d_val alternatives
for d in range(1,9): print(d, "1+pi/(2d^2)=%.5f"%(1+math.pi/(2*d*d)))
# H0 window giving N=292 at OL=0.685
lo=[H for H in [x/10 for x in range(300,1500)] if round(n(q_of(H,0.685)))==292]; print("H0 range for 292:",min(lo),max(lo))
