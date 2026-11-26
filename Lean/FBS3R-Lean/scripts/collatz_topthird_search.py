import math,bisect
F=[0,1,1]
while F[-1]<10**8: F.append(F[-1]+F[-2])
def h(n): return bisect.bisect_right(F,n)-1  # largest k with F_k<=n (k>=2)
phi=(1+5**.5)/2
bad=[];bad3=0;tot=0
for n in range(1,2000001,2):
    d=h(3*n+1)-h(n)
    x=math.log(5**.5*n,phi); fr=x-math.floor(x)
    if d>3: bad3+=1
    if fr<2/3 and d>2: bad.append((n,d,round(fr,4)))
print("odd n<=2e6: steps with increase>3:",bad3,"; non-top-third with increase 3:",len(bad), bad[:10])
