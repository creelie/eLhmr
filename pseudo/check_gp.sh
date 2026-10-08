#!/bin/sh
# Third check with PARI/GP: usage check_gp.sh FILE EPS
F=$1; E=$2
gp -q -s 2000000000 <<GP
v = readvec("$F");
k = #v; e = $E;
ok = 1;
for(i=1,k, if(v[i]<5 || v[i]%2==0 || v[i]%3==0, ok=0; print("bad entry ",i)));
for(i=1,k-1, if(v[i]>=v[i+1], ok=0; print("not increasing at ",i)));
P = prod(i=1,k, v[i]); Q = prod(i=1,k, v[i]-1);
if(P + e != 2*Q, ok=0; print("equation fails"));
for(i=1,k, for(j=1,k, if(gcd(v[i], v[j]-1)!=1, ok=0; print("gcd fails ",i," ",j))));
print(if(ok, "PARI/GP: OK", "PARI/GP: FAILED"), "  k=", k, " eps=", e, " digits(P)=", #Str(P));
quit
GP
