(* ::Package:: *)

(* Time-Stamp: <2020-8-8 15:27:19> *)
(* The content in this note, written by Sho Iwamoto, is still a private note and not under any license.
   You may not copy, distribute, or modify it, or create a derived work without permission. *)


$Assumptions = {T>0, e>=0, m>=0, \[Mu]\[Element]Reals};
kUp[exp_, max_] := (exp //. { BesselK[n_Integer /; n < max-1, z_] :> BesselK[n + 2, z] - (2/z) (n+1) BesselK[n+1, z] })
kDown[exp_]     := (exp //. { BesselK[n_Integer /; n >= 2, z_] :> BesselK[n - 2, z] + (2/z) (n-1) BesselK[n-1, z] })

fBE[e_, \[Mu]_, T_] := 1 / (Exp[(e-\[Mu])/T] - 1)
fFD[e_, \[Mu]_, T_] := 1 / (Exp[(e-\[Mu])/T] + 1)
fMB[e_, \[Mu]_, T_] := 1 / (Exp[(e-\[Mu])/T] + 0)


n[f_, m_, \[Mu]_, T_] := Integrate[(4Pi)Sqrt[e^2-m^2]e    f[e, \[Mu], T] / (2Pi)^3, {e,m,\[Infinity]}]
\[Rho][f_, m_, \[Mu]_, T_] := Integrate[(4Pi)Sqrt[e^2-m^2]e^2  f[e, \[Mu], T] / (2Pi)^3, {e,m,\[Infinity]}]
p[f_, m_, \[Mu]_, T_] := Integrate[(4Pi/3)Sqrt[e^2-m^2]^3 f[e, \[Mu], T] / (2Pi)^3, {e,m,\[Infinity]}]
\[CapitalDelta]int[f_, m_, \[Mu]_, T_, e_] :=       (4Pi)Sqrt[e^2-m^2]e    (f[e, \[Mu], T]-f[e, -\[Mu], T]) / (2Pi)^3;
\[CapitalDelta][f_, m_, \[Mu]_, T_] := Integrate[\[CapitalDelta]int[f,m,\[Mu],T, e], {e,m,\[Infinity]}]


nMB = n[fMB, m, \[Mu], T] /. {m->x T, \[Mu]-> \[Nu] T} // FullSimplify
\[Rho]MB = \[Rho][fMB, m, \[Mu], T] /. {m->x T, \[Mu]-> \[Nu] T} // kUp[#, 2]& // Simplify
pMB = p[fMB, m, \[Mu], T] /. {m->x T, \[Mu]-> \[Nu] T} // FullSimplify


n[fFD, m, 0, 1]
\[Rho][fFD, m, 0, 1]
p[fFD, m, 0, 1]
n[fBE, m, 0, 1]
\[Rho][fBE, m, 0, 1]
p[fBE, m, 0, 1]


nFD = n[fFD, m, \[Mu], T]
\[Rho]FD = \[Rho][fFD, m, \[Mu], T]
pFD = p[fFD, m, \[Mu], T]
nBE = n[fBE, m, \[Mu], T]
\[Rho]BE = \[Rho][fBE, m, \[Mu], T]
pBE = p[fBE, m, \[Mu], T]


{nFD, \[Rho]FD, pFD} /. Integrate->Hold[Integrate] //. {e -> e0+m, {e0+m, m, \[Infinity]} -> {e0, 0, \[Infinity]}, T->1} //. Hold[Integrate][a_, b_] :> Hold[Integrate][Series[a, {m, 0, 2}]//Normal, b] // FullSimplify[#, {e0>0}]&
{nFD0, \[Rho]FD0, pFD0} = ReleaseHold[%] // Collect[#, m, FullSimplify]&
\[CapitalDelta][fFD, m, \[Mu], T] /. Integrate->Hold[Integrate] //. {e -> e0+m, {e0+m, m, \[Infinity]} -> {e0, 0, \[Infinity]}, T->1} //. Hold[Integrate][a_, b_] :> Hold[Integrate][Series[a, {m, 0, 3}]//Normal//Collect[#, m, FullSimplify[#, {e0>0}]&]&, b]
ReleaseHold[%]


{nBE, \[Rho]BE, pBE} /. Integrate->Hold[Integrate] //. {e -> e0+m, {e0+m, m, \[Infinity]} -> {e0, 0, \[Infinity]}, T->1} //. Hold[Integrate][a_, b_] :> Hold[Integrate][Series[a, {m, 0, 1}]//Normal, b] // FullSimplify[#, {e0>0}]&
ReleaseHold[%]
%/.m->0


Series[\[CapitalDelta]int[fFD,m,\[Mu],T,e], {\[Mu],0, 1}] // Normal
Integrate[%, {e, m, \[Infinity]}]
Series[\[CapitalDelta]int[fBE,m,\[Mu],T,e], {\[Mu],0, 1}] // Normal
Integrate[%, {e, m, \[Infinity]}]


Series[\[CapitalDelta]int[fFD,m,\[Mu],T,e] /. {e->\[Epsilon]0+m}, {\[Mu],0, 1}] // Normal // FullSimplify
List@@(Series[%, {m, 0, 2}] // Normal)
Integrate[%, {\[Epsilon]0, 0, \[Infinity]}]


Series[\[CapitalDelta]int[fBE,m,\[Mu],T,e] /. {e->\[Epsilon]0+m}, {\[Mu],0, 1}] // Normal // FullSimplify
List@@(Series[%, {m, 0, 2}] // Normal)
Integrate[%, {\[Epsilon]0, 0, \[Infinity]}]


\[Xi][sign:1|-1, x_] := NIntegrate[(k E^k Sqrt[k^2-x^2])/((E^k+sign)^2 \[Pi]^2),{k,x,\[Infinity]}]
\[Xi]MB = Integrate[(k E^k Sqrt[k^2-x^2])/((E^k+0)^2 \[Pi]^2),{k,x,\[Infinity]}]
Plot[{\[Xi][1,x], \[Xi][-1,x], \[Xi]MB}, {x, 0, 10}]
Plot[{\[Xi][1,x], (1/6 - x^2/(4Pi^2))},{x,0,4}]
Plot[{\[Xi][-1,x], (1/3 - x/Pi^2)},{x,0,4}]



