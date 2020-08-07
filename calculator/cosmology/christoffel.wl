(* ::Package:: *)

(* Time-Stamp: <2020-8-8 15:27:19> *)
(* The content in this note, written by Sho Iwamoto, is still a private note and not under any license.
   You may not copy, distribute, or modify it, or create a derived work without permission. *)


coordinatesArray = {t, x, y, z};
metricMatrix = {
  {1, 0, 0, 0},
  {0, -a[t]^2, 0, 0},
  {0, 0, -a[t]^2, 0},
  {0, 0, 0, -a[t]^2}
} - (a[t]^2 K / (1-K(x^2+y^2+z^2))){
  {0, 0, 0, 0},
  {0, x^2, x y, x z},
  {0, y x, y^2, y z},
  {0, z x, z y, z^2}
};
coordinates[i_] := coordinatesArray[[i+1]];
metric[{}, {i_,j_}] := metricMatrix[[i+1, j+1]];
metric[{i_,j_}, {}] := Inverse[metricMatrix][[i+1,j+1]];


AffineConnection[g_, x_][{l_},{k_, j_}] := Sum[
  (1/2) g[{l,m},{}](D[g[{},{m,k}], x[j]] + D[g[{},{m,j}], x[k]] - D[g[{},{k,j}], x[m]])
  , {m, 0, 3}]
RiemannTensor[g_,x_][{s_}, {i_, j_, k_}] := Module[{
   \[CapitalGamma]=Table[AffineConnection[g,x][{i1}, {i2, i3}], {i1,0,3},{i2,0,3}, {i3,0,3}],
   ss = s+1, ii = i+1, jj = j+1, kk = k+1
  },
  D[\[CapitalGamma][[ss,jj,kk]], x[i]] - D[\[CapitalGamma][[ss,ii,kk]], x[j]] + Sum[\[CapitalGamma][[ll,jj,kk]]*\[CapitalGamma][[ss,ii,ll]] - \[CapitalGamma][[ll,ii,kk]]*\[CapitalGamma][[ss,jj,ll]], {ll, 1, 4}]]
RicciTensor[g_,x_][{}, {i_,j_}] := Sum[RiemannTensor[g,x][{k},{i,k,j}], {k,0,3}]
RicciScalar[g_,x_] := Sum[RicciTensor[g,x][{},{i,j}]metric[{i,j},{}], {i,0,3},{j,0,3}]


RicciTensor[metric,coordinates][{},{0,0}]//Simplify


RicciScalar[metric,coordinates] // Simplify


Rij = Table[RicciTensor[metric,coordinates][{},{i,j}],{i,0,3},{j,0,3}] // Simplify


Table[
  metric[{i,m}]RicciTensor[metric,coo


Sum[
  
//Simplify


(* ::Subsection:: *)
(*Validation: to spherical coordinates*)


ToSpherical[exp_, {x_, y_, z_}, {r_, \[Theta]_, \[Phi]_}] := Module[{
    x0 = r Sin[\[Theta]] Cos[\[Phi]],
    y0 = r Sin[\[Theta]] Sin[\[Phi]],
    z0 = r Cos[\[Theta]]
  },
  exp //. {x->x0, y->y0, z->z0,
    d[x]->{D[x0,r],D[x0,\[Theta]],D[x0,\[Phi]]}.{d[r],d[\[Theta]],d[\[Phi]]},
    d[y]->{D[y0,r],D[y0,\[Theta]],D[y0,\[Phi]]}.{d[r],d[\[Theta]],d[\[Phi]]},
    d[z]->{D[z0,r],D[z0,\[Theta]],D[z0,\[Phi]]}.{d[r],d[\[Theta]],d[\[Phi]]}}]

{{d[t],d[x],d[y],d[z]}}.metricMatrix.{{d[t]},{d[x]},{d[y]},{d[z]}}
ToSpherical[%, {x,y,z}, {r,\[Theta],\[Phi]}] // Simplify



