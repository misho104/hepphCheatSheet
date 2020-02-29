(* ::Package:: *)

AppendTo[$Path, "/Users/misho/HEPcodes/LoopTools/build"];
Install["LoopTools"];


{musq, delta} = {RandomReal[], RandomReal[]}*1000
SetMudim[musq];
SetDelta[delta];
\[CapitalDelta]\[Epsilon]Log\[Mu] = delta + Log[musq];


A0IntegrandX[aa0, M_] := M(\[CapitalDelta]\[Epsilon]Log\[Mu]+1-HoldIntegrate[Log[M],{x,0,1}])
B0IntegrandX[bb0,P_,M0_,M1_] := \[CapitalDelta]\[Epsilon]Log\[Mu] - HoldIntegrate[Log[-x(1-x)P+x M1+(1-x)M0],{x,0,1}]
(*9809213*)
C0Analytic[cc0, P1_, P2_, P3_, M1_, M2_, M3_] := Module[{
    Q1=x(1-x)(1-y)P2 + x^2 y(1-y)P3 + x(1-x)y P1 - x y M1 - (1-x) M2 - x(1-y) M3},
  HoldIntegrate[x/Q1, {x, 0, 1}, {y, 0, 1}]]
(*PaVe1979 / http://www.phy.pku.edu.cn/~qhcao/resources/cpy/2014/CAO_scalar_thesis.pdf*)
C0Analytic2[cc0, P1_, P2_, P3_, M1_, M2_, M3_] := Module[{  
    Q2=-P2x^2-P1 y^2+(P1+P2-P3)x y + (P2-M2+M3)x + (M2-M1+P3-P2)y-M3},
  HoldIntegrate[1/Q2, {x, 0, 1}, {y, 0, x}]]
CompareA0 := Module[{params = {aa0, Table[RandomReal[],1]}//Flatten},
  {A0i@@params, A0IntegrandX@@params}] /. HoldIntegrate->NIntegrate
CompareB0 := Module[{params = {bb0, Table[RandomReal[],3]}//Flatten},
  {B0i@@params, B0IntegrandX@@params}]/. HoldIntegrate->NIntegrate
CompareC0 := Module[{params = {cc0, Table[RandomReal[],6]}//Flatten, lambda},
  If[(params[[2]]-params[[3]]-params[[4]])^2 - 4*params[[3]]*params[[4]] < 0, Return[CompareC0]];
  {C0i@@params, C0Analytic@@params, C0Analytic2@@params}]/. HoldIntegrate->NIntegrate


Do[CompareA0//Print,5]
Do[CompareB0//Print,5]
Do[CompareC0//Print,30]


SortC0[exp_] := exp /. {
  C0i[cc0,p1_,p2_,p3_,m1_,m2_,m3_]:>Module[{
      a={p1,m3}, b={p2,m1}, c={p3,m2}
    },
    {a,b,c} = Sort[{a,b,c}];
    C0iS[cc0,a[[1]],b[[1]],c[[1]],b[[2]],c[[2]],a[[2]]]
  ]
};
