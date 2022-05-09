(* ::Package:: *)

(* :Time-Stamp: <2022-5-2 16:10:26> *)
(* :Author: Sho Iwamoto / Misho *)
(* :Copyright: 2022 Sho Iwamoto / Misho *)
(* This file is licensed under the Apache License, Version 2.0.
   You may not use this file except in compliance with it.
   See the LICENSE file attached or the following URL for the full license information.
   https://www.apache.org/licenses/LICENSE-2.0
*)


(* Path configutation *)
If[$FrontEnd =!= Null, SetDirectory[NotebookDirectory[]]];
<<DiracAlgebra`


On[Assert];
LorSum[a_Function] := Sum[a[i], {i, 0, 3}];
Slashed[p_]:=LorSum[p[#]GammaMatrix[None,#]&]
SqrtSigmaDot[p] . SqrtSigmaDot[p] == LorSum[p[#] SigmaMatrix[None, #]&];
Assert[FullSimplify[% //. {Mass[p]->Sqrt[p[0]^2-p[1]^2-p[2]^2-p[3]^2]}]]
SqrtSigmaBarDot[p] . SqrtSigmaBarDot[p] == LorSum[p[#] SigmaBarMatrix[None, #]&];
Assert[FullSimplify[% //. {Mass[p]->Sqrt[p[0]^2-p[1]^2-p[2]^2-p[3]^2]}]]

SpinorUBar[p,\[Xi]] == ConjugateTranspose[SpinorU[p,\[Xi]]] . GammaMatrix[0, None];
Assert[% // FullSimplify[#, {p[_]\[Element]Reals, p[0]>0, Mass[p]>0}]&]
SpinorVBar[p,\[Xi]] == ConjugateTranspose[SpinorV[p,\[Xi]]] . GammaMatrix[0, None];
Assert[% // FullSimplify[#, {p[_]\[Element]Reals, p[0]>0, Mass[p]>0}]&]

MatrixC . Transpose[ConjugateTranspose[SpinorU[p,\[Xi]]] . GammaMatrix[0,None]]//FunctionExpand// Simplify[#,{Mass[p]>0,p[0]>0,p[_]\[Element]Reals}]&
% == SpinorV[p,\[Xi]] // FullSimplify


SpinorV[p,\[Xi]] . SpinorVBar[p,\[Xi]] /. {\[Xi][1]->1,\[Xi][2]->0};
SpinorV[p,\[Xi]] . SpinorVBar[p,\[Xi]] /. {\[Xi][1]->0,\[Xi][2]->1};
%+%% - (LorSum[GammaMatrix[None,#]p[#]&]-Mass[p]IdentityMatrix[4])//FullSimplify;
%/.{Mass[p]->Sqrt[p[0]^2-p[1]^2-p[2]^2-p[3]^2]}


pp = LorSum[GammaMatrix[None,#]p[#]&]


(pp-m GammaFive . GammaFive) . Transpose[{{1,0,1,0}}]==0 /. {p[1|2|3]->0,p[0]->m}
(pp-m GammaFive . GammaFive) . Transpose[{{0,1,0,1}}]==0 /. {p[1|2|3]->0,p[0]->m}
(pp+m GammaFive . GammaFive) . Transpose[{{1,0,-1,0}}]==0 /. {p[1|2|3]->0,p[0]->m}
(pp+m GammaFive . GammaFive) . Transpose[{{0,1,0,-1}}]==0 /. {p[1|2|3]->0,p[0]->m}
(pp-m GammaFive . GammaFive) . Transpose[{{1,0,1,0}}]==0 /. {p[1|2|3]->0,p[0]->m}
(pp-m GammaFive . GammaFive) . Transpose[{{0,1,0,1}}]==0 /. {p[1|2|3]->0,p[0]->m}
(pp+m GammaFive . GammaFive) . Transpose[{{1,0,-1,0}}]==0 /. {p[1|2|3]->0,p[0]->m}
(pp+m GammaFive . GammaFive) . Transpose[{{0,1,0,-1}}]==0 /. {p[1|2|3]->0,p[0]->m}


Sum[PauliMatrix[i]p[i],{i,3}]/


pp . GammaFive . GammaFive . pp . GammaFive//FullSimplify


LorSum[GammaMatrix[None,#]p[#]&]//Eigenvectors
%*Sqrt[p[0]^2-p[1]^2-p[2]^2-p[3]^2]
%/.Sqrt[p[0]^2-p[1]^2-p[2]^2-p[3]^2]->0


GammaMatrix[1,None]


MatrixRank[]


Exit[]


SpinorU[p,\[Xi]1] . SpinorUBar[p,\[Xi]1]+SpinorU[p,\[Xi]2] . SpinorUBar[p,\[Xi]2];
hoge = Expand[%]//.{
  \[Xi]1[1]Conjugate[\[Xi]1[1]]->1-\[Xi]1[2]Conjugate[\[Xi]1[2]],
  \[Xi]2[1]Conjugate[\[Xi]2[1]]->1-\[Xi]2[2]Conjugate[\[Xi]2[2]],
  \[Xi]1[1]Conjugate[\[Xi]2[1]]->\[Xi]1[2]Conjugate[\[Xi]2[2]],
  \[Xi]2[1]Conjugate[\[Xi]1[1]]->\[Xi]2[2]Conjugate[\[Xi]1[2]],
  Mass[p]->Sqrt[p[0]^2-p[1]^2-p[2]^2-p[3]^2]
}  // Collect[#, \[Xi]2[_], Simplify]&;
%[[1,1]]


FullSimplify[%]



%+%% //FullSimplify;
%/.{Mass[p]->Sqrt[p[0]^2-p[1]^2-p[2]^2-p[3]^2]}


.


hoge=SpinorU[p,\[Xi]] . SpinorUBar[p,\[Xi]] - (1/2) (IdentityMatrix[4] + k GammaFive . LorSum[GammaMatrix[None,#]s[#]&]) . (LorSum[GammaMatrix[None,#]p[#]&]+Mass[p]IdentityMatrix[4]);


hoge[[2,3]]-hoge[[3,2]]//ExpandAll//Simplify[#, s[_]\[Element]Reals]&
%/.{p[1|2]->0,p[0]->Sqrt[Mass[p]^2-p[3]^2]}//FullSimplify





%131/.{s[0]->0,Sqrt[s[1]^2+s[2]^2+s[3]^2]->1}//Simplify


Expand[%]


ConjugateTranspose[{{\[Xi]1[1]},{\[Xi]1[2]}}] . {{\[Xi]1[1]},{\[Xi]1[2]}} == {{1}} 
ConjugateTranspose[{{\[Xi]1[1]},{\[Xi]1[2]}}] . {{\[Xi]2[1]},{\[Xi]2[2]}} == {{0}} 
ConjugateTranspose[{{\[Xi]2[1]},{\[Xi]2[2]}}] . {{\[Xi]2[1]},{\[Xi]2[2]}} == {{1}} 


{\[Xi]1, \[Xi]2} = Transpose[MatrixExp[I LorSum[(1/2)SigmaMatrix[None, #]s[#]&]]]


MatrixExp[(I Pi)/2 LorSum[SigmaMatrix[None, #]s[#]&]] /. {s[0]->0,Sqrt[s[1]^2+s[2]^2+s[3]^2]->1} // FullSimplify
%[[1]]//Norm//ComplexExpand//Simplify


%[[1]]


A[x_,y_]:=x . y-y . x
A[, \[Sigma][1]] //FullSimplify
MatrixExp[LorSum[I \[Sigma][#]s[#]&]] // FullSimplify


\[Sigma][i_] := (1/2)SigmaMatrix[i, None]
MatrixExp[LorSum[I \[Sigma][#]s[#]&]] . \[Sigma][3] - \[Sigma][1] . MatrixExp[LorSum[I \[Sigma][#]s[#]&]] // FullSimplify



Clear[Com,TDot];
Com[a_,TDot[b_,c__]] := TDot[Com[a,b],c] + TDot[b,Com[a,TDot[c]]]
TDot[a_]:=a
TDot[a_+b_]:=TDot[a]+TDot[b]
TDot[a___,Plus[b_,c_],d___]:=TDot[a,b,d]+TDot[a,c,d]
TDot[a___,TDot[b_,c_],d___]:=TDot[a,b,c,d]
TDot[a___, n_ b_, c___]/;NumericQ[n] := n TDot[a,b,c]

Com[M[a_,b_],M[c_,d_]] := TDot[(-I)(\[Eta][a,c]M[b,d]-\[Eta][a,d]M[b,c]+\[Eta][b,d]M[a,c]-\[Eta][b,c]M[a,d])]
Com[P[a_],M[b_,c_]] := TDot[(I)(\[Eta][a,b]P[c]-\[Eta][a,c]P[b])]
Com[M[b_,c_],P[a_]] := -Com[P[a],M[b,c]]


TDot[a___, b_\[Eta] c_,d___] := b TDot[a,c,d]






1/2 \[Epsilon][\[Mu],\[Nu],\[Rho],\[Sigma]] TDot[Com[M[\[Alpha],\[Beta]],TDot[P[\[Nu]],M[\[Rho],\[Sigma]]]]]//ExpandAll





Low\[Epsilon][m_,n_,r_,s_]:=-LeviCivitaTensor[4][[m+1,n+1,r+1,s+1]]
Low\[Epsilon][0,1,2,3]
Sum[Low\[Epsilon][m,n,r,s]S[m]p[n]GammaMatrix[r,None] . GammaMatrix[s,None],{m,0,3},{n,0,3},{r,0,3},{s,0,3}];
-2I LorSum[S[#]GammaMatrix[None,#]&] . LorSum[p[#]GammaMatrix[None,#]&] . GammaFive;
Expand[%%-%]//.{p[0] S[0]->p[1]S[1]+p[2]S[2]+p[3]S[3]}//Simplify



M = IdentityMatrix[4] m;


(Slashed[p]-M) . GammaFive . Slashed[s] . Slashed[p];
GammaFive . Slashed[s] . Slashed[p] . (Slashed[p]-M);
ExpandAll[%%-%];
%//.{p[0]^2 ->p[1]^2+p[2]^2+p[3]^2+m^2,p[1]s[1]->p[0] s[0]-p[2]s[2]-p[3]s[3]}//ExpandAll;
%//.{p[0]^2 ->p[1]^2+p[2]^2+p[3]^2+m^2,p[1]s[1]->p[0] s[0]-p[2]s[2]-p[3]s[3]}//ExpandAll;
%//.{p[0]^2 ->p[1]^2+p[2]^2+p[3]^2+m^2,p[1]^2s[1]->p[1](p[0] s[0]-p[2]s[2]-p[3]s[3])}//ExpandAll


LeviCivitaTensor[4]


(Slashed[p]+M) . SpinorV[p,\[Xi]] //.{m->Mass[p],p[0]->R Sqrt[Mass[p]^2+p[1]^2+p[2]^2+p[3]^2]} //FullSimplify
(Slashed[p]-M) . SpinorU[p,\[Xi]] //.{m->Mass[p],p[0]->R Sqrt[Mass[p]^2+p[1]^2+p[2]^2+p[3]^2]} //FullSimplify


1/2 GammaFive . Slashed[s] . Slashed[p]/.{s[0]->pn/m,s[i:1|2|3]->p[0]p[i]/pn/m}//ExpandAll;
%/.{p[0]^2->m^2+pn^2}//FullSimplify;
%/.{p[3]^2->pn^2-p[1]^2-p[2]^2}//FullSimplify


GammaMatrix[3,None]


GammaFive . Slashed[s] . Slashed[p] . GammaFive . Slashed[s] . Slashed[p]//ExpandAll;
%//.{p[3]^2->p[0]^2-m^2-p[1]^2-p[2]^2,s[1]p[1]->s[0]p[0]-s[2]p[2]-s[3]p[3]}//ExpandAll;
%//.{p[3]^2->p[0]^2-m^2-p[1]^2-p[2]^2,s[3]p[3]->s[0]p[0]-s[2]p[2]-s[1]p[1]}//ExpandAll;
%//.{s[3]^2->s[0]^2-s[1]^2-s[2]^2-ssq}//ExpandAll;
%/.(p|s)[2|1]->0//FullSimplify








Low\[Epsilon][m_,n_,r_,s_]:=-LeviCivitaTensor[4][[m+1,n+1,r+1,s+1]]
Low\[Epsilon][0,1,2,3]
f[m_,n_]:=(
Sum[Low\[Epsilon][m,n,r,s]GammaMatrix[r,None] . GammaMatrix[s,None],{r,0,3},{s,0,3}]==-I GammaFive . ( GammaMatrix[None,m] . GammaMatrix[None,n]- GammaMatrix[None,n] . GammaMatrix[None,m])
)


??


Table[f[m,n],{m,0,3},{n,0,3}]//Simplify


??Eta


High\[Epsilon][m_,n_,r_,s_]:=+LeviCivitaTensor[4][[m+1,n+1,r+1,s+1]]


F[\[Mu]_,\[Nu]_]:={
Sum[1/(4m) High\[Epsilon][\[Mu],\[Nu],\[Rho],\[Sigma]] I/4 (GammaMatrix[None,\[Rho]] . GammaMatrix[None,\[Sigma]]-GammaMatrix[None,\[Sigma]] . GammaMatrix[None,\[Rho]]),{\[Rho],0,3},{\[Sigma],0,3}],
1/(4m) GammaFive . GammaMatrix[\[Mu],None] . GammaMatrix[\[Nu],None]}



F[\[Mu]_,\[Nu]_]:={
Sum[High\[Epsilon][\[Mu],\[Nu],\[Rho],\[Sigma]]GammaMatrix[None,\[Rho]] . GammaMatrix[None,\[Sigma]],{\[Rho],0,3},{\[Sigma],0,3}],
-I GammaFive . (GammaMatrix[\[Mu],None] . GammaMatrix[\[Nu],None]-GammaMatrix[\[Nu],None] . GammaMatrix[\[Mu],None])}



F[3,2]


High\[Epsilon][0,2,1,3]


Eigenvalues[GammaFive . Slashed[s]]


1/(2m) GammaFive . Slashed[s] . Slashed[p]//.{s[0]->pp/m,s[i:1|2|3]->p[0]p[i]/pp/m} // Expand;
%//.{p[0]^2->m^2+pp^2,pp^2->p[1]^2+p[2]^2+p[3]^2}//Simplify;
%//.{p[0]^2->m^2+pp^2,pp^2->p[1]^2+p[2]^2+p[3]^2}//Simplify


(GammaFive*p[0]-GammaFive . GammaMatrix[0,None] . Slashed[p])/(2pp)


GammaMatrix[0,None] . GammaFive . Slashed[p]//ConjugateTranspose[#] . #==# . ConjugateTranspose[#]&//ComplexExpand


FullSimplify[%]


ComplexExpand[%]


FullSimplify[%]


Pu = (IdentityMatrix[4]m+Slashed[p])/(2m)
Pv = (IdentityMatrix[4]m-Slashed[p])/(2m)
PP = (IdentityMatrix[4]+h GammaFive . Slashed[s] . Slashed[p]/m)/2


2m PP . Pu - 1/2 (Slashed[p]+IdentityMatrix[4]m) . (IdentityMatrix[4]+h GammaFive . Slashed[s]) // Expand;
%/.{s[0]p[0]->Sum[s[i]p[i],{i,3}],p[0]^2->m^2+Sum[p[i]^2,{i,3}]}//Simplify;
%/.{s[0]p[0]->Sum[s[i]p[i],{i,3}],p[0]^2->m^2+Sum[p[i]^2,{i,3}]}//Expand



-2m PP . Pv - 1/2 (Slashed[p]-IdentityMatrix[4]m) . (IdentityMatrix[4]-h GammaFive . Slashed[s]) // Expand;
%/.{s[0]p[0]->Sum[s[i]p[i],{i,3}],p[0]^2->m^2+Sum[p[i]^2,{i,3}]}//Simplify;
%/.{s[0]p[0]->Sum[s[i]p[i],{i,3}],p[0]^2->m^2+Sum[p[i]^2,{i,3}]}//Expand



m+h p+sign s g p h h+ sign h s g m//FullSimplify


GammaFive . Slashed[e]/.{e[0]->pp/m,e[i:1|2|3]->p[0]p[i]/pp/m}


Slashed[p] . SpinorU[p,\[Xi]]-c SpinorU[p,\[Xi]]//FullSimplify


weak=With[{x = {{\[Xi][1]}, {\[Xi][2]}}, y = {{\[Eta][1]}, {\[Eta][2]}}}, ArrayFlatten[{{SqrtSigmaDot[p] . x}, {+SqrtSigmaBarDot[p] . y}}]]


Slashed[p] . weak - (Mass[p] weak) // ExpandAll;
%/.{p[0]^2->Mass[p]^2+p[1]^2+p[2]^2+p[3]^2}//FullSimplify





SpinorV[p,\[Xi]]


SpinorV2[p_, \[Eta]_] := With[{x = {{\[Eta][1]}, {\[Eta][2]}}}, ArrayFlatten[{{SqrtSigmaDot[p] . x}, {-SqrtSigmaBarDot[p] . x}}]]
SpinorVBar2[p_, \[Eta]_] := With[{x = Conjugate[{{\[Eta][1],\[Eta][2]}}]}, ArrayFlatten[{{x . SqrtSigmaDot[p], -x . SqrtSigmaBarDot[p]}}] . GammaMatrix[0, None]]
SpinorUBar[p,\[Xi]] . SpinorU[p,\[Zeta]] // FullSimplify[Expand[#] /. p[3]^2->p[0]^2-p[1]^2-p[2]^2-Mass[p]^2]&
SpinorVBar[p,\[Xi]] . SpinorV[p,\[Zeta]] // FullSimplify[Expand[#] /. p[3]^2->p[0]^2-p[1]^2-p[2]^2-Mass[p]^2]&
SpinorUBar[p,\[Xi]] . SpinorV[p,\[Zeta]] // FullSimplify[Expand[#] /. p[3]^2->p[0]^2-p[1]^2-p[2]^2-Mass[p]^2]&
SpinorVBar[p,\[Xi]] . SpinorU[p,\[Zeta]] // FullSimplify[Expand[#] /. p[3]^2->p[0]^2-p[1]^2-p[2]^2-Mass[p]^2]&
SpinorUBar[p,\[Xi]] . GammaMatrix[0, None] . SpinorU[p,\[Zeta]] // FullSimplify[Expand[#] /. p[3]^2->p[0]^2-p[1]^2-p[2]^2-Mass[p]^2]&
SpinorVBar[p,\[Xi]] . GammaMatrix[0, None] . SpinorV[p,\[Zeta]] // FullSimplify[Expand[#] /. p[3]^2->p[0]^2-p[1]^2-p[2]^2-Mass[p]^2]&

SpinorUBar[p,\[Xi]] . GammaMatrix[0, None] . SpinorV[q,\[Zeta]] // FullSimplify[Expand[#/.{q[0]->p[0], q[i:1|2|3]:>-p[i]}] /. p[3]^2->p[0]^2-p[1]^2-p[2]^2-Mass[p]^2 /. Mass[q]->Mass[p]]&
SpinorVBar[p,\[Xi]] . GammaMatrix[0, None] . SpinorU[q,\[Zeta]] // FullSimplify[Expand[#/.{q[0]->p[0], q[i:1|2|3]:>-p[i]}] /. p[3]^2->p[0]^2-p[1]^2-p[2]^2-Mass[p]^2 /. Mass[q]->Mass[p]]&
SpinorUBar[p,\[Xi]] . GammaMatrix[0, None] . SpinorU[q,\[Zeta]] // FullSimplify[Expand[#/.{q[0]->p[0], q[i:1|2|3]:>-p[i]}] /. p[3]^2->p[0]^2-p[1]^2-p[2]^2-Mass[p]^2 /. Mass[q]->Mass[p]]&
SpinorVBar[p,\[Xi]] . GammaMatrix[0, None] . SpinorV[q,\[Zeta]] // FullSimplify[Expand[#/.{q[0]->p[0], q[i:1|2|3]:>-p[i]}] /. p[3]^2->p[0]^2-p[1]^2-p[2]^2-Mass[p]^2 /. Mass[q]->Mass[p]]&
SpinorUBar[p,\[Xi]] . SpinorU[q,\[Zeta]] // FullSimplify[Expand[#/.{q[0]->p[0], q[i:1|2|3]:>-p[i]}] /. p[3]^2->p[0]^2-p[1]^2-p[2]^2-Mass[p]^2 /. Mass[q]->Mass[p]]&
SpinorVBar[p,\[Xi]] . SpinorV[q,\[Zeta]] // FullSimplify[Expand[#/.{q[0]->p[0], q[i:1|2|3]:>-p[i]}] /. p[3]^2->p[0]^2-p[1]^2-p[2]^2-Mass[p]^2 /. Mass[q]->Mass[p]]&


SpinorVBar2[p,\[Xi]] . SpinorV2[p,\[Zeta]] // FullSimplify[Expand[#] /. p[3]^2->p[0]^2-p[1]^2-p[2]^2-Mass[p]^2]&





LorSum[SigmaMatrix[#,None]r[#]&] . {{1},{0}}









(* ::Section:: *)
(*Eigenvector \[Xi] for Pauli-Lubanski operator*)


U = ArrayFlatten[{{SqrtSigmaDot[p],0},{0,SqrtSigmaBarDot[p]}}];
UInv = ArrayFlatten[{{SqrtSigmaBarDot[p],0},{0,SqrtSigmaDot[p]}}]/Mass[p];
\[CapitalXi] = {{\[Xi][1]},{\[Xi][2]},{\[Xi][1]},{\[Xi][2]}};
PRule[-1] := (Mass[p]^2->p[0]^2-Sum[p[j]^2,{j,3}]);
PRule[i:1|2|3] := (p[i]^2->p[0]^2-Mass[p]^2-Sum[If[i!=j,p[j]^2,0],{j,3}]);
ERule[i:1|2|3] := Sequence[
  e[i] p[i]->e[0]p[0] - Sum[If[i!=j,e[j]p[j],0],{j,3}],
  e[i]^2 -> e[0]^2 + 1 - Sum[If[i!=j,e[j]^2,0],{j,3}]
];
SpinorU[p,\[Xi]]==U . \[CapitalXi]//FullSimplify
Simplify[U . UInv]/.PRule[2]//Simplify
UInv == GammaFive . U . GammaFive (-1)/Mass[p]  + IdentityMatrix[4]*(Sqrt[2] Sqrt[Mass[p]+p[0]])/Mass[p]// Simplify


UInv . GammaFive . Slashed[e] . U//Simplify;
%/.{PRule[-1],ERule[1]}//Simplify;
%/.{PRule[2]}//Simplify;
%/.{ERule[3]}//Simplify;
matrix = %/.{PRule[3]}//Simplify;
eigen = Eigensystem[matrix]//.{ERule[1], PRule[3]}//Simplify[#,Mass[p]+p[0]>0]&


\[Phi][i_]:=(e[i] Mass[p]+e[i] p[0]-e[0] p[i])/(Mass[p]+p[0]);
evSimp = {{-1 F[1]+ 1 I F[2],F[3],0,1},{-F[3],-1 F[1]+ 1 I F[2] -2 I F[2],1,0},{-(-1 F[1]+ 1 I F[2]),-F[3],0,1},{F[3],F[1]+I F[2],1,0}};
(evSimp == eigen[[2]])//.F->\[Phi]//FullSimplify
evSimp//MatrixForm
{s1,s2,s3,s4}=evSimp;
Expand[Sum[\[Phi][i]^2,{i,3}]]//.{ERule[1],PRule[3]}//Simplify


\[Xi]A = ((1-F[3])s3+ (F[1]-I F[2]) s4)/(2 R) // FullSimplify;
\[Xi]B = -(((F[1]+I F[2]) s1+ (F[3]-1) s2)/(2 R)) // FullSimplify;
ExpandAll[{\[Xi]A[[1]]==\[Xi]A[[3]], \[Xi]A[[2]]==\[Xi]A[[4]], \[Xi]A[[1]]Conjugate[\[Xi]A[[1]]]+\[Xi]A[[2]]Conjugate[\[Xi]A[[2]]]}] //. Conjugate[a:F[1|2|3]]:>a;
FullSimplify[%,{F[1]^2+F[2]^2+F[3]^2==1}]

ExpandAll[{\[Xi]B[[1]]==\[Xi]B[[3]], \[Xi]B[[2]]==\[Xi]B[[4]], \[Xi]B[[1]]Conjugate[\[Xi]B[[1]]]+\[Xi]B[[2]]Conjugate[\[Xi]B[[2]]]}] //. Conjugate[a:F[1|2|3]]:>a;
FullSimplify[%,{F[1]^2+F[2]^2+F[3]^2==1}]

{matrix . \[Xi]A-\[Xi]A, matrix . \[Xi]B+\[Xi]B};
Expand[%] //. {PRule[1], ERule[1]}//FullSimplify[#,{F[1]^2+F[2]^2+F[3]^2==1}]& // Expand;
Expand[%/.F->\[Phi]]//.{ERule[1],PRule[3]}//Simplify


{\[Xi]A,\[Xi]B}//.{R->Sqrt[(1-F[3])/2],F->\[Phi],e[0]->pp/Mass[p],e[i:1|2|3]->p[0]p[i]/Mass[p]/pp}//Simplify//Expand//Simplify;
%//.{PRule[1],p[0]^2->pp^2+Mass[p]^2,p[i:1|2|3]->pp n[i]}//FullSimplify
%//.{n[1]->Sin[\[Theta]]Cos[\[Phi]],n[2]->Sin[\[Theta]]Sin[\[Phi]],n[3]->Cos[\[Theta]]}//FullSimplify[#,0<\[Theta]<Pi]&



