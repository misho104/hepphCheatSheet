(* ::Package:: *)

\[Eta][a:0|1|2|3, b:0|1|2|3] := Which[a!=b, 0, a==0, h\[Eta], True, -h\[Eta]]
\[Delta][a:0|1|2|3, b:0|1|2|3] := If[a==b,1,0]

\[Lambda]Mat = {{0,-\[Omega]x,-\[Omega]y,-\[Omega]z},{-\[Omega]x,0,\[Theta]z,-\[Theta]y},{-\[Omega]y,-\[Theta]z,0,+\[Theta]x},{-\[Omega]z,\[Theta]y,-\[Theta]x,0}};
\[Lambda][a:0|1|2|3,b:0|1|2|3] := \[Lambda]Mat[[a+1,b+1]]
dU[\[Mu]:0|1|2|3,\[Nu]:0|1|2|3] := (k) Sum[\[Lambda][\[Mu],a]\[Eta][\[Nu],a],{a,{0,1,2,3}}]
dL[\[Mu]:0|1|2|3,\[Nu]:0|1|2|3] := (k) Sum[\[Lambda][a,\[Nu]]\[Eta][\[Mu],a],{a,{0,1,2,3}}]

M[\[Rho]_,\[Sigma]_,\[Mu]_,\[Nu]_]:=(I/k)(\[Delta][\[Mu],\[Rho]]\[Eta][\[Nu],\[Sigma]]-\[Delta][\[Mu],\[Sigma]]\[Eta][\[Nu],\[Rho]])
MMat[\[Rho]:0|1|2|3,\[Sigma]:0|1|2|3]:=Table[M[\[Rho],\[Sigma],\[Mu],\[Nu]],{\[Mu],{0,1,2,3}},{\[Nu],{0,1,2,3}}]
asym[a_,b_]:=a.b-b.a;


(* Kugo-I \[Section]1-2, Eq.19 *)
{dL[2,3], dL[3,1], dL[1,2]}
{dL[1,0], dL[2,0], dL[3,0]}


(* Kugo-I \[Section]1-1, Eq.24 *)
Sum[(-I/2)dU[a,b]MMat[a,b],{a,{0,1,2,3}},{b,{0,1,2,3}}]/.h\[Eta]^2->1
%==\[Lambda]Mat//Simplify


(* Kugo-I \[Section]1-1, Eq.28 *)
LorAlgebra[\[Mu]_,\[Nu]_,\[Rho]_,\[Sigma]_] := -(I/k)(
  \[Eta][\[Mu],\[Rho]]MMat[\[Nu],\[Sigma]]-\[Eta][\[Nu],\[Rho]]MMat[\[Mu],\[Sigma]]-\[Eta][\[Mu],\[Sigma]]MMat[\[Nu],\[Rho]]+\[Eta][\[Nu],\[Sigma]]MMat[\[Mu],\[Rho]]
);
asym[MMat[\[Mu],\[Nu]],MMat[\[Rho],\[Sigma]]] == LorAlgebra[\[Mu],\[Nu],\[Rho],\[Sigma]];
Table[%,{\[Mu],{0,1,2,3}},{\[Nu],{0,1,2,3}},{\[Rho],{0,1,2,3}},{\[Sigma],{0,1,2,3}}]


Ki = -h\[Eta] Table[MMat[0,i],{i,3}];
\[Omega]i = {\[Omega]x, \[Omega]y, \[Omega]z};
Ji = h\[Eta]{MMat[2,3], MMat[3,1], MMat[1,2]};
\[Theta]i = {\[Theta]x, \[Theta]y, \[Theta]z};
I \[Omega]i.Ki + I \[Theta]i.Ji == \[Lambda]Mat /. {k->1,h\[Eta]^2->1}

Ai = (Ji + I Ki)/2;
Bi = (Ji - I Ki)/2;



Table[asym[Ji[[x]], Ji[[y]]] == I Sum[LeviCivitaTensor[3][[x,y,z]]Ji[[z]], {z,3}], {x,3},{y,3}]/.{k->1,h\[Eta]^(2|4)->1,h\[Eta]^3->h\[Eta]}//Simplify
Table[asym[Ji[[x]], Ki[[y]]] == I Sum[LeviCivitaTensor[3][[x,y,z]]Ki[[z]], {z,3}], {x,3},{y,3}]/.{k->1,h\[Eta]^(2|4)->1,h\[Eta]^3->h\[Eta]}//Simplify
Table[asym[Ki[[x]], Ki[[y]]] == -I Sum[LeviCivitaTensor[3][[x,y,z]]Ji[[z]], {z,3}], {x,3},{y,3}]/.{k->1,h\[Eta]^(2|4)->1,h\[Eta]^3->h\[Eta]}//Simplify

Table[asym[Ai[[x]], Ai[[y]]] == I Sum[LeviCivitaTensor[3][[x,y,z]]Ai[[z]], {z,3}], {x,3},{y,3}]/.{k->1,h\[Eta]^(2|4)->1,h\[Eta]^3->h\[Eta]}//Simplify
Table[asym[Bi[[x]], Bi[[y]]] == I Sum[LeviCivitaTensor[3][[x,y,z]]Bi[[z]], {z,3}], {x,3},{y,3}]/.{k->1,h\[Eta]^(2|4)->1,h\[Eta]^3->h\[Eta]}//Simplify
Table[asym[Ai[[x]], Bi[[y]]] == DiagonalMatrix[{0,0,0,0}], {x,3},{y,3}]/.{k->1,h\[Eta]^(2|4)->1,h\[Eta]^3->h\[Eta]}//Simplify






(* derivation of t_\mu\nu *)
Unprotect[Dot]
EQSeq[r_,s_,a_]:=asym[S[r,s],\[Gamma][a]] == Sum[-M[r,s,a,b]\[Gamma][b],{b,0,3}]
S[r_,s_]:=sym (\[Gamma]D[r].\[Gamma]D[s]+\[Gamma]D[s].\[Gamma]D[r])+asym(\[Gamma]D[r].\[Gamma]D[s]-\[Gamma]D[s].\[Gamma]D[r])
Dot[a___,\[Gamma][i:0|1|2|3],\[Gamma][j:0|1|2|3],b___]/;i>j:=-Dot[a,\[Gamma][j],\[Gamma][i],b]
Dot[a___,p:asym|sym|h\[Eta],b___]:=p Dot[a,b]
Dot[a___,p_,b__]/;NumericQ[p]:=p Dot[a,b]
Dot[a__,p_,b___]/;NumericQ[p]:=p Dot[a,b]
Dot[a___,Times[b_,d__],c___]:=Dot[a,b,d,c]
Dot[a___,\[Gamma][0],\[Gamma][0],b___]:=h\[Eta] Dot[a,b]
Dot[a___,\[Gamma][i:1|2|3],\[Gamma][i_],b___]:=-h\[Eta] Dot[a,b]
\[Gamma]D[0]:=h\[Eta] \[Gamma][0]
\[Gamma]D[i:1|2|3]:=-h\[Eta] \[Gamma][i]
h\[Eta]^n_/;n>1 ^:= h\[Eta]^Mod[n,2]


Table[EQSeq[a,b,c],{a,0,3},{b,0,3},{c,0,3}]/.{
  k->1,Dot[]->1,asym->I/4
}

Seqn[\[Mu]_,\[Nu]_,\[Rho]_,\[Sigma]_]:= asym[S[\[Mu],\[Nu]],S[\[Rho],\[Sigma]]] == -I(  \[Eta][\[Mu],\[Rho]]S[\[Nu],\[Sigma]]-\[Eta][\[Nu],\[Rho]]S[\[Mu],\[Sigma]]-\[Eta][\[Mu],\[Sigma]]S[\[Nu],\[Rho]]+\[Eta][\[Nu],\[Sigma]]S[\[Mu],\[Rho]])
Table[Seqn[a,b,c,d],{a,0,3},{b,0,3},{c,0,3},{d,0,3}]/.asym->I/4/.sym->0
