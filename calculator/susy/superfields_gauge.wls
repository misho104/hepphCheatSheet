#!/usr/bin/env wolframscript
(* ::Package:: *)

(* ::Subsection:: *)
(*Common tools*)


SetDirectory[NotebookDirectory[]];
<<WeylAlgebra`
<<WeylAlgebraDerivedRules`
 
SumToList[exp_]  := Module[{tmp = Expand[exp]}, If[Head[tmp] === Plus, List@@tmp, {tmp}]];

RewriteIndicesOrdering[a_] := a /. {
  NT[p:"\[Sigma]"|OverBar["\[Sigma]"],q__]:>{0,p,q},
  GT[p:"\[Theta]"|OverBar["\[Theta]"],q__]:>{3,p,q},
  _[Field[p_,_],___] :> {2,p},
  _[OverBar[Field[p_,_]],___] :> {1,p}
}
RewriteIndices[exp_, format_, indices_:Null] :=
  Module[{rep, old, nottoreplace, toreplace, new, rule},
    rep = exp //. TDot[a__]:>TDotList@@SortBy[{a}, RewriteIndicesOrdering];
    old = Cases[rep,  format :> index, All];
    nottoreplace = Counts[old] /. Association -> List // Cases[#, (p_ -> 1) :> p] &;
    toreplace = Counts[old] /. Association -> List // Cases[#, (p_ -> 2) :> p] &;
    new = If[indices===Null, If[Head[#]===OverDot, OverDot[Unique[]], Unique[]]& /@ toreplace, Select[indices, FreeQ[nottoreplace, #] &]];
    If[Length[toreplace] > Length[new], Return[exp]];
    rule = (#[[1]] -> #[[2]]) & /@ Transpose[{toreplace, new[[1 ;; Length[toreplace]]]}];
    exp /. rule];

RewriteIndices[exp_] := Module[{result},
  result = SumToList[exp];
  result = RewriteIndices[#, (UI|LI)[index_, "lorentz"], {"\[Mu]", "\[Nu]", "\[Rho]", "\[CapitalSigma]", "\[Alpha]", "\[Beta]", "\[Gamma]"}] & /@ result;
  result = RewriteIndices[#, ((UI|LI)[index_, "spinor"] /; FreeQ[index, OverDot]), {"a", "b", "c", "d", "e", "f", "g", "h", "k"}] & /@ result;
  result = RewriteIndices[#, ((UI|LI)[index_OverDot, "spinor"]), OverDot/@{"a", "b", "c", "d", "e", "f", "g", "h", "k"}] & /@ result;
  result = RewriteIndices[#, NI[index_, "SUNI"], {"i", "j", "k", "l", "m", "n"}] & /@ result;
  result = RewriteIndices[#, NI[index_, "SUNF"], {"s", "t", "u", "v", "w"}] & /@ result;
  Total[result]
];

RenewIndices[exp_] := Module[{result},
  result = SumToList[exp];
  result = RewriteIndices[#, (UI|LI)[index_, "lorentz"]] & /@ result;
  result = RewriteIndices[#, ((UI|LI)[index_, "spinor"] /; FreeQ[index, OverDot])] & /@ result;
  result = RewriteIndices[#, ((UI|LI)[index_OverDot, "spinor"])] & /@ result;
  result = RewriteIndices[#, NI[index_, "SUNI"]] & /@ result;
  result = RewriteIndices[#, NI[index_, "SUNF"]] & /@ result;
  Total[result]
];

SymmetrizeIndices[exp_, {a_, b_}] := (exp + (exp /. {a->b, b->a}))/2

SortTDot[exp_] := exp /. TDot -> TD //. {
  TD[x1___,
    GT[a1_, a2___, UI[a3:WeylAlgebra`Private`SpinorLabelType, "spinor"]],
    NT["\[Sigma]", s:(UI|LI)[_, "lorentz"], LI[a3_, "spinor"], LI[b3:OverDot[WeylAlgebra`Private`SpinorLabelType], "spinor"]],
    GT[b1_, b2___, UI[b3_OverDot, "spinor"]], x2___] /; FreeQ[{a2, b2}, "spinor"] :> (-1)TD[x1, GT[b1, b2, LI[b3, "spinor"]], NT[OverBar["\[Sigma]"], s, UI[b3, "spinor"], UI[a3,"spinor"]], GT[a1, a2, LI[a3, "spinor"]], x2],
  TD[x1___, GT[a:Except[_OverBar], ai:UI[i_, "spinor"]], GT[b:Except[_OverBar], bi:LI[i_, "spinor"]], x2___] /; Not[OrderedQ[{a,b}]] :> TD[x1, GT[b, ai], GT[a, bi], x2],
  TD[x1___, GT[a_OverBar, ai:LI[i_, "spinor"]], GT[b_OverBar, bi:UI[i_, "spinor"]], x2___] /; Not[OrderedQ[{a,b}]] :> TD[x1, GT[b, ai], GT[a, bi], x2]
} //. {
  TD[x1___, a_, b_, x2___] /; Not[OrderedQ[{a,b}]] :> TD[x1, b, a, x2]FlipSign[a,b]
} //. TD->TDot

LorentzSort[exp_] := (exp//.{
  (p:NT|GT)[x1__, LI[\[Mu]_,"lorentz"], x2___]/; FreeQ[{x1}, "\[Eta]"] :> Module[{\[Nu]=Unique[]}, \[Eta]L[\[Mu], \[Nu]] p[x1, UI[\[Nu],"lorentz"], x2]]
}//SortTDot//RewriteIndices)//.NT[HoldForm["\[Eta]"], a_, b_] /; Not[OrderedQ[{a,b}]] :> NT[HoldForm["\[Eta]"], b, a]//ReleaseHoldAll;


ToTeX = {};
Express::usage = "";
Attributes[Express] = {HoldFirst};
Express[exphold_, apply_:(#&), hold_:True] := If[hold=!=True, Express[exphold//Evaluate, apply, True], Module[{exp},
  exp = ReleaseHoldAll[exphold] // RewriteIndices // OrderTheta[#,apply]&;
  AppendTo[ToTeX, HoldForm[exphold] == exp];
  exp]]


(* ::Subsection:: *)
(*Definitions*)


MakeBoxesNT$deriv[f_, c_, Field[Dx[n_], x_], UI[\[Mu]_, "lorentz"], any___] := Row[{Superscript["\[PartialD]", \[Mu]], MakeBoxesNT$deriv[f, c, Field[n, x], any]}]
MakeBoxesNT$deriv[f_, c_, Field[Dx[n_], x_], LI[\[Mu]_, "lorentz"], any___] := Row[{Subscript["\[PartialD]", \[Mu]], MakeBoxesNT$deriv[f, c, Field[n, x], any]}]
MakeBoxesNT$deriv[f_, c_, OverBar[Field[Dx[n_], x_]], UI[\[Mu]_, "lorentz"], any___] := Row[{Superscript["\[PartialD]", \[Mu]], MakeBoxesNT$deriv[f, c, OverBar[Field[n, x]], any]}]
MakeBoxesNT$deriv[f_, c_, OverBar[Field[Dx[n_], x_]], LI[\[Mu]_, "lorentz"], any___] := Row[{Subscript["\[PartialD]", \[Mu]], MakeBoxesNT$deriv[f, c, OverBar[Field[n, x]], any]}]
MakeBoxesNT$deriv[f_, c_, Field[Conj[n_[i_]], x_], any___] := MakeBoxesNT$deriv[f, c, Field[Subsuperscript[n,i,"*"], x], any]
MakeBoxesNT$deriv[f_, c_, Field[Conj[n_], x_], any___] := MakeBoxesNT$deriv[f, c, Field[Superscript[n,"*"], x], any]
MakeBoxesNT$deriv[f_, c_, Field[n_[i_], x_], any___] := MakeBoxesNT$deriv[f, c, Row[{Subscript[n,i],"(",x,")"}], any]
MakeBoxesNT$deriv[f_, c_, Field[n_, x_], any___] := MakeBoxesNT$deriv[f, c, Row[{n,"(",x,")"}], any]
MakeBoxesNT$deriv[f_, c_, OverBar[Field[n_[i_], x_]], any___] := MakeBoxesNT$deriv[f, c, Row[{OverBar[Subscript[n,i]],"(",x,")"}], any]
MakeBoxesNT$deriv[f_, c_, OverBar[Field[n_, x_]], any___] := MakeBoxesNT$deriv[f, c, Row[{OverBar[n],"(",x,")"}], any]

MakeBoxesNT$deriv[f_, c_, Field[Dx2[n_], x_], any___] := Row[{Superscript["\[PartialD]", 2], MakeBoxesNT$deriv[f, c, Field[n, x], any]}]
MakeBoxesNT$deriv[exp___] := WeylAlgebra`Private`MakeBoxesNT$[exp]
WeylAlgebra`MakeBoxesNT = MakeBoxesNT$deriv;

Deriv /: MakeBoxes[obj: Deriv["x"[UI[i_,"lorentz"]], exp_], f:StandardForm|TraditionalForm] := Row[{Superscript["\[PartialD]", i], exp}] // ToBoxes // InterpretationBox[#,obj] &
Deriv /: MakeBoxes[obj: Deriv["x"[LI[i_,"lorentz"]], exp_], f:StandardForm|TraditionalForm] := Row[{Subscript["\[PartialD]", i], exp}] // ToBoxes // InterpretationBox[#,obj] &
Deriv /: MakeBoxes[obj: Deriv["\[Theta]"[UI[i_,"spinor"]],  exp_], f:StandardForm|TraditionalForm] := Row[{"\[PartialD]"/Row[{"\[PartialD]", Subscript["\[Theta]", i]}], exp}] // ToBoxes // InterpretationBox[#,obj] &
Deriv /: MakeBoxes[obj: Deriv["\[Theta]"[LI[i_,"spinor"]],  exp_], f:StandardForm|TraditionalForm] := Row[{"\[PartialD]"/Row[{"\[PartialD]", Superscript["\[Theta]", i]}], exp}] // ToBoxes // InterpretationBox[#,obj] &
Deriv /: MakeBoxes[obj: Deriv["\[Theta]b"[UI[i_,"spinor"]], exp_], f:StandardForm|TraditionalForm] := Row[{"\[PartialD]"/Row[{"\[PartialD]", Subscript[OverBar["\[Theta]"], i]}], exp}] // ToBoxes // InterpretationBox[#,obj] &
Deriv /: MakeBoxes[obj: Deriv["\[Theta]b"[LI[i_,"spinor"]], exp_], f:StandardForm|TraditionalForm] := Row[{"\[PartialD]"/Row[{"\[PartialD]", Superscript[OverBar["\[Theta]"], i]}], exp}] // ToBoxes // InterpretationBox[#,obj] &
DT /: MakeBoxes[obj: DT[n_], f:StandardForm|TraditionalForm] := MakeBoxes[Deriv[n,"["]]// InterpretationBox[#,obj] &


\[Theta][a_]  := GT["\[Theta]", UI[a, "spinor"]]
\[Theta][,a_] := GT["\[Theta]", LI[a, "spinor"]]
\[Xi][a_]  := GT["\[Xi]", UI[a, "spinor"]]
\[Xi][,a_] := GT["\[Xi]", LI[a, "spinor"]]
\[Theta]b[a_]  := GT[OverBar["\[Theta]"], UI[PutOverDot[a], "spinor"]]
\[Theta]b[,a_] := GT[OverBar["\[Theta]"], LI[PutOverDot[a], "spinor"]]
\[Xi]b[a_]  := GT[OverBar["\[Xi]"], UI[PutOverDot[a], "spinor"]]
\[Xi]b[,a_] := GT[OverBar["\[Xi]"], LI[PutOverDot[a], "spinor"]]
\[Theta]\[Theta] := Module[{i=Unique[]}, TDot[\[Theta][i], \[Theta][,i]]];
\[Theta]\[Theta]b := Module[{i=Unique[]}, TDot[\[Theta]b[,i], \[Theta]b[i]]];

\[CapitalOmega]1\[Theta]\[Theta]    /: MakeBoxes[obj: \[CapitalOmega]1\[Theta]\[Theta][],     f:StandardForm|TraditionalForm] := Superscript["\[Theta]", 2] // ToBoxes // InterpretationBox[#,obj] &
\[CapitalOmega]2\[Theta]\[Theta]b   /: MakeBoxes[obj: \[CapitalOmega]2\[Theta]\[Theta]b[],    f:StandardForm|TraditionalForm] := Superscript[OverBar["\[Theta]"], 2] // ToBoxes // InterpretationBox[#,obj] &
\[CapitalOmega]3\[Theta]\[Sigma]\[Theta]b  /: MakeBoxes[obj: \[CapitalOmega]3\[Theta]\[Sigma]\[Theta]b[\[Mu]_], f:StandardForm|TraditionalForm] := Row[{"(","\[Theta]", Superscript["\[Sigma]", \[Mu]], OverBar["\[Theta]"], ")"}]// ToBoxes // InterpretationBox[#,obj] &
\[CapitalOmega]4\[Theta]4    /: MakeBoxes[obj: \[CapitalOmega]4\[Theta]4[],     f:StandardForm|TraditionalForm] := Superscript["\[Theta]", 4] // ToBoxes // InterpretationBox[#,obj] &
OrderedPlus /: MakeBoxes[obj: OrderedPlus[a__], f:TraditionalForm] := Row[Riffle[{a}, Row[{"{","+","}"}]]] // ToBoxes // InterpretationBox[#,obj] &


ReduceTheta[exp_] := exp //. {
  TDot[x1___, GT["\[Theta]", UI[n_, "spinor"]], GT["\[Theta]", LI[n_, "spinor"]], x2___] :> \[CapitalOmega]1\[Theta]\[Theta][]*TDot[x1,x2],
  TDot[x1___, GT[OverBar["\[Theta]"], LI[n_, "spinor"]], GT[OverBar["\[Theta]"], UI[n_, "spinor"]], x2___] :> \[CapitalOmega]2\[Theta]\[Theta]b[]*TDot[x1,x2],
  \[CapitalOmega]1\[Theta]\[Theta][]*\[CapitalOmega]2\[Theta]\[Theta]b[] :> \[CapitalOmega]4\[Theta]4[],
  TDot[x1___, GT["\[Theta]", UI[n_, "spinor"]], NT["\[Sigma]", UI[\[Mu]_, "lorentz"], LI[n_, "spinor"], LI[m_, "spinor"]], GT[OverBar["\[Theta]"], UI[m_, "spinor"]], x2___] :> \[CapitalOmega]3\[Theta]\[Sigma]\[Theta]b[\[Mu]]*TDot[x1, x2]
};
CountTheta[exp_]    := Total@Flatten[{Cases[exp, GT["\[Theta]", ___]:>1, All],          Cases[exp, (\[CapitalOmega]3\[Theta]\[Sigma]\[Theta]b[_]):>1, All], Cases[exp, (\[CapitalOmega]4\[Theta]4[]|\[CapitalOmega]1\[Theta]\[Theta][]):>2, All]}]
CountThetaBar[exp_] := Total@Flatten[{Cases[exp, GT[OverBar["\[Theta]"], ___]:>1, All], Cases[exp, (\[CapitalOmega]3\[Theta]\[Sigma]\[Theta]b[_]):>1, All], Cases[exp, (\[CapitalOmega]4\[Theta]4[]|\[CapitalOmega]2\[Theta]\[Theta]b[]):>2, All]}]
CollectTheta[exp_, apply_:(#&)] := OrderTheta[exp, apply] /. OrderedPlus->Plus
OrderTheta[exp_, apply_:(#&)] := Module[{tmp = ExpandAll[ReleaseHoldAll[exp]]},
  If[Head[tmp] =!= Plus, Return[ReduceTheta[tmp]]];
  tmp = List@@tmp;
  tmp = GroupBy[tmp, {CountTheta[#]+CountThetaBar[#], CountThetaBar[#]}&]; (* terms in association *)
  tmp = (Sort[tmp/.Association->List])[[All, 2]];
  tmp = OrderedPlus@@(Simplify[Total/@ReduceTheta[tmp]]//apply)]
ThetaCoeff[exp_, theta:0|1|2, thetabar:0|1|2] := Module[{tmp = ExpandAll[ReleaseHoldAll[exp]]},
  If[Head[tmp] =!= Plus, Abort[]];
  tmp = List@@tmp;
  tmp = GroupBy[tmp, {CountTheta[#]+CountThetaBar[#], CountThetaBar[#]}&]; (* terms in association *)
  Lookup[tmp, {{theta+thetabar, thetabar}}, {0}]//Flatten//Total]

\[Phi] [i_,x_]      := NT[Field["\[Phi]"[i],x]]
F [i_,x_]      := NT[Field["F"[i],x]]
\[Psi] [i_,x_,a_]   := GT[Field["\[Psi]"[i],x], UI[a, "spinor"]]
\[Psi] [i_,x_, ,a_] := GT[Field["\[Psi]"[i],x], LI[a, "spinor"]]
\[Psi]b[i_,x_,a_]   := GT[OverBar[Field["\[Psi]"[i],x]], UI[OverDot[a], "spinor"]]
\[Psi]b[i_,x_, ,a_] := GT[OverBar[Field["\[Psi]"[i],x]], LI[OverDot[a], "spinor"]]

dd[s_,x_]      := NT[Field["DD",x], NI[s, "SUNF"]]
\[Lambda] [s_,x_,a_]   := GT[Field["\[Lambda]",x], UI[a, "spinor"], NI[s, "SUNF"]]
\[Lambda] [s_,x_, ,a_] := GT[Field["\[Lambda]",x], LI[a, "spinor"], NI[s, "SUNF"]]
\[Lambda]b[s_,x_,a_]   := GT[OverBar[Field["\[Lambda]",x]], UI[OverDot[a], "spinor"], NI[s, "SUNF"]]
\[Lambda]b[s_,x_, ,a_] := GT[OverBar[Field["\[Lambda]",x]], LI[OverDot[a], "spinor"], NI[s, "SUNF"]]
A [s_,x_,\[Mu]_]   := NT[Field["A",x], UI[\[Mu], "lorentz"], NI[s, "SUNF"]]
A [s_,x_,,\[Mu]_]  := NT[Field["A",x], LI[\[Mu], "lorentz"], NI[s, "SUNF"]]
FF[s_,x_,\[Mu]_,\[Nu]_] := Module[{t=Unique[], u=Unique[]}, Dx[\[Mu], A[s, x, \[Nu]]] - Dx[\[Nu], A[s, x, \[Mu]]] + g NT["f", NI[s, "SUNF"], NI[t, "SUNF"], NI[u, "SUNF"]]A[t,x,\[Mu]]A[u,x,\[Nu]]]
FF[s_,x_,,\[Mu]_,\[Nu]_] := Module[{t=Unique[], u=Unique[]}, Dx[,\[Mu], A[s, x, ,\[Nu]]] - Dx[,\[Nu], A[s, x, ,\[Mu]]] + g NT["f", NI[s, "SUNF"], NI[t, "SUNF"], NI[u, "SUNF"]]A[t,x,,\[Mu]]A[u,x,,\[Nu]]]
FF0[i_,j_,x_,\[Mu]_,\[Nu]_] := Module[{s=Unique[], t=Unique[], k=Unique[]}, Dx[\[Mu], A[s,x,\[Nu]]]T[s,i,j] - Dx[\[Nu], A[s,x,\[Mu]]]T[s,i,j] - I g (A[s,x,\[Mu]]T[s,i,k]A[t,x,\[Nu]]T[t,k,j]-A[t,x,\[Nu]]T[t,i,k]A[s,x,\[Mu]]T[s,k,j])]
FF0[i_,j_,x_,,\[Mu]_,\[Nu]_] := Module[{s=Unique[], t=Unique[], k=Unique[]}, Dx[,\[Mu], A[s,x,,\[Nu]]]T[s,i,j] - Dx[,\[Nu], A[s,x,,\[Mu]]]T[s,i,j] - I g (A[s,x,,\[Mu]]T[s,i,k]A[t,x,,\[Nu]]T[t,k,j]-A[t,x,,\[Nu]]T[t,i,k]A[s,x,,\[Mu]]T[s,k,j])]
T [i_,s_,t_] := NT["T", NI[i, "SUNF"], NI[s,"SUNI"], NI[t,"SUNI"]]

NT["TS", a_, b_, i_, j_]/;Not[OrderedQ[{a,b}]]:=NT["TS", b,a,i,j]
NT["f", x1___, a_, b_, x2___]/;Not[OrderedQ[{a,b}]]:=(-1)NT["f",x1,b,a,x2]


(* for spinors: (unused rule)
Conjugate[GT[a:NameType, b:RepeatedNull[IndexType]]] := SwitchOverDot[GT[OverBar[a], b]]
 -> OverBar[Field[\[Psi][i], x]] etc...
*)

NT /: Conjugate[NT[Field[f_,x_], any___]] := NT[Field[Conj[f], x], any] // SwitchOverDot
Conj[Conj[f_]] := f
Conj[(f:"C"|"M1"|"M2"|"A"|"DD")[i_]] := f[i]

(* Derivatives *)

IsGrassmann[x_] := Switch[Head[x], "x", False, "xD", False, "\[Theta]", True, "\[Theta]b", True, _, Print[x];Abort[]]
Dx [index_,  any_] := Deriv["x"[UI[index, "lorentz"]], any]             (* Dx[\[Mu]]   = \[PartialD]^\[Mu];              \!\(\(Dx[\(,\)\(\[Mu]\)]\)\ \ \  = \ 
\*SubscriptBox[\(\[PartialD]\), \(\[Mu]\)]\) *)
Dx [,index_, any_] := Deriv["x"[LI[index, "lorentz"]], any]             (* Dx[\[Mu]]   = \[PartialD]^\[Mu];              \!\(\(Dx[\(,\)\(\[Mu]\)]\)\ \ \  = \ 
\*SubscriptBox[\(\[PartialD]\), \(\[Mu]\)]\) *)
DxD[index_,  any_] := Deriv["xD"[UI[index, "lorentz"]], any]            (* DxD[\[Mu]]  = D^\[Mu];              \!\(\(Dx[\(,\)\(\[Mu]\)]\)\ \ \  = \ 
\*SubscriptBox[\(\[PartialD]\), \(\[Mu]\)]\) *)
DxD[,index_, any_] := Deriv["xD"[LI[index, "lorentz"]], any]            (* DxD[\[Mu]]  = D^\[Mu];              \!\(\(Dx[\(,\)\(\[Mu]\)]\)\ \ \  = \ 
\*SubscriptBox[\(\[PartialD]\), \(\[Mu]\)]\) *)
D\[Theta] [index_,  any_] := Deriv["\[Theta]"[UI[index, "spinor"]],  any]             (* D\[Theta][\[Alpha]]   = \[PartialD]^\[Alpha] = d/d(\[Theta]_\[Alpha]),   D\[Theta][,\[Alpha]]   = \!\(
\*SubscriptBox[\(\[PartialD]\), \(\[Alpha]\)]\ \(\(=\)\(\ \)\(d/d\((
\*SuperscriptBox[\(\[Theta]\), \(\[Alpha]\)])\)\)\)\); all derivatives from left. *) 
D\[Theta] [,index_, any_] := Deriv["\[Theta]"[LI[index, "spinor"]],  any]             (* D\[Theta][\[Alpha]]   = \[PartialD]^\[Alpha] = d/d(\[Theta]_\[Alpha]),   D\[Theta][,\[Alpha]]   = \!\(
\*SubscriptBox[\(\[PartialD]\), \(\[Alpha]\)]\ \(\(=\)\(\ \)\(d/d\((
\*SuperscriptBox[\(\[Theta]\), \(\[Alpha]\)])\)\)\)\); all derivatives from left. *) 
D\[Theta]b[index_,  any_] := Deriv["\[Theta]b"[UI[PutOverDot[index], "spinor"]], any] (* D\[Theta]b[\[Alpha].] = \[PartialD]^\[Alpha]. = d/d(\[Theta]_\[Alpha].), D\[Theta]b[,\[Alpha].] = \!\(
\*SubscriptBox[\(\[PartialD]\), 
OverscriptBox[\(\[Alpha]\), \(.\)]]\ \(\(=\)\(\ \)\(d/d\((
\*SuperscriptBox[
OverscriptBox[\(\[Theta]\), \(_\)], 
OverscriptBox[\(\[Alpha]\), \(.\)]])\)\)\)\); all derivatives from left. *)
D\[Theta]b[,index_, any_] := Deriv["\[Theta]b"[LI[PutOverDot[index], "spinor"]], any] (* D\[Theta]b[\[Alpha].] = \[PartialD]^\[Alpha]. = d/d(\[Theta]_\[Alpha].), D\[Theta]b[,\[Alpha].] = \!\(
\*SubscriptBox[\(\[PartialD]\), 
OverscriptBox[\(\[Alpha]\), \(.\)]]\ \(\(=\)\(\ \)\(d/d\((
\*SuperscriptBox[
OverscriptBox[\(\[Theta]\), \(_\)], 
OverscriptBox[\(\[Alpha]\), \(.\)]])\)\)\)\); all derivatives from left. *)

DD [, a_, exp_] := Module[{db=PutOverDot[Unique[]], \[Mu]=Unique[]},      +D\[Theta] [, a, exp] - I TDot[\[Sigma][\[Mu], a, db], \[Theta]b[db], Dx[,\[Mu], exp]]]
DDb[, a_, exp_] := Module[{da=PutOverDot[a], b=Unique[], \[Mu]=Unique[]}, -D\[Theta]b[,da, exp] + I TDot[\[Theta][b], \[Sigma][\[Mu], b, da], Dx[,\[Mu], exp]]]
DD [a_,   exp_] := Module[{db=PutOverDot[Unique[]], \[Mu]=Unique[]},      -D\[Theta] [a,   exp] + I TDot[\[Theta]b[,db], \[Sigma]b[\[Mu], db, a], Dx[,\[Mu], exp]]]
DDb[a_,   exp_] := Module[{da=PutOverDot[a], b=Unique[], \[Mu]=Unique[]}, +D\[Theta]b[da,  exp] - I TDot[\[Sigma]b[\[Mu], da, b], \[Theta][,b], Dx[,\[Mu], exp]]]
QQ [, a_, exp_] := Module[{db=PutOverDot[Unique[]], \[Mu]=Unique[]},      +D\[Theta] [, a, exp] + I TDot[\[Sigma][\[Mu], a, db], \[Theta]b[db], Dx[,\[Mu], exp]]]
QQ [a_,   exp_] := Module[{db=PutOverDot[Unique[]], \[Mu]=Unique[]},      -D\[Theta] [a,   exp] - I TDot[\[Theta]b[,db], \[Sigma]b[\[Mu], db, a], Dx[,\[Mu], exp]]]
QQb[, a_, exp_] := Module[{da=PutOverDot[a], b=Unique[], \[Mu]=Unique[]}, -D\[Theta]b[,da, exp] - I TDot[\[Theta][b], \[Sigma][\[Mu], b, da], Dx[,\[Mu], exp]]]
QQb[a_,   exp_] := Module[{da=PutOverDot[a], b=Unique[], \[Mu]=Unique[]}, +D\[Theta]b[da,  exp] + I TDot[\[Sigma]b[\[Mu], da, b], \[Theta][,b], Dx[,\[Mu], exp]]]

Deriv[var_, TDot[exp__]] := TDot[DT[var], exp]
Deriv[var_, t:(_NT|_GT)] := TDot[DT[var], t]
Deriv[var_, Plus[a_, b__]] := Deriv[var, a] + Deriv[var, Plus[b]]
Deriv[var_, Times[a:(_String|_?NumericQ), b__]] := a Deriv[var, Times[b]]
Deriv[var_, (_String|_?NumericQ)] := 0

TDot[x1___, d:DT[var_], a:_NT, x2___] := TDot[x1, TakeDerivative[var, a], x2] + TDot[x1, a, d, x2]
TDot[x1___, d:DT[var_], a:_GT, x2___] := TDot[x1, TakeDerivative[var, a], x2] + If[IsGrassmann[var], -1, 1] * TDot[x1, a, d, x2]
TDot[x1___, DT[var_]] := 0

TakeDerivative["x"[UI[\[Mu]_, "lorentz"]], (t:NT|GT)[f:Field[__]|OverBar[Field[__]], any___]] := t[Dx[f], UI[\[Mu], "lorentz"], any]
TakeDerivative["x"[LI[\[Mu]_, "lorentz"]], (t:NT|GT)[f:Field[__]|OverBar[Field[__]], any___]] := t[Dx[f], LI[\[Mu], "lorentz"], any]
TakeDerivative["x"[_UI|_LI], (NT|GT)[f:Except[Field[__]|OverBar[Field[__]]], ___]] := 0
Dx[Field[n_, x_]] := Field[Dx[n], x]
Dx[OverBar[Field[n_, x_]]] := OverBar[Field[Dx[n], x]]
NT[Field[Dx[Dx[n_]], x_], OrderlessPatternSequence[UI[a_, "lorentz"], LI[a_, "lorentz"]], any___] := NT[Field[Dx2[n], x], any]
GT[Field[Dx[Dx[n_]], x_], OrderlessPatternSequence[UI[a_, "lorentz"], LI[a_, "lorentz"]], any___] := GT[Field[Dx2[n], x], any]

NT[f:Field[Dx[Dx[_]], _], a:(UI|LI)[i_, "lorentz"], b:(UI|LI)[j_, "lorentz"], any___] /; Not[OrderedQ[{i, j}]] := NT[f, b, a, any]
GT[f:Field[Dx[Dx[_]], _], a:(UI|LI)[i_, "lorentz"], b:(UI|LI)[j_, "lorentz"], any___] /; Not[OrderedQ[{i, j}]] := GT[f, b, a, any]

TakeDerivative["\[Theta]"[UI[a_, "spinor"]], GT["\[Theta]", LI[b_, "spinor"]]] := \[Delta][a, b, "spinor"]
TakeDerivative["\[Theta]"[UI[a_, "spinor"]], GT["\[Theta]", UI[b_, "spinor"]]] := \[Epsilon]U[b, a] (* d/\[Theta]_a * \[Theta]^b = d/\[Theta]_a * \[Epsilon]^bc \[Theta]_c = \[Epsilon]^ba *)
TakeDerivative["\[Theta]"[LI[a_, "spinor"]], GT["\[Theta]", UI[b_, "spinor"]]] := \[Delta][b, a, "spinor"]
TakeDerivative["\[Theta]"[LI[a_, "spinor"]], GT["\[Theta]", LI[b_, "spinor"]]] := \[Epsilon]L[b, a]

TakeDerivative["\[Theta]b"[UI[a_, "spinor"]], GT[OverBar["\[Theta]"], LI[OverDot[b_], "spinor"]]] := \[Delta]d[a, b, "spinor"]
TakeDerivative["\[Theta]b"[UI[a_, "spinor"]], GT[OverBar["\[Theta]"], UI[b_, "spinor"]]] := \[Epsilon]U[b, a]
TakeDerivative["\[Theta]b"[LI[a_, "spinor"]], GT[OverBar["\[Theta]"], UI[b_, "spinor"]]] := \[Delta]d[b, a, "spinor"]
TakeDerivative["\[Theta]b"[LI[a_, "spinor"]], GT[OverBar["\[Theta]"], LI[b_, "spinor"]]] := \[Epsilon]L[b, a]
TakeDerivative["\[Theta]"[_UI|_LI],   NT[___]] := 0
TakeDerivative["\[Theta]b"[_UI|_LI],  NT[___]] := 0
TakeDerivative["\[Theta]"[_UI|_LI],   GT[Except["\[Theta]"], ___]] := 0
TakeDerivative["\[Theta]b"[_UI|_LI],  GT[Except[OverBar["\[Theta]"]], ___]] := 0

TakeDerivative["xD"[p:(UI|LI)[\[Mu]_, "lorentz"]], w:(n:GT|NT)[f:(OverBar[Field["\[Lambda]", x_]]|Field["\[Lambda]"|"DD", x_]), x1___, NI[s_, "SUNF"], x2___]] := Module[{t=Unique[], u=Unique[]},
  TakeDerivative["x"[p], w] +  g NT["f", NI[s, "SUNF"],NI[t, "SUNF"],NI[u, "SUNF"]] NT[Field["A",x],p,NI[t,"SUNF"]]n[f,x1, NI[u,"SUNF"], x2]]
TakeDerivative["xD"[_UI|_LI], (NT|GT)[f:Except[Field[__]|OverBar[Field[__]]], ___]] := 0
TakeDerivative["xD"[p_], GT[Field[Dx2["\[Lambda]"],x_],any___]] := Module[{\[Mu]=Unique[]}, Deriv["xD"[p], GT[Field["\[Lambda]", x], any]] // Dx[,\[Mu],#]& // Dx[\[Mu],#]&]
TakeDerivative["xD"[p_], GT[Field[Dx["\[Lambda]"],x_],a:(UI|LI)[_,"lorentz"],any___]] := Deriv["xD"[p], GT[Field["\[Lambda]", x], any]] // Deriv["x"[a], #]&
  
(* Derivative + conjugate *)
Conj[Dx[f_]] := Dx[Conj[f]]
Conj[Dx2[f_]] := Dx2[Conj[f]]

(* for debug
T[x,a,b]T[y,b,c]+T[y,a,b]T[x,b,c]//SymmetrizeT//RewriteIndices//ExpandAll
T[x,a,b]T[y,b,c]-T[y,a,b]T[x,b,c]//SymmetrizeT//RewriteIndices//ExpandAll
\[Sigma]b[\[Mu],a,b]\[Sigma][\[Nu],b,c]- (\[Sigma]b[\[Mu],a,b]\[Sigma][\[Nu],b,c]//ReleaseHoldAll//Sym\[Sigma]//ReleaseHoldAll//ExpandAll)
%//ReleaseHoldAll // FillIndices[#,"spinor"]& // Table[#,{a,2},{c,2},{\[Mu],0,3},{\[Nu],0,3}]&
\[Sigma]b[\[Mu],c,a]\[Sigma][\[Nu],b,c]- (\[Sigma]b[\[Mu],c,a]\[Sigma][\[Nu],b,c]//ReleaseHoldAll//Sym\[Sigma]//ReleaseHoldAll//ExpandAll)
%//ReleaseHoldAll // FillIndices[#,"spinor"]& // Table[#,{a,2},{b,2},{\[Mu],0,3},{\[Nu],0,3}]&
FF0[p,q,x,\[Mu],\[Nu]] // SymmetrizeT // RewriteIndices
FF0[p,q,x,,\[Mu],\[Nu]] // SymmetrizeT // RewriteIndices*)


(* ::Subsection:: *)
(*Vector superfield*)


\[CapitalDelta]x[\[Mu]_] := Module[{a=Unique[], b=Unique[]}, -I TDot[\[Theta][a], \[Sigma][\[Mu], a, b], \[Theta]b[b]]];
\[CapitalDelta]x2 := (-1/2)*\[Theta]\[Theta]*\[Theta]\[Theta]b;
YtoX[exp_] := exp //. {
  (t:NT|GT)[Field[n_,y], any___] :> Module[{\[Mu]=Unique[\[Mu]]}, t[Field[n,x], any] + \[CapitalDelta]x[\[Mu]]*Dx[,\[Mu], t[Field[n,x], any]] + (\[CapitalDelta]x2/2)t[Field[Dx2[n], x], any]],
  (t:NT|GT)[OverBar[Field[n_,yd]],any___] :> Module[{\[Mu]=Unique[\[Mu]]}, t[OverBar[Field[n,x]], any] - \[CapitalDelta]x[\[Mu]]*Dx[,\[Mu], t[Field[n,x], any]] + (\[CapitalDelta]x2/2)t[Field[Dx2[n], x], any]]
}//ReleaseHoldAll//ExpandAll


SymmetrizeT[exp_] := exp//.TDot[w:OrderlessPatternSequence[any___, T[s_,i_,j_],T[t_,j_,k_]]] :> (1/2) TDot[any, Module[{u=Unique[]}, NT["TS", NI[s, "SUNF"], NI[t, "SUNF"], NI[i, "SUNI"], LI[k, "SUNI"]] + I NT["f", NI[s, "SUNF"], NI[t, "SUNF"], NI[u, "SUNF"]]T[u,i,k]]];

ContractT[exp_] := exp//.{
  TDot[w:OrderlessPatternSequence[x___, T[a_,i_,j_], T[b_,j_,k_]]] :> TDot[x,TT[{a,b},i,k]],
  TDot[w:OrderlessPatternSequence[x___, TT[{a__},i_,k_], T[c_,k_,m_]]] :> TDot[x,TT[{a,c},i,m]],
  TDot[w:OrderlessPatternSequence[x___, TT[{a__},i_,j_], T[c_,k_,i_]]] :> TDot[x,TT[{c,a},k,j]],
  TDot[w:OrderlessPatternSequence[x___, TT[{a__},i_,k_], TT[{c__},k_,m_]]] :> TDot[x,TT[{a,c},i,m]]
} //. {
  TDot[a___,b:TT[{x_, y_},p_,q_],c___] /; Not[OrderedQ[{x,y}]] :>((b TDot[a,c])/.{x->y,y->x}),
  TDot[a___,b:TT[{x_, y_},p_,q_],c___] /; OrderedQ[{x,y}] :>((b TDot[a,c]))
}
V[i_, j_] := Module[{a=Unique[], b=Unique[], \[Mu]=Unique[], s=Unique[]}, T[s, i, j]* Total[{
  -TDot[\[Theta][a],\[Sigma][\[Mu],a,b],\[Theta]b[b],A[s,x,,\[Mu]]],
  +TDot[\[Theta][a], \[Theta][,a], \[Theta]b[,b], \[Lambda]b[s,x,b]],
  +TDot[\[Theta]b[,a], \[Theta]b[a], \[Theta][b], \[Lambda][s,x,,b]],
  (1/2)TDot[\[Theta][a],\[Theta][,a],\[Theta]b[,b],\[Theta]b[b],dd[s,x]]
}]]
expV[r_, i_, j_] := Module[{k=Unique[]}, \[Delta][i, j, "SUNI"] + r V[i,j] + (r^2/2)TDot[V[i,k],V[k,j]]]// ReleaseHoldAll//ExpandAll


g/:NumericQ[g]:=True
w1 = HoldForm[(-1/(8g))DDb[,b,DDb[b,TDot[expV[-2 g,p,r],DD[,a,expV[2 g,r,q]]]]]];
wExpanded0 = \[Lambda][s,y,,a]T[s,p,q] + dd[s,y]T[s,p,q]\[Theta][,a] + TDot[\[Sigma][\[Mu],\[Nu],a,b],\[Theta][,b]] "FF0"[p,q,y,,\[Mu],\[Nu]] + \[Theta]\[Theta] I \[Sigma][\[Mu],a,b]"DxD"[,\[Mu],\[Lambda]b[s,yd,b]]T[s,p,q];
wExpanded = \[Lambda][s,y,,a]T[s,p,q] + dd[s,y]T[s,p,q]\[Theta][,a] + TDot[\[Sigma][\[Mu],\[Nu],a,b],\[Theta][,b]] FF0[p,q,y,,\[Mu],\[Nu]] + \[Theta]\[Theta] I \[Sigma][\[Mu],a,b]DxD[,\[Mu],Evaluate[\[Lambda]b[s,yd,b]//YtoX]]T[s,p,q] // YtoX;
diff = w1-wExpanded // ReleaseHoldAll // ExpandAll // SortTDot // RewriteIndices;


diff // Switch\[Sigma] // Switch\[Sigma] // SymmetrizeT//ExpandAll//RewriteIndices;
SymmetrizeIndices[Sym\[Sigma][%], {"\[Mu]","\[Nu]"}]//SortTDot//RewriteIndices//LorentzSort//Switch\[Sigma]//ReleaseHoldAll//RewriteIndices


TeXConvert[exp_] := Module[{tmp},
      tmp = exp //. {a->"alpha",b->"beta",c->"gamma",d->"delta",Complex[a_, b_] :> a+b "ii"} // TeXForm // ToString;
      tmp = FixedPoint[StringReplace[{
           " }" -> "}", " ^" -> "^", " _" -> "_", " )" -> ")",
           "\\dot{\\alpha}" -> "\\dalpha", "\\dot{\\beta}" -> "\\dbeta", "\\dot{\\gamma}" -> "\\dgamma", "\\dot{\\delta}" -> "\\ddelta",
           "\\bar{\\theta}" -> "\\btheta",
           "\\bar{\\sigma}" -> "\\bsigma",
           "\\Sigma"->"\\sigma",
           "\\overline{" -> "\\bar{",
           "\\text{Tr}"->"\\Tr",
           "\\text{ii}"->"\\ii",
           "\\text{}"->"{}",
           "\{+\}-"->"-",
           "\{+\}"->"+",
           "_{\\text{dummy}}"->"",
           "^{\\text{dummy}}"->"",
           "\\text{alpha}"->"\\alpha",
           "\\text{beta}"->"\\beta",
           "\\text{gamma}"->"\\gamma",
           "\\text{delta}"->"\\delta",
           "\\text{a}"->"\\alpha",
           "\\text{b}"->"\\beta",
           "\\text{c}"->"\\gamma",
           "\\text{d}"->"\\delta",
           "\\text{s}"->"a",
           "\\text{t}"->"b",
           "\\text{u}"->"c",
           "\\text{F}"->"F",
           "\\text{C}"->"C",
           "\\text{A}"->"A",
           "\\text{DD}"->"D",
           "\\text{M1}"->"M",
           "\\text{M2}"->"N",
           "\\text{i}"->"i",
           "\\text{T}"->"T",
           "\\text{yd}"->"y^*",
           ".\\sigma"->"\\sigma",
           ".\\bsigma"->"\\bsigma",
           a:("\\delta^{\\"~~Repeated[LetterCharacter])~~"}{}_{\\"~~s:Repeated[LetterCharacter]~~"}":>a<>"}_{\\"<>s<>"}",
           a:("\\sigma^{\\"~~Repeated[LetterCharacter]~~"}") ~~ "{}_" :> a<>"_"
     }], tmp];
     tmp = StringReplace[tmp, {"["->"\\bigl(", "]"->"\\bigr)"}];
     tmp = StringReplace[tmp, {"\\left\\bigl"->"\\left", "\\right\\bigr"->"\\right"}];
     tmp]


ToTeX = {};
Express[FF["s",x,\[Mu],\[Nu]]]
Express[FF0["i","j",x,\[Mu],\[Nu]]]
Express[DxD[\[Mu],\[Lambda]["s",x,a]]]
wExpanded0//RewriteIndices//ExpandAll//RewriteIndices//ContractT;
Express[%,Collect[#, _TT]&]
wExpanded//RewriteIndices//ReleaseHoldAll//ExpandAll//RewriteIndices//ContractT;
Express[%,Collect[#, _TT]&]
filehandle = OpenWrite["superfields_gauge_1.raw"];
Do[
  tmp = TeXConvert[t];
  WriteString[filehandle, tmp];
  WriteString[filehandle, "\n\\\\&\n"];
  , {t, ToTeX}];
Close[filehandle];



