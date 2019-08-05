#!/usr/bin/env wolframscript
(* ::Package:: *)

SetDirectory[NotebookDirectory[]];
<<WeylAlgebra`
<<WeylAlgebraDerivedRules`


(* ::Subsection:: *)
(*Common tools*)


TeXConvert[exp_] := Module[{tmp},
      tmp = exp //. {a | "a" -> \[Alpha], b | "b" -> \[Beta], c | "c" -> \[Gamma], d | "d" -> \[Delta], Complex[a_, b_] :> a+b "ii"} // TeXForm // ToString;
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
           "\\text{F}"->"F",
           "\\text{C}"->"C",
           "\\text{A}"->"A",
           "\\text{DD}"->"D",
           "\\text{M1}"->"M",
           "\\text{M2}"->"N",
           ".\\sigma"->"\\sigma",
           ".\\bsigma"->"\\bsigma",
           a:("\\delta^{\\"~~Repeated[LetterCharacter])~~"}{}_{\\"~~s:Repeated[LetterCharacter]~~"}":>a<>"}_{\\"<>s<>"}",
           a:("\\sigma^{\\"~~Repeated[LetterCharacter]~~"}") ~~ "{}_" :> a<>"_"
     }], tmp];
     tmp = StringReplace[tmp, {"["->"\\bigl(", "]"->"\\bigr)"}];
     tmp = StringReplace[tmp, {"\\left\\bigl"->"\\left", "\\right\\bigr"->"\\right"}];
     tmp]
 
SumToList[exp_]  := Module[{tmp = Expand[exp]}, If[Head[tmp] === Plus, List@@tmp, {tmp}]];

RewriteIndices[exp_, format_, indices_:Null] :=
  Module[{old, nottoreplace, toreplace, new, rule},
    old = Cases[exp,  format :> index, All];
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


ToTeX = {};
Express::usage = "";
Attributes[Express] = {HoldFirst};
Express[exphold_, apply_:(#&), hold_:True] := If[hold=!=True, Express[exphold//Evaluate, apply, True], Module[{exp},
  exp = apply[ReleaseHoldAll[exphold]] // RewriteIndices // OrderTheta;
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

CC[i_,x_]      := NT[Field["C"[i],x]]
dd[i_,x_]      := NT[Field["DD"[i],x]]
M1[i_,x_]      := NT[Field["M1"[i],x]]
M2[i_,x_]      := NT[Field["M2"[i],x]]
\[Chi] [i_,x_,a_]   := GT[Field["\[Chi]"[i],x], UI[a, "spinor"]]
\[Chi] [i_,x_, ,a_] := GT[Field["\[Chi]"[i],x], LI[a, "spinor"]]
\[Chi]b[i_,x_,a_]   := GT[OverBar[Field["\[Chi]"[i],x]], UI[OverDot[a], "spinor"]]
\[Chi]b[i_,x_, ,a_] := GT[OverBar[Field["\[Chi]"[i],x]], LI[OverDot[a], "spinor"]]
\[Lambda] [i_,x_,a_]   := GT[Field["\[Lambda]"[i],x], UI[a, "spinor"]]
\[Lambda] [i_,x_, ,a_] := GT[Field["\[Lambda]"[i],x], LI[a, "spinor"]]
\[Lambda]b[i_,x_,a_]   := GT[OverBar[Field["\[Lambda]"[i],x]], UI[OverDot[a], "spinor"]]
\[Lambda]b[i_,x_, ,a_] := GT[OverBar[Field["\[Lambda]"[i],x]], LI[OverDot[a], "spinor"]]
A [i_,x_,\[Mu]_]   := NT[Field["A"[i],x], UI[\[Mu], "lorentz"]]
A [i_,x_,,\[Mu]_]  := NT[Field["A"[i],x], LI[\[Mu], "lorentz"]]


(* for spinors: (unused rule)
Conjugate[GT[a:NameType, b:RepeatedNull[IndexType]]] := SwitchOverDot[GT[OverBar[a], b]]
 -> OverBar[Field[\[Psi][i], x]] etc...
*)

NT /: Conjugate[NT[Field[f_,x_], any___]] := NT[Field[Conj[f], x], any] // SwitchOverDot
Conj[Conj[f_]] := f
Conj[(f:"C"|"M1"|"M2"|"A"|"DD")[i_]] := f[i]

(* Derivatives *)

IsGrassmann[x_] := Switch[Head[x], "x", False, "\[Theta]", True, "\[Theta]b", True, _, Print[x];Abort[]]
Dx [index_,  any_] := Deriv["x"[UI[index, "lorentz"]], any]             (* Dx[\[Mu]]   = \[PartialD]^\[Mu];              \!\(\(Dx[\(,\)\(\[Mu]\)]\)\ \ \  = \ 
\*SubscriptBox[\(\[PartialD]\), \(\[Mu]\)]\) *)
Dx [,index_, any_] := Deriv["x"[LI[index, "lorentz"]], any]             (* Dx[\[Mu]]   = \[PartialD]^\[Mu];              \!\(\(Dx[\(,\)\(\[Mu]\)]\)\ \ \  = \ 
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

(* Derivative + conjugate *)
Conj[Dx[f_]] := Dx[Conj[f]]
Conj[Dx2[f_]] := Dx2[Conj[f]]


(* ::Subsection:: *)
(*Chiral superfield*)


CommuteDerivatives[exp_] := exp//.{TDot[x1___, DT[a_], Deriv[b_, f]] /; Not[FreeQ[{a,b}, "lorentz"]] :> TDot[x1, dd[a b,f]], Deriv[a_, Deriv[b_, f]]/;Not[FreeQ[{a,b}, "lorentz"]]:>dd[a b,f]} // ExpandAll
QQ[,a,QQ[,b, f]]  + QQ[,b,QQ[,a, f]] // ReleaseHoldAll//RewriteIndices//CollectTheta//CommuteDerivatives//SortTDot//CommuteDerivatives
QQ[,a,DD[,b, f]]  + DD[,b,QQ[,a, f]] // ReleaseHoldAll//RewriteIndices//CollectTheta//CommuteDerivatives//SortTDot//CommuteDerivatives
QQ[,a,DDb[,b, f]] + DDb[,b,QQ[,a, f]] // ReleaseHoldAll//RewriteIndices//CollectTheta//CommuteDerivatives
DD[,a,DD[,b, f]]  + DD[,b,DD[,a, f]] // ReleaseHoldAll//RewriteIndices//CollectTheta//CommuteDerivatives//SortTDot//CommuteDerivatives
DD[,a,QQb[,b, f]] + QQb[,b,DD[,a, f]] // ReleaseHoldAll//RewriteIndices//CollectTheta//CommuteDerivatives
QQb[,a,DDb[,b, f]] + DDb[,b,QQb[,a, f]] // ReleaseHoldAll//RewriteIndices//CollectTheta//CommuteDerivatives//SortTDot//CommuteDerivatives


QQ[,a,QQb[,b, f]] + QQb[,b,QQ[,a, f]] // ReleaseHoldAll//RewriteIndices//CollectTheta//CommuteDerivatives
DD[,a,DDb[,b, f]] + DDb[,b,DD[,a, f]] // ReleaseHoldAll//RewriteIndices//CollectTheta//CommuteDerivatives


ToTeX = {};
Express[QQ[,a,f]]
Express[QQb[,a,f]]
Express[QQ[a,f]]
Express[QQb[a,f]]
Express[DD[,a, f]]
Express[DDb[,a, f]]
Express[DD[a, f]]
Express[DDb[a, f]]

Express[Evaluate[D\[Theta][a, HoldForm[\[Theta]\[Theta]]]]]
Express[Evaluate[D\[Theta][,a, HoldForm[\[Theta]\[Theta]]]]]
Express[Evaluate[D\[Theta]b[a, HoldForm[\[Theta]\[Theta]b]]]]
Express[Evaluate[D\[Theta]b[,a, HoldForm[\[Theta]\[Theta]b]]]]
Express[Evaluate[D\[Theta][a,D\[Theta][b, HoldForm[\[Theta]\[Theta]]]]]]
Express[Evaluate[D\[Theta][,a,D\[Theta][b, HoldForm[\[Theta]\[Theta]]]]]]
Express[Evaluate[D\[Theta][a,D\[Theta][,b, HoldForm[\[Theta]\[Theta]]]]]]
Express[Evaluate[D\[Theta][,a,D\[Theta][,b, HoldForm[\[Theta]\[Theta]]]]]]
Express[Evaluate[D\[Theta]b[a,D\[Theta]b[b, HoldForm[\[Theta]\[Theta]b]]]]]
Express[Evaluate[D\[Theta]b[,a,D\[Theta]b[b, HoldForm[\[Theta]\[Theta]b]]]]]
Express[Evaluate[D\[Theta]b[a,D\[Theta]b[,b, HoldForm[\[Theta]\[Theta]b]]]]]
Express[Evaluate[D\[Theta]b[,a,D\[Theta]b[,b, HoldForm[\[Theta]\[Theta]b]]]]]

filehandle = OpenWrite["superfields_0.raw"];
Do[
  tmp = TeXConvert[t];
  WriteString[filehandle, tmp];
  WriteString[filehandle, "\n\\\\&\n"];
  , {t, ToTeX}];
Close[filehandle];


\[CapitalDelta]x[\[Mu]_] := Module[{a=Unique[], b=Unique[]}, -I TDot[\[Theta][a], \[Sigma][\[Mu], a, b], \[Theta]b[b]]];
\[CapitalDelta]x2 := (-1/2)*\[Theta]\[Theta]*\[Theta]\[Theta]b;
\[CapitalPhi][i_] := Module[{c=Unique[]}, \[Phi][i,y] + Sqrt[2] TDot[\[Theta][c],\[Psi][i,y,,c]] + \[Theta]\[Theta] F[i,y]]
YtoX[exp_] := exp //. {
  (t:NT|GT)[Field[n_,y], any___] :> Module[{\[Mu]=Unique[\[Mu]]}, t[Field[n,x], any] + \[CapitalDelta]x[\[Mu]]*Dx[,\[Mu], t[Field[n,x], any]] + (\[CapitalDelta]x2/2)t[Field[Dx2[n], x], any]]//ReleaseHoldAll//ExpandAll
}


ToTeX = {};
Express[\[Phi]["dummy",HoldForm[y]], YtoX, False]
Express[\[CapitalPhi][i]]
Express[\[CapitalPhi][i]//YtoX]
Express[\[CapitalPhi][i]//YtoX//Conjugate]
Express[(\[CapitalPhi][i]//YtoX//Conjugate)(\[CapitalPhi][j]//YtoX)]
Express[ThetaCoeff[(\[CapitalPhi][i]//YtoX)(\[CapitalPhi][j]//YtoX), 2, 0]]
Express[ThetaCoeff[(\[CapitalPhi][i]//YtoX)(\[CapitalPhi][j]//YtoX)(\[CapitalPhi][k]//YtoX), 2, 0]]

filehandle = OpenWrite["superfields_1.raw"];
Do[
  tmp = TeXConvert[t];
  WriteString[filehandle, tmp];
  WriteString[filehandle, "\n\\\\&\n"];
  , {t, ToTeX}];
Close[filehandle];  


expIKP = Module[{
    IKP=Function[i, (Ik \[CapitalPhi][i]//YtoX)//.{\[Phi][i,x]:>\[Phi], F[i,x]:>F}] (*delayed evaluation*)
  },
  1 + IKP[i] + (1/2)IKP[i]IKP[i] + (1/6)IKP[i]IKP[i]IKP[i] + (1/24)IKP[i]IKP[i]IKP[i]IKP[i]+ (1/120)IKP[i]IKP[i]IKP[i]IKP[i]IKP[i]]//ReleaseHoldAll//ExpandAll;


expIKPexpanded = Total[{
  expN[Ik \[Phi], 5],
  (-Sqrt[2]Ik TDot[-\[Theta][a],\[Psi][i,x,,a]]expN[Ik \[Phi],4]),
  (-I Ik)expN[Ik \[Phi], 4]TDot[\[Theta][a],\[Sigma][\[Mu],a,b],\[Theta]b[b],NT[Field[Dx["\[Phi]"[i]], x], LI[\[Mu], "lorentz"]]],
  (Ik F expN[Ik \[Phi], 4]\[Theta]\[Theta] - (Ik^2/2) TDot[\[Psi][i, x,a],\[Psi][i, x,,a]]expN[Ik \[Phi], 3]\[Theta]\[Theta]),
  (Ik I)/Sqrt[2] expN[Ik \[Phi],4] TDot[GT[Field[Dx["\[Psi]"[i]], x], LI[\[Mu], "lorentz"], UI[a, "spinor"]], \[Sigma][\[Mu], a, b], \[Theta]b[b]] \[Theta]\[Theta],
  ( Ik^2 I/Sqrt[2]) \[Theta]\[Theta] expN[Ik \[Phi], 3]TDot[GT[Field["\[Psi]"[i], x], UI[a, "spinor"]], \[Sigma][\[Mu],a,b],\[Theta]b[b], NT[Field[Dx["\[Phi]"[i]], x], LI[\[Mu], "lorentz"]]],
  (-Ik/4 expN[Ik \[Phi],4]NT[Field[Dx2["\[Phi]"[i]],x]] + (-Ik^2/4)expN[Ik \[Phi],3] TDot[NT[Field[Dx["\[Phi]"[i]],x],LI[\[Mu],"lorentz"]],NT[Field[Dx["\[Phi]"[i]],x],UI[\[Mu],"lorentz"]]]) \[Theta]\[Theta] \[Theta]\[Theta]b}
];
(expIKP - expIKPexpanded) //. expN[a_, n_] :> Sum[a^i/i!, {i, 0, n}]// ReleaseHoldAll // RewriteIndices


ToTeX = {};
expIKPexpanded //. expN[a_, n_] :> Exp[a] // ReleaseHoldAll // RewriteIndices // CollectTheta // Expand
Express[%]
filehandle = OpenWrite["superfields_2.raw"];
Do[
  tmp = TeXConvert[t];
  WriteString[filehandle, tmp];
  WriteString[filehandle, "\n\\\\&\n"];
  , {t, ToTeX}];
Close[filehandle];


(* ::Subsection:: *)
(*Vector superfield*)


V[i_] := Module[{a=Unique[], b=Unique[], c=Unique[], \[Mu]=Unique[]}, Total[{
  CC[i,x],
  +I TDot[\[Theta][a],   \[Chi][i, x,,a]],
  -I TDot[\[Theta]b[,a], \[Chi]b[i, x,a]],
  (1/2)HoldForm[TDot][\[Theta][a],\[Theta][,a],M1[i,x]+I M2[i, x]],
  (1/2)HoldForm[TDot][\[Theta]b[,a],\[Theta]b[a],M1[i,x]-I M2[i, x]],
  -TDot[\[Theta][a],\[Sigma][\[Mu],a,b],\[Theta]b[b],A[i,x,,\[Mu]]],
  +TDot[\[Theta][a], \[Theta][,a], \[Theta]b[,b], \[Lambda]b[i,x,b]],
  (+1/2)TDot[\[Theta][a], \[Theta][,a], \[Theta]b[,b], \[Sigma]b[\[Mu],b,c],HoldForm[Dx][,\[Mu],\[Chi][i,x,,c]]],
  +TDot[\[Theta]b[,a], \[Theta]b[a], \[Theta][b], \[Lambda][i,x,,b]],
  (-1/2)TDot[\[Theta]b[,a], \[Theta]b[a], \[Theta][b], \[Sigma][\[Mu],b,c],HoldForm[Dx][,\[Mu],\[Chi]b[i,x,c]]],
  (1/2)TDot[\[Theta][a],\[Theta][,a],\[Theta]b[,b],\[Theta]b[b],dd[i,x]],
  (-1/4)TDot[\[Theta][a],\[Theta][,a],\[Theta]b[,b],\[Theta]b[b],HoldForm[Dx][\[Mu],HoldForm[Dx][,\[Mu],CC[i,x]]]]
}]]


V[i]//(# - Conjugate[#])& // ReleaseHoldAll //SortTDot // RewriteIndices


V[i] - I(\[CapitalPhi][i]//YtoX) +I (\[CapitalPhi][i]//YtoX//Conjugate);
V[i]/.{
   NT[Field["C"[i], x]] -> NT[Field["C"[i], x]] - I \[Phi][i,x]+I Conjugate[\[Phi][i,x]],
   w:(NT[Field["M1"[i], x]] + I NT[Field["M2"[i], x]]):> w - 2 I F[i,x],
   w:(NT[Field["M1"[i], x]] - I NT[Field["M2"[i], x]]):> w + 2 I Conjugate[F[i,x]],
   GT[Field["\[Chi]"[i],x],s:(_UI|_LI)] :> GT[Field["\[Chi]"[i],x],s] - Sqrt[2] GT[Field["\[Psi]"[i],x],s],
   GT[OverBar[Field["\[Chi]"[i],x]],s:(_UI|_LI)] :> GT[OverBar[Field["\[Chi]"[i],x]],s] -Sqrt[2] GT[OverBar[Field["\[Psi]"[i],x]],s],
   NT[Field["A"[i],x],s:(_UI|_LI)] :> NT[Field["A"[i],x],s] + NT[Field[Dx["\[Phi]"[i]],x],s] + NT[Field[Conj[Dx["\[Phi]"[i]]],x],s]
}
%%-% // ReleaseHoldAll //ExpandAll// RewriteIndices // CollectTheta // RewriteIndices // SortTDot


expKV = Module[{
    KV=Function[i, (k V[i])] (*delayed evaluation*)
  },
  1 + KV[i] + (1/2)KV[i]KV[i] + (1/6)KV[i]KV[i]KV[i] + (1/24)KV[i]KV[i]KV[i]KV[i]+ (1/120)KV[i]KV[i]KV[i]KV[i]KV[i]]//ReleaseHoldAll//ExpandAll//ReleaseHoldAll;


expKVexpanded = Total[{
  expN[k CC, 5],
  I k TDot[\[Theta][a],\[Chi][i,x,,a]]expN[k CC, 4],
  -I k TDot[\[Theta]b[,a],\[Chi]b[i,x,a]]expN[k CC, 4],
  k^2 TDot[\[Theta][a],\[Chi][i,x,,a]]TDot[\[Theta]b[,a],\[Chi]b[i,x,a]]expN[k CC, 3],
  -k TDot[\[Theta][a],\[Sigma][,\[Mu],a,b],\[Theta]b[b],A[i,x,\[Mu]]] expN[k CC, 4],
  k(1/2)TDot[\[Theta][a],\[Theta][,a],M1[i,x]+I M2[i, x]]expN[k CC, 4],
  (k^2/4)\[Theta]\[Theta] TDot[\[Chi][i,x,a],\[Chi][i,x,,a]]expN[k CC, 3],
  k(1/2)TDot[\[Theta]b[,a],\[Theta]b[a],M1[i,x]-I M2[i, x]]expN[k CC, 4],
  (k^2/4)\[Theta]\[Theta]b TDot[\[Chi]b[i,x,,a],\[Chi]b[i,x,a]]expN[k CC, 3],
  \[Theta]\[Theta]b(
      k (TDot[\[Theta][a],\[Lambda][i,x,,a]]-(1/2) TDot[\[Theta][a], \[Sigma][\[Mu],a,c],Dx[,\[Mu],\[Chi]b[i,x,c]]])expN[k CC,4]
      +(I k^2/2) TDot[\[Theta][a],\[Chi][i,x,,a]]expN[k CC,3](M1[i,x]- I M2[i, x])
      + (I k^3/4) TDot[\[Theta][a],\[Chi][i,x,,a], \[Chi]b[i,x,,b], \[Chi]b[i,x,b]]expN[k CC,2]
      + (I k^2/2) TDot[\[Chi]b[i,x,,a], \[Sigma]b[,\[Mu],a,b], \[Theta][,b]]A[i,x,\[Mu]]expN[k CC,3]
  ),
  \[Theta]\[Theta](
      k (TDot[\[Theta]b[,a],\[Lambda]b[i,x,a]]+(1/2) TDot[\[Theta]b[,a], \[Sigma]b[\[Mu],a,c],Dx[,\[Mu],\[Chi][i,x,,c]]])expN[k CC,4]
      -(I k^2/2) TDot[\[Theta]b[,a],\[Chi]b[i,x,a]]expN[k CC,3](M1[i,x]+ I M2[i, x])
      - (I k^3/4) TDot[\[Theta]b[,a],\[Chi]b[i,x,a], \[Chi][i,x,b], \[Chi][i,x,,b]]expN[k CC,2]
      +(I k^2/2) TDot[\[Chi][i,x,a], \[Sigma][,\[Mu],a,b], \[Theta]b[b]]A[i,x,\[Mu]]expN[k CC,3]
  ),
  \[Theta]\[Theta] \[Theta]\[Theta]b k((1/2)dd[i,x]-(1/4)Dx[\[Mu],Dx[,\[Mu],CC[i,x]]]) expN[k CC, 4],
  \[Theta]\[Theta] \[Theta]\[Theta]b I ((-k^2/2) TDot[\[Lambda][i,x,a],\[Chi][i,x,,a]] - (-k^2/2) TDot[\[Lambda]b[i,x,,a],\[Chi]b[i,x,a]]) expN[k CC, 3],
  \[Theta]\[Theta] \[Theta]\[Theta]b (k^2/4)(TDot[M1[i,x],M1[i,x]]+TDot[M2[i,x],M2[i,x]] + A[i,x,\[Mu]]A[i,x,,\[Mu]])expN[k CC, 3],
 \[Theta]\[Theta] \[Theta]\[Theta]b I ((-k^3/2) (I/4)TDot[\[Chi][i,x,a],\[Chi][i,x,,a]]( M1[i,x] -I M2[i, x]) - (k^3/2)(I/4) TDot[\[Chi]b[i,x,,a],\[Chi]b[i,x,a]](M1[i,x]+I M2[i, x])) expN[k CC, 2],
 \[Theta]\[Theta] \[Theta]\[Theta]b I (k^2/4)TDot[\[Chi]b[i,x,,a], \[Sigma]b[\[Mu],a,c],Dx[,\[Mu],\[Chi][i,x,,c]]] expN[k CC, 3],
 \[Theta]\[Theta] \[Theta]\[Theta]b (-I) (k^2/4)TDot[Dx[,\[Mu],\[Chi]b[i,x,,a]], \[Sigma]b[\[Mu],a,c],\[Chi][i,x,,c]] expN[k CC, 3],
 \[Theta]\[Theta] \[Theta]\[Theta]b k^4/16 TDot[\[Chi][i,x,a],\[Chi][i,x,,a]] TDot[\[Chi]b[i,x,,b],\[Chi]b[i,x,b]] expN[k CC, 1],
 \[Theta]\[Theta] \[Theta]\[Theta]b (k^3/4)TDot[\[Chi]b[i,x,,a], \[Sigma]b[,\[Mu],a,c],\[Chi][i,x,,c]]A[i,x,\[Mu]] expN[k CC, 2]
}];
((expKV //. CC[i,x] -> CC) - expKVexpanded) //. expN[a_, n_] :> Sum[a^i/i!, {i, 0, n}]// ReleaseHoldAll //SortTDot // CollectTheta // RewriteIndices


Vwz[i_] := Module[{a=Unique[], b=Unique[], \[Mu]=Unique[]}, Total[{
  -TDot[\[Theta][a],\[Sigma][\[Mu],a,b],\[Theta]b[b],A[i,x,,\[Mu]]],
  +TDot[\[Theta][a], \[Theta][,a], \[Theta]b[,b], \[Lambda]b[i,x,b]],
  +TDot[\[Theta]b[,a], \[Theta]b[a], \[Theta][b], \[Lambda][i,x,,b]],
  (1/2)TDot[\[Theta][a],\[Theta][,a],\[Theta]b[,b],\[Theta]b[b],dd[i,x]]
}]]
ExpVwz[k_] := 1 + k Vwz[i] + k^2 Vwz[i]Vwz[i]/2


LorentzSort[exp_] := (exp//.{
  (p:NT|GT)[x1__, LI[\[Mu]_,"lorentz"], x2___]/; FreeQ[{x1}, "\[Eta]"] :> Module[{\[Nu]=Unique[]}, \[Eta]L[\[Mu], \[Nu]] p[x1, UI[\[Nu],"lorentz"], x2]]
}//SortTDot//RewriteIndices)//.NT[HoldForm["\[Eta]"], a_, b_] /; Not[OrderedQ[{a,b}]] :> NT[HoldForm["\[Eta]"], b, a]//ReleaseHoldAll;

kinetic = Total[{
  TDot[I \[Psi]b[i,x,,a], \[Sigma]b[\[Mu],a,b],Dx[,\[Mu],\[Psi][j,x,,b]]-I g Q A[i,x,,\[Mu]]\[Psi][j,x,,b]],
  Conjugate[(Dx[\[Mu],\[Phi][i,x]]-I g Q A[i,x,\[Mu]]\[Phi][i,x])](Dx[,\[Mu],\[Phi][j,x]]-I g Q A[i,x,,\[Mu]]\[Phi][j,x])
}]//Simplify[#,{Q\[Element]Reals,g>0}]&

surface = -1/4 Dx[\[Mu],Conjugate[\[Phi][i,x]]]\[Phi][j,x]-1/4Dx[\[Mu],\[Phi][j,x]]Conjugate[\[Phi][i,x]] - (I/2)TDot[\[Psi]b[i,x,,a] ,\[Sigma]b[\[Mu],a,b],\[Psi][j,x,,b]] // Dx[,\[Mu],#]&

ThetaCoeff[(\[CapitalPhi][i]//YtoX//Conjugate)(\[CapitalPhi][j]//YtoX)ExpVwz[2g Q],2,2] - \[Theta]\[Theta] \[Theta]\[Theta]b (kinetic+surface) //ReleaseHoldAll//Expand // CollectTheta // SortTDot // RewriteIndices // LorentzSort


ToTeX = {};
Express[V["dummy"]// ReleaseHoldAll// RewriteIndices // SortTDot]
V["dummy"] - I (\[CapitalPhi]["dummy"]//YtoX) +I (\[CapitalPhi]["dummy"]//YtoX//Conjugate) // ReleaseHoldAll// RewriteIndices // SortTDot;
Express[%]
expKVexpanded //. expN[a_, n_] :> Exp[a] // ReleaseHoldAll // RewriteIndices // CollectTheta
Express[%]
Express[Vwz[i]]
Express[ExpVwz[2g Q]]
Express[(\[CapitalPhi][i]//YtoX//Conjugate)(\[CapitalPhi][j]//YtoX)ExpVwz[2g Q] - \[Theta]\[Theta] \[Theta]\[Theta]b surface // ReleaseHoldAll // ThetaCoeff[#,2,2]& // Switch\[Sigma] // SortTDot // RewriteIndices // LorentzSort]
filehandle = OpenWrite["superfields_3.raw"];
Do[
  tmp = TeXConvert[t];
  WriteString[filehandle, tmp];
  WriteString[filehandle, "\n\\\\&\n"];
  , {t, ToTeX}];
Close[filehandle];



