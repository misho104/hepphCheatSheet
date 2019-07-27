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
           ".\\sigma"->"\\sigma",
           ".\\bsigma"->"\\bsigma",
           a:("\\delta^{\\"~~Repeated[LetterCharacter])~~"}{}_{\\"~~s:Repeated[LetterCharacter]~~"}":>a<>"}_{\\"<>s<>"}",
           a:("\\sigma^{\\"~~Repeated[LetterCharacter]~~"}") ~~ "{}_" :> a<>"_"
     }], tmp];
     tmp = StringReplace[tmp, {"["->"\\bigl(", "]"->"\\bigr)"}];
     tmp = StringReplace[tmp, {"\\left\\bigl"->"\\left", "\\right\\bigr"->"\\right"}];
     tmp]
 
SumToList[exp_]  := Module[{tmp = Expand[exp]}, If[Head[tmp] === Plus, List@@tmp, {tmp}]];

RewriteIndices[exp_, format_, indices_] :=
  Module[{old, nottoreplace, toreplace, new, rule},
    old = Cases[exp,  format :> index, All];
    nottoreplace = Counts[old] /. Association -> List // Cases[#, (p_ -> 1) :> p] &;
    toreplace = Counts[old] /. Association -> List // Cases[#, (p_ -> 2) :> p] &;
    new = Select[indices, FreeQ[nottoreplace, #] &];
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


\[Theta][a_]  := GT["\[Theta]", UI[a, "spinor"]]
\[Theta][,a_] := GT["\[Theta]", LI[a, "spinor"]]
\[Xi][a_]  := GT["\[Xi]", UI[a, "spinor"]]
\[Xi][,a_] := GT["\[Xi]", LI[a, "spinor"]]
\[Chi][a_]  := GT["\[Chi]", UI[a, "spinor"]]
\[Chi][,a_] := GT["\[Chi]", LI[a, "spinor"]]
\[Theta]b[a_]  := GT[OverBar["\[Theta]"], UI[PutOverDot[a], "spinor"]]
\[Theta]b[,a_] := GT[OverBar["\[Theta]"], LI[PutOverDot[a], "spinor"]]
\[Xi]b[a_]  := GT[OverBar["\[Xi]"], UI[PutOverDot[a], "spinor"]]
\[Xi]b[,a_] := GT[OverBar["\[Xi]"], LI[PutOverDot[a], "spinor"]]
\[Chi]b[a_]  := GT[OverBar["\[Chi]"], UI[PutOverDot[a], "spinor"]]
\[Chi]b[,a_] := GT[OverBar["\[Chi]"], LI[PutOverDot[a], "spinor"]]
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

(* for spinors: 
Conjugate[GT[a:NameType, b:RepeatedNull[IndexType]]] := SwitchOverDot[GT[OverBar[a], b]]
 -> OverBar[Field[\[Psi][i], x]] etc...
*)
NT /: Conjugate[NT[Field[f_,x_], any___]] := NT[Field[Conj[f], x], any] // SwitchOverDot
Conj[Conj[f_]] := f

(* Derivative *)
Dx[\[Mu]_, (t:NT|GT)[f:Field[__]|OverBar[Field[__]], any___]] := t[Dx[f], UI[\[Mu], "lorentz"], any]
Dx[,\[Mu]_, (t:NT|GT)[f:Field[__]|OverBar[Field[__]], any___]] := t[Dx[f], LI[\[Mu], "lorentz"], any]
Dx[Field[n_, x_]] := Field[Dx[n], x]
Dx[OverBar[Field[n_, x_]]] := OverBar[Field[Dx[n], x]]
NT[Field[Dx[Dx[n_]], x_], OrderlessPatternSequence[UI[a_, "lorentz"], LI[a_, "lorentz"]], any___] := NT[Field[Dx2[n], x], any]
GT[Field[Dx[Dx[n_]], x_], OrderlessPatternSequence[UI[a_, "lorentz"], LI[a_, "lorentz"]], any___] := GT[Field[Dx2[n], x], any]

(* Derivative + conjugate *)
Conj[Dx[f_]] := Dx[Conj[f]]
Conj[Dx2[f_]] := Dx2[Conj[f]]


(* ::Subsection:: *)
(*Evaluation*)


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



