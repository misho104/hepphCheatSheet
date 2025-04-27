(* ::Package:: *)

(* ::Package:: *)

(* :Time-Stamp: <2024-08-14 04:12:47> *)
(* :Author: Sho Iwamoto / Misho *)


BeginPackage["DiracAlgebra`"];


ReleaseHoldAll::usage = "Removes all Hold patterns.";

NT::usage = "Normal variables (non-Grassmannian tensor).";
GT::usage = "Grassmannian variables.";
UI::usage = "Upper index.";
LI::usage = "Lower index.";
NI::usage = "Non-positional index.";
TDot::usage = "Dot-product.";
Field::usage = "Represents a field.";
$Contraction::usage = "Boolean configuration variable to contract spinor-indices in display or not.";

FlipSign::usage = "FlipSign[a, b, ..., z] is the sign-flip of grassmann product when A is moved to the last.";
\[Epsilon]U::usage = "Levi-Civita tensor with upper indices.";
\[Epsilon]L::usage = "Levi-Civita tensor with lower indices.";
\[Eta]U::usage = "Minkowski metric \[Eta] with upper indices.";
\[Eta]L::usage = "Minkowski metric \[Eta] with lower indices.";
gU::usage = "General metric g with upper indices.";
gL::usage = "General metric g with lower indices.";
\[Gamma]::usage = "Gamma matrices in Chiral representation.";
\[Gamma]U::usage = "Gamma matrices in Chiral representation.";
\[Gamma]L::usage = "Gamma matrices in Chiral representation.";
\[Gamma]5::usage = "Gamma-five matrix in Chiral representation.";
PL::usage = "Left-hand projection operator in Chiral representation."
PR::usage = "Right-hand projection operator in Chiral representation."
One::usage = "4x4 identity matrix."
\[Delta]::usage = "Kronecker-delta.";

FillIndices::usage = "FillIndices evaluates the Einstein summation of specified types.";
SumIndex::usage = "SumIndex calculates the sum over specified index.";
Tablize::usage = "Tablize generates a table over the specified index.";
MakeBoxesNT::usage = "hoge";


Begin["`Private`"];

System`Convert`CommonDump`templateBoxToDisplay = BoxForm`TemplateBoxToDisplayBoxes;

(* Object definition in BNF *)
LabelType = _Symbol | _String;
LabelTypeOrI = LabelType | _Integer;

IndexClassType = _String;
UpperIndexType = UI[LabelTypeOrI, IndexClassType];
LowerIndexType = LI[LabelTypeOrI, IndexClassType];
IndexType = (UI|LI|NI)[LabelTypeOrI, IndexClassType];

NameType = _Symbol | _String | _Field;
If[ValueQ[Global`$ExtraNameType], NameType = NameType | Global`$ExtraNameType];

NormalTensorType = NT[NameType | OverBar[NameType], RepeatedNull[IndexType]];
GrassmannTensorType = GT[NameType | OverBar[NameType], RepeatedNull[IndexType]];
TensorType = NormalTensorType | GrassmannTensorType;

BlankType := Blank|BlankSequence|BlankNullSequence;
NoPattern[ex_] := FreeQ[Hold[ex], BlankType];
Attributes[NoPattern] = {HoldAllComplete};

(* Format *)
Sequence[GT, NameType | OverBar[NameType] | _Row, RepeatedNull[IndexType]] // (#1 /: MakeBoxes[obj: #1[n:#2|HoldForm[#2], i:#3], f:StandardForm|TraditionalForm] := MakeBoxesNT[f, Style[#, Red]&, n, i] // ToBoxes // InterpretationBox[#,obj] &) &;
Sequence[NT, NameType | OverBar[NameType] | _Row, RepeatedNull[IndexType]] // (#1 /: MakeBoxes[obj: #1[n:#2|HoldForm[#2], i:#3], f:StandardForm|TraditionalForm] := MakeBoxesNT[f, #&, n, i] // ToBoxes // InterpretationBox[#,obj] &) &;
MakeBoxesNT$[f_, c_, HoldForm["\[Gamma]5"], any___] := MakeBoxesNT$[f, c, "\[Gamma]", LI["5", "other"], any]
MakeBoxesNT$[f_, c_, HoldForm["PL"], any___] := MakeBoxesNT$[f, c, "P", LI["L", "other"], any]
MakeBoxesNT$[f_, c_, HoldForm["PR"], any___] := MakeBoxesNT$[f, c, "P", LI["R", "other"], any]
MakeBoxesNT$[f_, c_, HoldForm["One"], any___] := MakeBoxesNT$[f, c, Style["1", Bold], any]
MakeBoxesNT$[f_, c_, n_] := c[n];
MakeBoxesNT$[f_, c_, n_, UI[a:LabelTypeOrI, _]] := Superscript[c[n], a]
MakeBoxesNT$[f_, c_, n_, (LI|NI)[a:LabelTypeOrI, _]] := Subscript[c[n], a]
MakeBoxesNT$[f_, c_, n_, a:Repeated[_UI]] := Row[{a}[[All, 1]]] // Superscript[c[n], #]&
MakeBoxesNT$[f_, c_, n_, a:Repeated[_LI|_NI]] := Row[{a}[[All, 1]]] // Subscript[c[n], #]&
MakeBoxesNT$[f_, c_, n_, any__, a:Repeated[_UI]] := Row[{MakeBoxesNT$[f, c, n, any], MakeBoxesNT$[f, c, "", a]}]
MakeBoxesNT$[f_, c_, n_, any__, a:Repeated[_LI|_NI]] := Row[{MakeBoxesNT$[f, c, n, any], MakeBoxesNT$[f, c, "", a]}]
MakeBoxesNT = MakeBoxesNT$; (* for extensions *)

TDot /: MakeBoxes[obj: TDot[a__], f:StandardForm] := Dot[TDotPreFormat[a]] // ToBoxes // InterpretationBox[#,obj] &
TDot /: MakeBoxes[obj: TDot[a__], f:TraditionalForm] := Row[{TDotPreFormat[a]}] // ToBoxes // InterpretationBox[#,obj] &

TDotPreFormat$Target = ("\[Gamma]"|HoldForm["\[Gamma]"]|"\[Gamma]5"|HoldForm["\[Gamma]5"]|HoldForm["PL"]|HoldForm["PR"]|HoldForm["One"]);
TDotPreFormat$SpinorRow[{a_, GT[{b__}]}, s___] := TDotPreFormat$SpinorRow[{a, b}, s]
TDotPreFormat$SpinorRow[{GT[{a__}], b_}, s___] := TDotPreFormat$SpinorRow[{a, b}, s]
TDotPreFormat$[seq___] := Module[{objs = {seq}},
  objs = objs //. {List[
    x1___,
    GT[a1:Transpose[NameType]|OverBar[NameType]|ConjugateTranspose[NameType], a2___, NI[a4:LabelType, "spinor"]],
    GT[b1:NameType, NI[a4_, "spinor"]] | TDotPreFormat$SpinorRow[b1_, NI[a4_, "spinor"]],
    x2___
  ] /; FreeQ[{a2}, "spinor"] :> List[x1, TDotPreFormat$SpinorRow[{GT[a1, a2], GT[b1]}], x2], List[
    x1___,
    NT[a1:TDotPreFormat$Target, a2___, a3:NI[LabelTypeOrI, "spinor"], NI[a4:LabelType, "spinor"]],
    GT[b1:NameType, NI[a4_, "spinor"]] | TDotPreFormat$SpinorRow[b1_, NI[a4_, "spinor"]],
    x2___
  ] /; FreeQ[{a2}, "spinor"] :> List[x1, TDotPreFormat$SpinorRow[{NT[a1, a2], GT[b1]}, a3], x2], List[
    x1___,
    GT[b1:NameType, NI[a3:LabelType, "spinor"]] | TDotPreFormat$SpinorRow[b1_, NI[a3:LabelType, "spinor"]],
    NT[a1:TDotPreFormat$Target, a2___, NI[a3_, "spinor"], a4:NI[LabelTypeOrI, "spinor"]],
    x2___
  ] /; FreeQ[{a2}, "spinor"] :> List[x1, TDotPreFormat$SpinorRow[{GT[b1], NT[a1, a2]}, a4], x2]};
  Sequence@@(objs //. TDotPreFormat$SpinorRow[List[a___], s___] :> NT[Row[{"(", a, ")"}], s])]
$Contraction = True;
TDotPreFormat$disabled[seq___] := seq;
TDotPreFormat := If[$Contraction, TDotPreFormat$, TDotPreFormat$disabled]


ReleaseHoldAll[exp_] := FixedPoint[ReleaseHold, exp]

IndexIter::any = "Need to specify index class, not any.";
IndexIter[name_] := Switch[name,
  "lorentz", {0, 1, 2, 3},
  "spinor", {1, 2, 3, 4},
  "SU2I", {1, 2},
  "SU2F", {1, 2, 3},
  "any", Message[IndexIter::any]; Abort[],
  _, Abort[]];

(* spinor index moves last *)
NT[x__, a:(NI[_, "spinor"]), b:((UI|LI)[_, type_]), y___] /; type =!= "spinor" := NT[x, b, a]
GT[x__, a:(NI[_, "spinor"]), b:((UI|LI)[_, type_]), y___] /; type =!= "spinor" := GT[x, b, a]


(* Conjugate Operation is "defined" For (single) Grassmann-type tensor. *)
(*
DO WE NEED? also, Reverse is OK for grassmann????
GT /: Conjugate[GT[OverBar[a:NameType], b:RepeatedNull[IndexType]]] := SwitchOverDot[GT[a, b]]
GT /: Conjugate[GT[a:NameType, b:RepeatedNull[IndexType]]] := SwitchOverDot[GT[OverBar[a], b]]
TDot /: Conjugate[TDot[a___]] := TDot@@(Reverse[Conjugate/@{a}])
*)

(* Product of tensor *)
FlipSign[a_NT, ___] := 1
FlipSign[a_GT] := 1
FlipSign[a_GT, b_NT, c___] := FlipSign[a, c]
FlipSign[a_GT, b_GT, c___] := (-1)FlipSign[a, c]

TDot::GrassmannProduct = "Invalid grassman product found: `1`.";
TDot[] := 1;
TDot[a:_NT|_GT] := a;

TDot[x1___, Times[a:Except[_GT], b__], x2___] := TDot[x1, a, Times[b], x2]
TDot[x1___, Plus[a_, b__], x2___] := TDot[x1, a, x2] + TDot[x1, Plus[b], x2]
TDot[x1___, TDot[x2___], x3___] := TDot[x1, x2, x3]

TDot[x1___, a_List, x2___] := TDot[x1, #, x2] &/@ a;

TDot[x1___, a_, x2___] /; NumericQ[a] := a TDot[x1, x2]
TDot[x1___, a_Symbol, x2___] := a TDot[x1, x2]
TDot /: TDot[a___]TDot[b___] := TDot[a,b]

TDot[OrderlessPatternSequence[a:GT[___], a_, ___]] := 0

(* Times are included in TDot (but not define for GT because of order issue *)
NT /: Times[a_NT, b_NT] := TDot[a, b]
NT /: Times[a_NT, b_GT] := TDot[a, b]
NT /: Times[a_GT, b_NT] := TDot[a, b]
TDot /: Times[a:(_NT|_GT), TDot[b__]] := TDotProduct[{a}, {b}]
TDot /: Times[TDot[a__], b:(_NT|_GT)] := TDotProduct[{a}, {b}]
TDotProduct[a_List, b_List] := If[OddQ[Count[a, _GT] * Count[b, _GT]], Message[TDot::GrassmannProduct, {a,b}]; Abort[], TDot[Sequence@@a, Sequence@@b]]


(* Eta-contraction rule *)
TDot[x1___, NT["\[Eta]", UI[a:LabelTypeOrI, "lorentz"], UI[b:LabelType, "lorentz"]], x2___, (n:GT|NT)[n1___, LI[b_, "lorentz"], n2___], x3___] := TDot[x1, x2, n[n1, UI[a, "lorentz"], n2], x3]
TDot[x1___, NT["\[Eta]", LI[a:LabelTypeOrI, "lorentz"], LI[b:LabelType, "lorentz"]], x2___, (n:GT|NT)[n1___, UI[b_, "lorentz"], n2___], x3___] := TDot[x1, x2, n[n1, LI[a, "lorentz"], n2], x3]
TDot[x1___, (n:GT|NT)[n1___, LI[b_, "lorentz"], n2___], x2___, NT["\[Eta]", UI[a:LabelTypeOrI, "lorentz"], UI[b:LabelType, "lorentz"]], x3___] := TDot[x1, x2, n[n1, UI[a, "lorentz"], n2], x3]
TDot[x1___, (n:GT|NT)[n1___, UI[b_, "lorentz"], n2___], x2___, NT["\[Eta]", LI[a:LabelTypeOrI, "lorentz"], LI[b:LabelType, "lorentz"]], x3___] := TDot[x1, x2, n[n1, LI[a, "lorentz"], n2], x3]

(* Kronecker Delta: UI is in front of LI. *)
NT["\[Delta]", a:LI[LabelTypeOrI, IndexClassType], b:UI[LabelTypeOrI, IndexClassType]] := NT["\[Delta]", b, a]
TDot[x1___, NT["\[Delta]", UI[a:LabelTypeOrI, c:IndexClassType|"any"], LI[b:LabelType, c:IndexClassType|"any"]], x2___, (n:GT|NT)[n1___, (t:UI|NI)[b_, c_], n2___], x3___] := TDot[x1, x2, n[n1, t[a, c], n2], x3]
TDot[x1___, NT["\[Delta]", UI[a:LabelType, c:IndexClassType|"any"], LI[b:LabelTypeOrI, c:IndexClassType|"any"]], x2___, (n:GT|NT)[n1___, (t:LI|NI)[a_, c_], n2___], x3___] := TDot[x1, x2, n[n1, t[b, c], n2], x3]
TDot[x1___, (n:GT|NT)[n1___, (t:UI|NI)[b_, c_], n2___], x2___, NT["\[Delta]", UI[a:LabelTypeOrI, c:IndexClassType|"any"], LI[b:LabelType, c:IndexClassType|"any"]], x3___] := TDot[x1, n[n1, t[a, c], n2], x2, x3]
TDot[x1___, (n:GT|NT)[n1___, (t:LI|NI)[a_, c_], n2___], x2___, NT["\[Delta]", UI[a:LabelType, c:IndexClassType|"any"], LI[b:LabelTypeOrI, c:IndexClassType|"any"]], x3___] := TDot[x1, n[n1, t[b, c], n2], x2, x3]
NT["\[Eta]", f:OrderlessPatternSequence[LI[a:LabelTypeOrI, "lorentz"], UI[b:LabelTypeOrI, "lorentz"]]] := NT["\[Delta]", f]

(* general metric g *)
TDot[x1___, NT[Field["g"], a1___, UI[j_, "lorentz"], a2___], x2___, NT[Field["g"], b1___, LI[j_, "lorentz"], b2___], x3___] := TDot[x1, x2, x3, NT["\[Delta]", a1, a2, b1, b2]]
TDot[x1___, NT[Field["g"], a1___, LI[j_, "lorentz"], a2___], x2___, NT[Field["g"], b1___, UI[j_, "lorentz"], b2___], x3___] := TDot[x1, x2, x3, NT["\[Delta]", a1, a2, b1, b2]]


(* Objects *)
Metric[i:0|1|2|3] := If[i==0, 1, -1]
DiracMatrices = {
  {{0,0,1,0},{0,0,0,1},{1,0,0,0},{0,1,0,0}},
  {{0,0,0,1},{0,0,1,0},{0,-1,0,0},{-1,0,0,0}},
  {{0,0,0,-I},{0,0,I,0},{0,I,0,0},{-I,0,0,0}},
  {{0,0,1,0},{0,0,0,-1},{-1,0,0,0},{0,1,0,0}},
  {{-1,0,0,0},{0,-1,0,0},{0,0,1,0},{0,0,0,1}}
};


\[Epsilon]U[a_, b_, c_, d_] := NT[HoldForm["\[Epsilon]"], UI[a, "lorentz"], UI[b, "lorentz"], UI[c, "lorentz"], UI[d, "lorentz"]]
\[Epsilon]L[a_, b_, c_, d_] := NT[HoldForm["\[Epsilon]"], LI[a, "lorentz"], LI[b, "lorentz"], LI[c, "lorentz"], LI[d, "lorentz"]]

NT["\[Epsilon]", ___, a:IndexType, ___, a_, ___] := 0
NT["\[Epsilon]", x___, pos_[a:LabelTypeOrI, type_], pos_[b:LabelTypeOrI, type_], y___] /; Not[OrderedQ[{a, b}]] := (-1) NT["\[Epsilon]", x, pos[b, type], pos[a, type], y]

NT["\[Epsilon]", UI[0, "lorentz"], UI[1, "lorentz"], UI[2, "lorentz"], UI[3, "lorentz"]] := +1
NT["\[Epsilon]", LI[0, "lorentz"], LI[1, "lorentz"], LI[2, "lorentz"], LI[3, "lorentz"]] := -1 (* beware! *)

\[Eta]U[\[Mu]_, \[Nu]_] := NT[HoldForm["\[Eta]"], UI[\[Mu], "lorentz"], UI[\[Nu], "lorentz"]]
\[Eta]L[\[Mu]_, \[Nu]_] := NT[HoldForm["\[Eta]"], LI[\[Mu], "lorentz"], LI[\[Nu], "lorentz"]]
gU[\[Mu]_, \[Nu]_] := NT[Field["g"], UI[\[Mu], "lorentz"], UI[\[Nu], "lorentz"]]
gL[\[Mu]_, \[Nu]_] := NT[Field["g"], LI[\[Mu], "lorentz"], LI[\[Nu], "lorentz"]]

\[Gamma][\[Mu]_, a_, b_]  := \[Gamma]U[\[Mu], a, b]
\[Gamma]U[\[Mu]_, a_, b_] := NT[HoldForm["\[Gamma]"], UI[\[Mu], "lorentz"], NI[a, "spinor"], NI[b, "spinor"]]
\[Gamma]L[\[Mu]_, a_, b_] := NT[HoldForm["\[Gamma]"], LI[\[Mu], "lorentz"], NI[a, "spinor"], NI[b, "spinor"]]
\[Gamma]5[a_, b_]         := NT[HoldForm["\[Gamma]5"], NI[a, "spinor"], NI[b, "spinor"]]
PL[a_, b_]                := NT[HoldForm["PL"], NI[a, "spinor"], NI[b, "spinor"]]
PR[a_, b_]                := NT[HoldForm["PR"], NI[a, "spinor"], NI[b, "spinor"]]
One[a_, b_]               := NT[HoldForm["One"], NI[a, "spinor"], NI[b, "spinor"]]

\[Delta][a_, b_, class:IndexClassType] := NT[HoldForm["\[Delta]"], UI[a, class], LI[b, class]];
\[Delta][a_, b_] := \[Delta][a, b, "any"];


(* definitions *)
NT["\[Delta]", UI[a_Integer, (cls:IndexClassType)|"any"], LI[a_, (cls_)|"any"]] := 1

NT["\[Delta]", UI[a_Integer, (cls:IndexClassType)|"any"], LI[b_Integer, (cls_)|"any"]] /; a!=b := 0

NT["\[Delta]", x:UI[a:LabelType, cls:IndexClassType], y:LI[a_, cls_]] := SumIndex[1, {a, cls}]

NT["\[Eta]", UI[\[Mu]:0|1|2|3, "lorentz"], UI[\[Nu]:0|1|2|3, "lorentz"]] := If[\[Mu]==\[Nu], Metric[\[Mu]], 0]
NT["\[Eta]", LI[\[Mu]:0|1|2|3, "lorentz"], LI[\[Nu]:0|1|2|3, "lorentz"]] := If[\[Mu]==\[Nu], Metric[\[Mu]], 0]

NT["\[Gamma]", UI[\[Mu]:0|1|2|3, "lorentz"], NI[a:1|2|3|4, "spinor"], NI[b:1|2|3|4, "spinor"]] := DiracMatrices[[\[Mu]+1, a, b]]
NT["\[Gamma]", LI[\[Mu]:0|1|2|3, "lorentz"], NI[a:1|2|3|4, "spinor"], NI[b:1|2|3|4, "spinor"]] := DiracMatrices[[\[Mu]+1, a, b]] * Metric[\[Mu]]
NT["\[Gamma]5",                              NI[a:1|2|3|4, "spinor"], NI[b:1|2|3|4, "spinor"]] := DiracMatrices[[5, a, b]]
NT["PL",  NI[a_, "spinor"], NI[b_, "spinor"]]  := (One[a, b] - \[Gamma]5[a, b]) / 2
NT["PR",  NI[a_, "spinor"], NI[b_, "spinor"]]  := (One[a, b] + \[Gamma]5[a, b]) / 2
NT["One", NI[a_, "spinor"], NI[b_, "spinor"]] := \[Delta][a, b, "spinor"]

NT[""]



TDot::InvalidIndices = "Invalid indices in `1`.";

FindIndices[a:TDot[RepeatedNull[TensorType]]] := Cases[a, _UI|_LI|_NI, 2] // Select[FreeQ[#[[1]], _Integer]&]

FindUniqueIndices[a:TDot[RepeatedNull[TensorType]]] := Cases[CountsBy[FindIndices[a], #[[1]]&] /. Association->List, Rule[p_,1]:>p]

FindIndicesToContract[a:TDot[RepeatedNull[TensorType]]] := Module[{i=GroupBy[FindIndices[a], Head], upper, lower, nopos},
  upper = Lookup[i, UI, {}];
  lower = Lookup[i, LI, {}];
  nopos = Lookup[i, NI, {}] // Counts;
  If[Intersection[upper, lower]=!={}, Message[TDot::InvalidIndices, a]; Print[3,i]; Abort[]];
  If[Not[DuplicateFreeQ[upper]], Message[TDot::InvalidIndices, a]; Print[i]; Abort[]];
  If[Not[DuplicateFreeQ[lower]], Message[TDot::InvalidIndices, a]; Print[i, i];Abort[]];
  If[Max[List @@ nopos] > 2,  Message[TDot::InvalidIndices, a]; Abort[]];
  Join[Intersection[(List@@#)&/@upper, (List@@#)&/@lower], (List@@#)&/@Cases[nopos /. Association -> List, Rule[p_, 2] :> p]]];

FillIndices$sub[a:TDot[RepeatedNull[TensorType]], indextypes_List] := Module[{tmp = ReleaseHoldAll[a], indices},
  indices = Select[FindIndicesToContract[tmp], MemberQ[indextypes, #[[2]]]&];
  If[Length[indices] > 0, SumIndex[tmp, Evaluate[indices[[1]]]], tmp]];
FillIndices[exp_, indextypes_List] := Module[{tmp = ReleaseHoldAll[exp]},
  FixedPoint[(# /. {a:TDot[RepeatedNull[TensorType]] :> FillIndices$sub[a, indextypes]})&, tmp]]
FillIndices[exp_, indextypes_] := FillIndices[exp, {indextypes}]


SumIndex::InvalidType = "Unsupported type `1`.";
Attributes[SumIndex] = {HoldAll};
SumIndex[exp_] := exp;
SumIndex[exp_, {symbol_, type_}] := Module[{iter, i, result},
  iter = Which[
     MatchQ[type, List[RepeatedNull[_Integer]]], type,
     MatchQ[type, _String], IndexIter[type],
     True, Message[SumIndex::InvalidType, type]; Abort[]];
  Which[
    Head[symbol]===OverDot,
      (* overdot summation *)
      iter = OverDot/@iter;
      result = Sum[exp, {symbol, iter}//Evaluate],
    StringQ[symbol],
      (* string must be replaced by symbols (and escape dotted indices) *)
      i = Unique[];
      result = exp //. symbol -> i //. OverDot[i] -> OverDot[symbol];
      result = Sum[result, {i, iter}//Evaluate],
    True,
      (* non-dot summation; escape dotted indices *)
      i = Unique[];
      result = exp //. OverDot[symbol] -> i;
      result = Sum[result, {symbol, iter}//Evaluate];
      result = result //. i -> OverDot[symbol]
  ];
  result];

Attributes[Tablize] = {HoldAll};
Tablize[exp_] := exp;
Tablize[exp_, {symbol_, type_}, remaining___] := Module[{iter, i, result},
  iter = Which[
     MatchQ[type, List[RepeatedNull[_Integer]]], type,
     MatchQ[type, _String], IndexIter[type],
     True, Message[SumIndex::InvalidType, type]; Abort[]];
  If[Head[symbol]===OverDot,
    (* overdot summation *)
    iter = OverDot/@iter;
    result = Table[exp, {symbol, iter}//Evaluate],
    (* non-dot summation; escape dotted indices *)
    i = Unique[];
    result = exp //. OverDot[symbol] -> i;
    result = Table[result, {symbol, iter}//Evaluate];
    result = result //. i -> OverDot[symbol]];
  Tablize[result, remaining]];


(* TDot order: spinors, \[Eta], non-spinors *)
NoOverlap[e1_, e2_] := DisjointQ[Cases[e1, (UI|LI|NI)[a_, b_]:>{a,b}, All], Cases[e2, (UI|LI|NI)[a_, b_]:>{a,b}, All]]
w:TDot[x1___, a:(_NT|_GT), b:(NT|GT)[___, NI[_, "spinor"], ___], x2___] /; FreeQ[a, "spinor"] && NoPattern[w] := FlipSign[a, b]*TDot[x1, b, a, x2]
w:TDot[x1___, a: NT[x_, ___], b: NT[Field["g"], ___], x2___] /; (x=!=Field["g"] && FreeQ[a, "spinor"] && NoPattern[w]) := TDot[x1, b, a, x2]
w:TDot[x1___, a: NT[x_, ___], b: NT["\[Eta]", ___], x2___] /; (x=!="\[Eta]" && FreeQ[a, "spinor"] && NoPattern[w]) := TDot[x1, b, a, x2]
TDot[x1___, a:(NT|GT)[a1_, NI[a2_Integer, "spinor"]], b:(NT|GT)[b1_, NI[b2_Integer, "spinor"]], x2___] /; OrderedQ[{{b2, b1}, {a2, a1}}] := FlipSign[a, b] TDot[x1,b,a,x2]
TDot[x1___, a:(NT|GT)[a1__, NI[a2:LabelType, "spinor"], a3___], x2:RepeatedNull[_NT|_GT], b:(NT|GT)[b1__, NI[a2_, "spinor"], b3___], x3___] /; FreeQ[{a1, b3}, "spinor"] := FlipSign[a, x2, b] TDot[x1,x2,b,a,x3]
TDot[x1___, a:(NT|GT)[a1__, NI[a2:LabelType, "spinor"], a3___], x2:Repeated[_NT|_GT], b:(NT|GT)[b1__, NI[a2_, "spinor"], b3___], x3___] /; FreeQ[{a3, b1}, "spinor"] := FlipSign[a, x2] TDot[x1,x2,a,b,x3]

(* TDot simplification *)
(*
w:TDot[x1___, NT["\[Gamma]", r1:(UI|LI)[i:0|1|2|3, "lorentz"], c1:NI[LabelTypeOrI, "spinor"], c2:NI[n:LabelType, "spinor"]],
              NT["\[Gamma]", r2:(UI|LI)[j:0|1|2|3, "lorentz"], c2_, c3:NI[LabelTypeOrI, "spinor"]], x2___] /; i > j && FreeQ[{x1, x2, c1, c3}, n] && NoPattern[w] := (-1)*TDot[x1, NT["\[Gamma]", r2, c1, c2], NT["\[Gamma]", r1, c2, c3], x2]
w:TDot[x1___, NT["\[Gamma]", r1:(UI|LI)[i:0|1|2|3, "lorentz"], c1:NI[LabelTypeOrI, "spinor"], c2:NI[n:LabelType, "spinor"]],
              NT["\[Gamma]", r2:(UI|LI)[i_,        "lorentz"], c2_, c3:NI[LabelTypeOrI, "spinor"]], x2___] /; FreeQ[{x1, x2, c1, c3}, n] && NoPattern[w] := If[r1==r2, Metric[i], 1] * TDot[x1, NT["One", c1, c3], x2]
w:TDot[x1___, NT["\[Gamma]", r1:(UI|LI)[i:LabelType, "lorentz"], c1:NI[LabelTypeOrI, "spinor"], c2:NI[n:LabelType, "spinor"]],
              NT["\[Gamma]", r2:(UI|LI)[i_,          "lorentz"], c2_, c3:NI[LabelTypeOrI, "spinor"]], x2___] /; FreeQ[{x1, x2, c1, c3}, n] && NoPattern[w] := If[r1==r2, NT["\[Eta]", r1, r2], NT["\[Delta]", r1, r2]] * TDot[x1, NT["One", c1, c3], x2]
w:TDot[x1___, NT["\[Gamma]5", c1:NI[LabelTypeOrI, "spinor"], c2:NI[n:LabelType, "spinor"]],
              NT["\[Gamma]", r1:(UI|LI)[i:LabelTypeOrI, "lorentz"], c2_, c3:NI[LabelTypeOrI, "spinor"]], x2___] /; FreeQ[{x1, x2, c1, c3}, n] && NoPattern[w] := (-1)*TDot[x1, NT["\[Gamma]", r1, c1, c2], NT["\[Gamma]5", c2, c3], x2]
*)



End[];
EndPackage[];


(* ::Code:: *)
(*GT["a"]*)
(*GT["a", NI[x, "spinor"]]*)
(*GT["a", NI[x, "spinor"], NI[y, "spinor"]]*)
(*GT["a", NI[x, "spinor"]]*)
(*GT["a", NI[x, "spinor"], NI[y, "spinor"]]*)
(*GT["a", NI[x, "spinor"], NI[y, "spinor"]]*)
(*GT["a", NI[x, "spinor"], NI[y, "spinor"], NI[x, "spinor"], NI[y, "spinor"]]*)
(*TDot[GT[OverBar[\[Theta]], NI[OverDot[a], "spinor"]],GT[OverBar[\[Theta]], NI[OverDot[c], "spinor"]],  \[Sigma]b[\[Mu], a, b], \[Sigma][\[Nu], b, c]]//ReleaseHoldAll*)
(*TDot[GT[OverBar[\[Theta]], NI[OverDot[c], "spinor"]],  \[Sigma]b[\[Mu], a, b], \[Sigma][\[Nu], b, c]]//ReleaseHoldAll*)
(*TDot[GT[OverBar[\[Theta]], NI[OverDot[a], "spinor"]], \[Sigma]b[\[Mu], a, b], \[Sigma][\[Nu], b, c]]//ReleaseHoldAll*)
(*TDot[GT[OverBar[\[Theta]], NI[OverDot[a], "spinor"]],GT[\[Theta], NI[b, "spinor"]],  \[Sigma]b[\[Mu], a, b]]//ReleaseHoldAll*)
(*TDot[GT[OverBar[\[Theta]], NI[OverDot[b], "spinor"]],  \[Sigma][\[Mu], a, b]]//ReleaseHoldAll*)
(*TDot[GT[OverBar[\[Theta]], NI[OverDot[a], "spinor"]], \[Sigma]b[\[Mu], a, b]]//ReleaseHoldAll*)
