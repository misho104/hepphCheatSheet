(* ::Package:: *)

BeginPackage["WeylAlgebra`"];


ReleaseHoldAll::usage = "Removes all Hold patterns.";

NT::usage = "Normal tensor (non-Grassmannian tensor).";
GT::usage = "Grassmannian tensor.";
UI::usage = "Upper index.";
LI::usage = "Lower index.";
TDot::usage = "Dot-product of tensors.";
Field::usage = "Represents a field.";
$Contraction::usage = "Boolean configuration variable to contract spinor-indices in display or not.";

FlipSign::usage = "FlipSign[a, b, ..., z] is the sign-flip of grassmann product when A is moved to the last.";
\[Epsilon]U::usage = "Epsilon-tensor with upper indices.";
\[Epsilon]L::usage = "Epsilon-tensor with lower indices.";
\[Epsilon]Ud::usage = "Epsilon-tensor with upper dotted spinor-indices.";
\[Epsilon]Ld::usage = "Epsilon-tensor with lower dotted spinor-indices.";
\[Eta]U::usage = "Minkowski metric \[Eta] with upper indices.";
\[Eta]L::usage = "Minkowski metric \[Eta] with lower indices.";
\[Sigma]::usage = "Sigma metric in Weyl representation.";
\[Sigma]b::usage = "Sigma-bar metric in Weyl representation.";
\[Sigma]Upper::usage = "Sigma metric in Weyl representation but spinor-indices are forced upper.";
\[Sigma]bLower::usage = "Sigma-bar metric in Weyl representation but spinor-indices are forced lower.";
\[Delta]::usage = "Kronecker-delta.";
\[Delta]d::usage = "Kronecker-delta with dotted spinor-indices.";

PutOverDot::usage = "Put an overdot to the index if missing.";
SwitchOverDot::usage = "Alternate OverDot of the index.";

FillIndices::usage = "FillIndices evaluates the Einstein summation of specified types.";
SumIndex::usage = "SumIndex calculates the sum over specified index.";
Tablize::usage = "Tablize generates a table over the specified index.";
MakeBoxesNT::usage = "hoge";


Begin["`Private`"];

System`Convert`CommonDump`templateBoxToDisplay = BoxForm`TemplateBoxToDisplayBoxes;

(* Object definition in BNF *)
LabelType = _Symbol | _String;
SpinorLabelType = LabelType | OverDot[LabelType];

LabelTypeOrI = LabelType | _Integer;
SpinorLabelTypeOrI = LabelTypeOrI | OverDot[LabelTypeOrI];

IndexClassType = _String;
UpperIndexType = UI[SpinorLabelTypeOrI, IndexClassType];
LowerIndexType = LI[SpinorLabelTypeOrI, IndexClassType];
IndexType = (UI|LI)[SpinorLabelTypeOrI, IndexClassType];

NameType = _Symbol | _String | _Field;

NormalTensorType = NT[NameType | OverBar[NameType], RepeatedNull[IndexType]];
GrassmannTensorType = GT[NameType | OverBar[NameType], RepeatedNull[IndexType]];
TensorType = NormalTensorType | GrassmannTensorType;

(* Format *)
Sequence[GT, NameType | OverBar[NameType] | _Row, RepeatedNull[IndexType]] // (#1 /: MakeBoxes[obj: #1[n:#2|HoldForm[#2], i:#3], f:StandardForm|TraditionalForm] := MakeBoxesNT[f, Style[#, Red]&, n, i] // ToBoxes // InterpretationBox[#,obj] &) &;
Sequence[NT, NameType | OverBar[NameType] | _Row, RepeatedNull[IndexType]] // (#1 /: MakeBoxes[obj: #1[n:#2|HoldForm[#2], i:#3], f:StandardForm|TraditionalForm] := MakeBoxesNT[f, #&, n, i] // ToBoxes // InterpretationBox[#,obj] &) &;
MakeBoxesNT$[f_, c_, n_] := c[n];
MakeBoxesNT$[f_, c_, n_, UI[a:SpinorLabelTypeOrI, _]] := Superscript[c[n], a]
MakeBoxesNT$[f_, c_, n_, LI[a:SpinorLabelTypeOrI, _]] := Subscript[c[n], a]
MakeBoxesNT$[f_, c_, n_, a:Repeated[_UI]] := Row[{a}[[All, 1]]] // Superscript[c[n], #]&
MakeBoxesNT$[f_, c_, n_, a:Repeated[_LI]] := Row[{a}[[All, 1]]] // Subscript[c[n], #]&
MakeBoxesNT$[f_, c_, n_, any__, a:Repeated[_UI]] := Row[{MakeBoxesNT$[f, c, n, any], MakeBoxesNT$[f, c, "", a]}]
MakeBoxesNT$[f_, c_, n_, any__, a:Repeated[_LI]] := Row[{MakeBoxesNT$[f, c, n, any], MakeBoxesNT$[f, c, "", a]}]
MakeBoxesNT = MakeBoxesNT$; (* for extensions *)

TDot /: MakeBoxes[obj: TDot[a__], f:StandardForm] := Dot[TDotPreFormat[a]] // ToBoxes // InterpretationBox[#,obj] &
TDot /: MakeBoxes[obj: TDot[a__], f:TraditionalForm] := Row[{TDotPreFormat[a]}] // ToBoxes // InterpretationBox[#,obj] &

TDotPreFormat$Target = ("\[Sigma]"|OverBar["\[Sigma]"]|"\[Epsilon]"|HoldForm["\[Sigma]"]|HoldForm[OverBar["\[Sigma]"]]|HoldForm["\[Epsilon]"]);
TDotPreFormat$SpinorRow[{a_, GT[{b__}]}, s___] := TDotPreFormat$SpinorRow[{a, b}, s]
TDotPreFormat$SpinorRow[{GT[{a__}], b_}, s___] := TDotPreFormat$SpinorRow[{a, b}, s]
TDotPreFormat$[seq___] := Module[{objs = {seq}},
  objs = objs //. {List[
    x1___,
    GT[a1:NameType, a2___, UI[a4:LabelType, "spinor"]],
    GT[b1:NameType, LI[a4_, "spinor"]] | TDotPreFormat$SpinorRow[b1_, LI[a4_, "spinor"]],
    x2___
  ] /; FreeQ[{a2}, "spinor"] :> List[x1, TDotPreFormat$SpinorRow[{GT[a1, a2], GT[b1]}], x2], List[
    x1___,
    GT[a1:OverBar[NameType], a2___, LI[a4:OverDot[LabelType], "spinor"]],
    GT[b1:OverBar[NameType], UI[a4_, "spinor"]] | TDotPreFormat$SpinorRow[b1_, UI[a4_, "spinor"]],
    x2___
  ] /; FreeQ[{a2}, "spinor"] :> List[x1, TDotPreFormat$SpinorRow[{GT[a1, a2], GT[b1]}], x2], List[
    x1___,
    NT[a1:TDotPreFormat$Target, a2___, a3:(UI|LI)[SpinorLabelTypeOrI, "spinor"], UI[a4:LabelType, "spinor"]],
    GT[b1:NameType, LI[a4_, "spinor"]] | TDotPreFormat$SpinorRow[b1_, LI[a4_, "spinor"]],
    x2___
  ] /; FreeQ[{a2}, "spinor"] :> List[x1, TDotPreFormat$SpinorRow[{NT[a1, a2], GT[b1]}, a3], x2], List[
    x1___,
    NT[a1:TDotPreFormat$Target, a2___, a3:(UI|LI)[SpinorLabelTypeOrI, "spinor"], LI[a4:OverDot[LabelType], "spinor"]],
    GT[b1:(OverBar[NameType]), UI[a4_, "spinor"]] | TDotPreFormat$SpinorRow[b1_, UI[a4_, "spinor"]],
    x2___
  ] /; FreeQ[{a2}, "spinor"] :> List[x1, TDotPreFormat$SpinorRow[{NT[a1, a2], GT[b1]}, a3], x2], List[
    x1___,
    GT[b1:NameType, UI[a3:LabelType, "spinor"]] | TDotPreFormat$SpinorRow[b1_, UI[a3:LabelType, "spinor"]],
    NT[a1:TDotPreFormat$Target, a2___, LI[a3_, "spinor"], a4:(UI|LI)[SpinorLabelTypeOrI, "spinor"]],
    x2___
  ] /; FreeQ[{a2}, "spinor"] :> List[x1, TDotPreFormat$SpinorRow[{GT[b1], NT[a1, a2]}, a4], x2], List[
    x1___,
    GT[b1:(OverBar[NameType]), LI[a3:OverDot[LabelType], "spinor"]] | TDotPreFormat$SpinorRow[b1_, LI[a3:OverDot[LabelType], "spinor"]],
    NT[a1:TDotPreFormat$Target, a2___, UI[a3_, "spinor"], a4:(UI|LI)[SpinorLabelTypeOrI, "spinor"]],
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
  "spinor", {1, 2},
  "any", Message[IndexIter::any]; Abort[],
  _, Abort[]];

PutOverDot[a:SpinorLabelTypeOrI] := If[Head[a]===OverDot, a, OverDot[a]];
SwitchOverDot[a:SpinorLabelTypeOrI] := If[Head[a]===OverDot, a[[1]], OverDot[a]];
SwitchOverDot[a:_NT|_GT] := a/. {(x:UI|LI)[y:SpinorLabelTypeOrI, "spinor"] :> x[SwitchOverDot[y], "spinor"]}

(* spinor index moves last *)
NT[x__, a:((UI|LI)[_, "spinor"]), b:((UI|LI)[_, type_]), y___] /; type =!= "spinor" := NT[x, b, a] 
GT[x__, a:((UI|LI)[_, "spinor"]), b:((UI|LI)[_, type_]), y___] /; type =!= "spinor" := GT[x, b, a] 


(* Conjugate Operation is "defined" For (single) Grassmann-type tensor. *)
GT /: Conjugate[GT[OverBar[a:NameType], b:RepeatedNull[IndexType]]] := SwitchOverDot[GT[a, b]]
GT /: Conjugate[GT[a:NameType, b:RepeatedNull[IndexType]]] := SwitchOverDot[GT[OverBar[a], b]]
TDot /: Conjugate[TDot[a___]] := TDot@@(Reverse[Conjugate/@{a}])


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


(* Epsilon-contraction rule: Always from left *)
GT /: TDot[x1___, NT["\[Epsilon]", UI[a:SpinorLabelType, "spinor"], UI[b:SpinorLabelType, "spinor"]], x2___, GT[n___, LI[b_, "spinor"]], x3___] /; FreeQ[{n}, "spinor"] := TDot[x1, x2, GT[n, UI[a, "spinor"]], x3]
GT /: TDot[x1___, NT["\[Epsilon]", LI[a:SpinorLabelType, "spinor"], LI[b:SpinorLabelType, "spinor"]], x2___, GT[n___, UI[b_, "spinor"]], x3___] /; FreeQ[{n}, "spinor"] := TDot[x1, x2, GT[n, LI[a, "spinor"]], x3]
GT /: TDot[x1___, NT["\[Epsilon]", UI[b:SpinorLabelType, "spinor"], UI[a:SpinorLabelType, "spinor"]], x2___, GT[n___, LI[b_, "spinor"]], x3___] /; FreeQ[{n}, "spinor"] := (-1)TDot[x1, x2, GT[n, UI[a, "spinor"]], x3]
GT /: TDot[x1___, NT["\[Epsilon]", LI[b:SpinorLabelType, "spinor"], LI[a:SpinorLabelType, "spinor"]], x2___, GT[n___, UI[b_, "spinor"]], x3___] /; FreeQ[{n}, "spinor"] := (-1)TDot[x1, x2, GT[n, LI[a, "spinor"]], x3]
GT /: TDot[x1___, GT[n___, LI[b_, "spinor"]], x2___, NT["\[Epsilon]", UI[a:SpinorLabelType, "spinor"], UI[b:SpinorLabelType, "spinor"]], x3___] /; FreeQ[{n}, "spinor"] := TDot[x1, GT[n, UI[a, "spinor"]], x2, x3]
GT /: TDot[x1___, GT[n___, UI[b_, "spinor"]], x2___, NT["\[Epsilon]", LI[a:SpinorLabelType, "spinor"], LI[b:SpinorLabelType, "spinor"]], x3___] /; FreeQ[{n}, "spinor"] := TDot[x1, GT[n, LI[a, "spinor"]], x2, x3]
GT /: TDot[x1___, GT[n___, LI[b_, "spinor"]], x2___, NT["\[Epsilon]", UI[b:SpinorLabelType, "spinor"], UI[a:SpinorLabelType, "spinor"]], x3___] /; FreeQ[{n}, "spinor"] := (-1) TDot[x1, GT[n, UI[a, "spinor"]], x2, x3]
GT /: TDot[x1___, GT[n___, UI[b_, "spinor"]], x2___, NT["\[Epsilon]", LI[b:SpinorLabelType, "spinor"], LI[a:SpinorLabelType, "spinor"]], x3___] /; FreeQ[{n}, "spinor"] := (-1) TDot[x1, GT[n, LI[a, "spinor"]], x2, x3]

(* Bare-indiced spinors are forced to upper. *)
GT[n___, LI[a:_Integer, "spinor"]] /; FreeQ[{n}, "spinor"] := Sum[\[Epsilon]L[a,b]GT[n, UI[b, "spinor"]]//ReleaseHold, {b, 2}];
GT[n___, LI[a:OverDot[_Integer], "spinor"]] /; FreeQ[{n}, "spinor"] := Sum[\[Epsilon]Ld[a,b]GT[n, UI[OverDot[b], "spinor"]]//ReleaseHold, {b, 2}] ;


(* TDot order: spinors, \[Eta], non-spinors *)
TDot[x1___, a:(_NT|_GT), b:(NT|GT)[___, (LI|UI)[_, "spinor"], ___], x2___] /; FreeQ[a, "spinor"] := FlipSign[a, b]*TDot[x1, b, a, x2]
TDot[x1___, a: NT[x_, ___], b: NT["\[Eta]", ___], x2___] /; (x=!="\[Eta]" && FreeQ[a, "spinor"]) := TDot[x1, b, a, x2]
TDot[x1___, a:(NT|GT)[a1__, LI[a2:LabelType, "spinor"], a3___], x2___, b:(NT|GT)[b1__, UI[a2_, "spinor"], b3___], x3___] /; FreeQ[{a1, b3}, "spinor"] := FlipSign[a, x2, b] TDot[x1,x2,b,a,x3]
TDot[x1___, a:(NT|GT)[a1__, UI[a2:OverDot[LabelType], "spinor"], a3___], x2___, b:(NT|GT)[b1__, LI[a2_, "spinor"], b3___], x3___] /; (FreeQ[{a1, b3}, "spinor"] && DuplicateFreeQ[Cases[{a3, b1}, (UI|LI)[s_, "spinor"]:>s]]):= FlipSign[a, x2, b] TDot[x1,x2,b,a,x3]
TDot[x1___, a:(NT|GT)[a1__, UI[a2:LabelType, "spinor"], a3___], x2__, b:(NT|GT)[b1__, LI[a2_, "spinor"], b3___], x3___] /; FreeQ[{a3, b1}, "spinor"] := FlipSign[a, x2] TDot[x1,x2,a,b,x3]
TDot[x1___, a:(NT|GT)[a1__, LI[a2:OverDot[LabelType], "spinor"], a3___], x2__, b:(NT|GT)[b1__, UI[a2_, "spinor"], b3___], x3___] /; (FreeQ[{a3, b1}, "spinor"] && DuplicateFreeQ[Cases[{a1, b3}, (UI|LI)[s_, "spinor"]:>s]]) := FlipSign[a, x2] TDot[x1,x2,a,b,x3]

(* TDot order: integer-indexed spinors *)
TDot[x1___, a:GT[_, (UI|LI)[_Integer|OverDot[_Integer], "spinor"]], x2___, b:GT[_, (UI|LI)[_Integer|OverDot[_Integer], "spinor"]], x3___]/; Not[OrderedQ[{a,b}]] := FlipSign[a, x2, b] TDot[x1,x2,b,a,x3]

(* Eta-contraction rule *)
TDot[x1___, NT["\[Eta]", UI[a:LabelTypeOrI, "lorentz"], UI[b:LabelType, "lorentz"]], x2___, (n:GT|NT)[n1___, LI[b_, "lorentz"], n2___], x3___] := TDot[x1, x2, n[n1, UI[a, "lorentz"], n2], x3]
TDot[x1___, NT["\[Eta]", LI[a:LabelTypeOrI, "lorentz"], LI[b:LabelType, "lorentz"]], x2___, (n:GT|NT)[n1___, UI[b_, "lorentz"], n2___], x3___] := TDot[x1, x2, n[n1, LI[a, "lorentz"], n2], x3]
TDot[x1___, (n:GT|NT)[n1___, LI[b_, "lorentz"], n2___], x2___, NT["\[Eta]", UI[a:LabelTypeOrI, "lorentz"], UI[b:LabelType, "lorentz"]], x3___] := TDot[x1, x2, n[n1, UI[a, "lorentz"], n2], x3]
TDot[x1___, (n:GT|NT)[n1___, UI[b_, "lorentz"], n2___], x2___, NT["\[Eta]", LI[a:LabelTypeOrI, "lorentz"], LI[b:LabelType, "lorentz"]], x3___] := TDot[x1, x2, n[n1, LI[a, "lorentz"], n2], x3]

(* Kronecker Delta: UI is in front of LI. *)
NT["\[Delta]", a:LI[SpinorLabelTypeOrI, IndexClassType], b:UI[SpinorLabelTypeOrI, IndexClassType]] := NT["\[Delta]", b, a]
TDot[x1___, NT["\[Delta]", UI[a:SpinorLabelTypeOrI, c:IndexClassType|"any"], LI[b:SpinorLabelType, c:IndexClassType|"any"]], x2___, (n:GT|NT)[n1___, UI[b_, c_], n2___], x3___] := TDot[x1, x2, n[n1, UI[a, c], n2], x3]
TDot[x1___, NT["\[Delta]", UI[a:SpinorLabelType, c:IndexClassType|"any"], LI[b:SpinorLabelTypeOrI, c:IndexClassType|"any"]], x2___, (n:GT|NT)[n1___, LI[a_, c_], n2___], x3___] := TDot[x1, x2, n[n1, LI[b, c], n2], x3]
TDot[x1___, (n:GT|NT)[n1___, UI[b_, c_], n2___], x2___, NT["\[Delta]", UI[a:SpinorLabelTypeOrI, c:IndexClassType|"any"], LI[b:SpinorLabelType, c:IndexClassType|"any"]], x3___] := TDot[x1, n[n1, UI[a, c], n2], x2, x3]
TDot[x1___, (n:GT|NT)[n1___, LI[a_, c_], n2___], x2___, NT["\[Delta]", UI[a:SpinorLabelType, c:IndexClassType|"any"], LI[b:SpinorLabelTypeOrI, c:IndexClassType|"any"]], x3___] := TDot[x1, n[n1, LI[b, c], n2], x2, x3]
NT["\[Eta]", f:OrderlessPatternSequence[LI[a:LabelTypeOrI, "lorentz"], UI[b:LabelTypeOrI, "lorentz"]]] := NT["\[Delta]", f]


(* Objects *)
\[Epsilon]U[a_, b_] := NT[HoldForm["\[Epsilon]"], UI[a, "spinor"], UI[b, "spinor"]]
\[Epsilon]L[a_, b_] := NT[HoldForm["\[Epsilon]"], LI[a, "spinor"], LI[b, "spinor"]]
\[Epsilon]Ud[a_, b_] := NT[HoldForm["\[Epsilon]"], UI[PutOverDot[a], "spinor"], UI[PutOverDot[b], "spinor"]]
\[Epsilon]Ld[a_, b_] := NT[HoldForm["\[Epsilon]"], LI[PutOverDot[a], "spinor"], LI[PutOverDot[b], "spinor"]]

\[Epsilon]U[a_, b_, c_, d_] := NT[HoldForm["\[Epsilon]"], UI[a, "lorentz"], UI[b, "lorentz"], UI[c, "lorentz"], UI[d, "lorentz"]]
\[Epsilon]L[a_, b_, c_, d_] := NT[HoldForm["\[Epsilon]"], LI[a, "lorentz"], LI[b, "lorentz"], LI[c, "lorentz"], LI[d, "lorentz"]]

NT["\[Epsilon]", ___, a_, ___, a_, ___] := 0
NT["\[Epsilon]", x___, pos_[a_, type_], pos_[b_, type_], y___] /; Not[OrderedQ[{a, b}]] := (-1) NT["\[Epsilon]", x, pos[b, type], pos[a, type], y]
NT["\[Epsilon]", UI[1, "spinor"], UI[2, "spinor"]] := +1
NT["\[Epsilon]", LI[1, "spinor"], LI[2, "spinor"]] := -1 (* beware! *)
NT["\[Epsilon]", UI[OverDot[1], "spinor"], UI[OverDot[2], "spinor"]] := +1
NT["\[Epsilon]", LI[OverDot[1], "spinor"], LI[OverDot[2], "spinor"]] := -1 (* beware! *)

NT["\[Epsilon]", UI[0, "lorentz"], UI[1, "lorentz"], UI[2, "lorentz"], UI[3, "lorentz"]] := +1
NT["\[Epsilon]", LI[0, "lorentz"], LI[1, "lorentz"], LI[2, "lorentz"], LI[3, "lorentz"]] := -1 (* beware! *)

\[Eta]U[\[Mu]_, \[Nu]_] := NT[HoldForm["\[Eta]"], UI[\[Mu], "lorentz"], UI[\[Nu], "lorentz"]]
\[Eta]L[\[Mu]_, \[Nu]_] := NT[HoldForm["\[Eta]"], LI[\[Mu], "lorentz"], LI[\[Nu], "lorentz"]]

\[Sigma][\[Mu]_, a_, b_]        := NT[HoldForm["\[Sigma]"], UI[\[Mu], "lorentz"], LI[a, "spinor"], LI[PutOverDot[b], "spinor"]]
\[Sigma][Null,\[Mu]_, a_, b_]       := NT[HoldForm["\[Sigma]"], LI[\[Mu], "lorentz"], LI[a, "spinor"], LI[PutOverDot[b], "spinor"]]
\[Sigma]Upper[\[Mu]_, a_, b_]   := NT[HoldForm["\[Sigma]"], UI[\[Mu], "lorentz"], UI[a, "spinor"], UI[PutOverDot[b], "spinor"]]
\[Sigma]Upper[Null,\[Mu]_, a_, b_]  := NT[HoldForm["\[Sigma]"], LI[\[Mu], "lorentz"], UI[a, "spinor"], UI[PutOverDot[b], "spinor"]]
\[Sigma]b[\[Mu]_, a_, b_]       := NT[HoldForm[OverBar["\[Sigma]"]], UI[\[Mu], "lorentz"], UI[PutOverDot[a], "spinor"], UI[b, "spinor"]]
\[Sigma]b[Null,\[Mu]_, a_, b_]      := NT[HoldForm[OverBar["\[Sigma]"]], LI[\[Mu], "lorentz"], UI[PutOverDot[a], "spinor"], UI[b, "spinor"]]
\[Sigma]bLower[\[Mu]_, a_, b_]   := NT[HoldForm[OverBar["\[Sigma]"]], UI[\[Mu], "lorentz"], LI[PutOverDot[a], "spinor"], LI[b, "spinor"]]
\[Sigma]bLower[Null,\[Mu]_, a_, b_]  := NT[HoldForm[OverBar["\[Sigma]"]], LI[\[Mu], "lorentz"], LI[PutOverDot[a], "spinor"], LI[b, "spinor"]]

\[Sigma][\[Mu]_, \[Nu]_, a_, b_]   := NT[HoldForm["\[Sigma]"], UI[\[Mu], "lorentz"], UI[\[Nu], "lorentz"], LI[a, "spinor"], UI[b, "spinor"]]
\[Sigma][Null,\[Mu]_, \[Nu]_, a_, b_]  := NT[HoldForm["\[Sigma]"], LI[\[Mu], "lorentz"], LI[\[Nu], "lorentz"], LI[a, "spinor"], UI[b, "spinor"]]
\[Sigma]b[\[Mu]_, \[Nu]_, a_, b_]  := NT[HoldForm[OverBar["\[Sigma]"]], UI[\[Mu], "lorentz"], UI[\[Nu], "lorentz"], UI[PutOverDot[a], "spinor"], LI[PutOverDot[b], "spinor"]]
\[Sigma]b[Null,\[Mu]_, \[Nu]_, a_, b_] := NT[HoldForm[OverBar["\[Sigma]"]], LI[\[Mu], "lorentz"], LI[\[Nu], "lorentz"], UI[PutOverDot[a], "spinor"], LI[PutOverDot[b], "spinor"]]

\[Delta][a_, b_, class:IndexClassType] := NT[HoldForm["\[Delta]"], UI[a, class], LI[b, class]];
\[Delta][a_, b_] := \[Delta][a, b, "any"];
\[Delta]d[a_, b_, class:"spinor"] := NT[HoldForm["\[Delta]"], UI[PutOverDot[a], class], LI[PutOverDot[b], class]];
\[Delta]d[a_, b_] := \[Delta]d[a, b, "spinor"];


(* definitions *)
NT["\[Delta]", UI[a_Integer, (cls:IndexClassType)|"any"], LI[a_, (cls_)|"any"]] := 1
NT["\[Delta]", UI[OverDot[a_Integer], (cls:IndexClassType)|"any"], LI[OverDot[a_], (cls_)|"any"]] := 1

NT["\[Delta]", UI[a:LabelTypeOrI, (cls:IndexClassType)|"any"], LI[b:LabelTypeOrI, (cls_)|"any"]] /; a!=b := 0
NT["\[Delta]", UI[OverDot[a:LabelTypeOrI], (cls:IndexClassType)|"any"], LI[OverDot[b:LabelTypeOrI], (cls_)|"any"]] /; a!=b := 0

NT["\[Delta]", x:UI[a:LabelType, cls:IndexClassType], y:LI[a_, cls_]] := Sum[NT["\[Delta]", x, y], {a, IndexIter[cls]}]
NT["\[Delta]", UI[OverDot[a:LabelType], cls:IndexClassType], LI[OverDot[a_], cls_]] := Sum[NT["\[Delta]", x, y], {a, IndexIter[cls]}]

NT["\[Eta]", UI[\[Mu]:0|1|2|3, "lorentz"], UI[\[Nu]:0|1|2|3, "lorentz"]] := Which[\[Mu]!=\[Nu], 0, \[Mu]==\[Nu]==0, 1, True, -1]
NT["\[Eta]", LI[\[Mu]:0|1|2|3, "lorentz"], LI[\[Nu]:0|1|2|3, "lorentz"]] := Which[\[Mu]!=\[Nu], 0, \[Mu]==\[Nu]==0, 1, True, -1]
NT["\[Sigma]", UI[\[Mu]:0|1|2|3, "lorentz"], LI[a:1|2, "spinor"], LI[OverDot[b:1|2], "spinor"]] := PauliMatrix[\[Mu]][[a,b]]

NT[OverBar["\[Sigma]"], UI[\[Mu]:0|1|2|3, "lorentz"], UI[OverDot[a:1|2], "spinor"], UI[b:1|2, "spinor"]] := If[\[Mu]==0, +1, -1] * PauliMatrix[\[Mu]][[a,b]]
NT[sigma:("\[Sigma]"|OverBar["\[Sigma]"]), x___, LI[\[Mu]:0|1|2|3, "lorentz"], y___] := \[Eta]L[\[Mu],\[Mu]] * NT[sigma, x, UI[\[Mu], "lorentz"], y]
NT["\[Sigma]", UI[\[Mu]_, "lorentz"], UI[\[Nu]_, "lorentz"], LI[a_, "spinor"], UI[b_, "spinor"]] := Module[{c=OverDot[Unique[]], result},
  result = (I/4)*(\[Sigma][\[Mu],a,c]\[Sigma]b[\[Nu],c,b] - \[Sigma][\[Nu],a,c]\[Sigma]b[\[Mu],c,b]);
  If[IntegerQ[\[Mu]] && IntegerQ[\[Nu]] && (IntegerQ[a] || IntegerQ[b]), SumIndex[result, {c, "spinor"}], result]]
NT[OverBar["\[Sigma]"], UI[\[Mu]_, "lorentz"], UI[\[Nu]_, "lorentz"], UI[OverDot[a_], "spinor"], LI[OverDot[b_], "spinor"]] := Module[{c=Unique[], result},
  result = (I/4)*(\[Sigma]b[\[Mu],a,c]\[Sigma][\[Nu],c,b] - \[Sigma]b[\[Nu],a,c]\[Sigma][\[Mu],c,b]);
  If[IntegerQ[\[Mu]] && IntegerQ[\[Nu]] && (IntegerQ[a] || IntegerQ[b]), SumIndex[result, {c, "spinor"}], result]]

(* irregular sigma position *)
NT["\[Sigma]", lor_, UI[a_, "spinor"], UI[b_, "spinor"]] := Module[{c=Unique[], d=OverDot[Unique[]]},
  \[Epsilon]U[a,c]*\[Epsilon]Ud[b,d]*NT["\[Sigma]", lor, LI[c, "spinor"], LI[d, "spinor"]]]
NT[OverBar["\[Sigma]"], lor_, LI[a_, "spinor"], LI[b_, "spinor"]] := Module[{c=OverDot[Unique[]], d=Unique[]},
  \[Epsilon]Ld[a,c]*\[Epsilon]L[b,d]*NT[OverBar["\[Sigma]"], lor, UI[c, "spinor"], UI[d, "spinor"]]]

(* special rule for epsilons*)
NT["\[Epsilon]", whole:OrderlessPatternSequence[UI[a:_Integer|OverDot[_Integer], "spinor"], UI[b:SpinorLabelType, "spinor"]]] := Module[{c=Unique[], tmp, putdot},
  putdot = If[Head[b]===OverDot, PutOverDot, #&];
  tmp = (NT[HoldForm["\[Epsilon]"], whole] /. b->putdot[c]) \[Delta][b,putdot[c],"spinor"];
  Sum[tmp, {c, 2}//Evaluate]//ReleaseHold]
NT["\[Epsilon]", whole:OrderlessPatternSequence[LI[a:_Integer|OverDot[_Integer], "spinor"], LI[b:SpinorLabelType, "spinor"]]] := Module[{c=Unique[], tmp, putdot},
  putdot = If[Head[b]===OverDot, PutOverDot, #&];
  tmp = (NT[HoldForm["\[Epsilon]"], whole] /. b->putdot[c]) \[Delta][putdot[c],b,"spinor"];
  Sum[tmp, {c, 2}//Evaluate]//ReleaseHold]


TDot::InvalidIndices = "Invalid indices in `1`.";

FindIndices[a:TDot[RepeatedNull[TensorType]]] := Cases[a, _UI|_LI, 2] // Select[FreeQ[#[[1]], _Integer]&]

FindUniqueIndices[a:TDot[RepeatedNull[TensorType]]] := Cases[CountsBy[FindIndices[a], #[[1]]&] /. Association->List, Rule[p_,1]:>p]
  
FindIndicesToContract[a:TDot[RepeatedNull[TensorType]]] := Module[{i=GroupBy[FindIndices[a], Head], upper, lower},
  upper = Lookup[i, UI, {}];
  lower = Lookup[i, LI, {}];
  If[Intersection[upper, lower]=!={}, Message[TDot::InvalidIndices, a]; Print[3,i]; Abort[]];
  If[Not[DuplicateFreeQ[upper]], Message[TDot::InvalidIndices, a]; Print[i]; Abort[]];
  If[Not[DuplicateFreeQ[lower]], Message[TDot::InvalidIndices, a]; Print[i, i];Abort[]];
  Intersection[(List@@#)&/@upper, (List@@#)&/@lower]]

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
  If[Head[symbol]===OverDot,
    (* overdot summation *)
    iter = OverDot/@iter;
    result = Sum[exp, {symbol, iter}//Evaluate],
    (* non-dot summation; escape dotted indices *)
    i = Unique[];
    result = exp //. OverDot[symbol] -> i;
    result = Sum[result, {symbol, iter}//Evaluate];
    result = result //. i -> OverDot[symbol]];
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


End[];
EndPackage[];


(* ::Code:: *)
(*GT["a"]*)
(*GT["a", UI[x, "spinor"]]*)
(*GT["a", UI[x, "spinor"], UI[y, "spinor"]]*)
(*GT["a", LI[x, "spinor"]]*)
(*GT["a", LI[x, "spinor"], UI[y, "spinor"]]*)
(*GT["a", LI[x, "spinor"], LI[y, "spinor"]]*)
(*GT["a", UI[x, "spinor"], UI[y, "spinor"], UI[x, "spinor"], LI[y, "spinor"]]*)
(*TDot[GT[OverBar[\[Theta]], LI[OverDot[a], "spinor"]],GT[OverBar[\[Theta]], UI[OverDot[c], "spinor"]],  \[Sigma]b[\[Mu], a, b], \[Sigma][\[Nu], b, c]]//ReleaseHoldAll*)
(*TDot[GT[OverBar[\[Theta]], UI[OverDot[c], "spinor"]],  \[Sigma]b[\[Mu], a, b], \[Sigma][\[Nu], b, c]]//ReleaseHoldAll*)
(*TDot[GT[OverBar[\[Theta]], LI[OverDot[a], "spinor"]], \[Sigma]b[\[Mu], a, b], \[Sigma][\[Nu], b, c]]//ReleaseHoldAll*)
(*TDot[GT[OverBar[\[Theta]], LI[OverDot[a], "spinor"]],GT[\[Theta], LI[b, "spinor"]],  \[Sigma]b[\[Mu], a, b]]//ReleaseHoldAll*)
(*TDot[GT[OverBar[\[Theta]], UI[OverDot[b], "spinor"]],  \[Sigma][\[Mu], a, b]]//ReleaseHoldAll*)
(*TDot[GT[OverBar[\[Theta]], LI[OverDot[a], "spinor"]], \[Sigma]b[\[Mu], a, b]]//ReleaseHoldAll*)
