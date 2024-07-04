(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["Wolfram`Class`"];


(* ::Text:: *)
(*Declare your public symbols here:*)


InheritDefinitions;
Class;
PropertyMethod;
StaticMethod;
ClassMethod;


Begin["`Private`"];


(* ::Section:: *)
(*Definitions*)


(* ::Text:: *)
(*Define your public and private symbols here:*)


ClearAll[TraceSteps, DelayedDefinition, DelayedBlock, ParallelDelayedBlock]
SetAttributes[{TraceSteps, DelayedDefinition, DelayedBlock, ParallelDelayedBlock}, HoldAll]

TraceSteps[expr_, steps_Integer : 1, opts : OptionsPattern[TraceScan]] := Block[{count = 0, res},
	res = TraceScan[
		If[ count >= steps,
			Return[#, TraceScan],
			count++;
		] &,
		expr,
		opts,
		TraceDepth -> 1
	];
	If[res === Unevaluated[expr], HoldForm[expr], res]
]

DelayedDefinition[vars_, expr_, steps_Integer : 1, opts : OptionsPattern[TraceSteps]] := Block[{count = 0, withExpr, blockExpr},
	withExpr = TraceSteps[expr, steps, opts];
	blockExpr = With[vars, Evaluate[withExpr]];
	blockExpr
]

DelayedBlock[a_, b_, expr_, args___] := Module[{c}, With[{tmp = DelayedDefinition[{a = c}, expr, args]},
	If[ (* unevaluated *)
		tmp === {} || tmp === (HoldForm[expr] /. HoldPattern[a] :> c),
		expr,
		(* recurse with default arguments *)
		Function[Null, DelayedBlock[a, b, #], HoldAll] @@ (tmp /. c :> b)
	]
]]

(* Evaluate on a parallel kernel, otherwise Trace doesn't work inside MakeBoxes for some mysterious reason *)
ParallelDelayedBlock[a_, b_, args___] := Enclose @ ParallelEvaluate[
	DelayedBlock[a, b, args],
	ConfirmMatch[First[Kernels[], First @ LaunchKernels[1, ProgressReporting -> None]], _KernelObject],
	DistributedContexts -> Automatic
]


ClearAll[InheritDefinitions, $Children, $Parent]
SetAttributes[{InheritDefinitions, $Children, $Parent, RootParent, AllChildren, ParentTest, ParentType}, HoldAll]

$UpValueHack = False;

$Children[_] := Hold[]
$Parent[_] := None

AllChildren[x_] := Flatten[Replace[$Children[x], y_ :> RuleCondition[Prepend[AllChildren[y], y]], {1}], 1, Hold]
RootParent[x_] := RootParent[x] = With[{parent = $Parent[x]}, If[parent === None || Hold[x] === parent, Hold[x], RootParent @@ parent]]
ParentTest[x_][y_] := With[{parent = $Parent[y]}, parent =!= None && (parent === Hold[x] || Function[Null, ParentTest[x][Unevaluated[#]], HoldAll] @@ parent)]
ParentType[x_] := _ ? (ParentTest[x])

MissingUnion[list_List] := Union @@ Replace[list, _Missing -> {}, {1}]

InheritDefinitions[a_ ? Developer`SymbolQ, b_ ? Developer`SymbolQ] := (

	(* Track children and parents *)
	$Children[a] = Union[$Children[a], Hold[b]];
	$Parent[b] = Hold[a];

	(* Inherit DownValues and SubValues *)
	b[args___] := DelayedBlock[a, b, a[args]];

	(* Inherit FormatValues. Needs TraceInternal and one more step to go deeper *)
	MakeBoxes[b, form___] ^:= ParallelDelayedBlock[a, b, MakeBoxes[a, form], 2, TraceInternal -> True, TraceDepth -> Infinity];

	(* NValues is also tricky as it evaluates its arguments *)
	N[b, args___] :=
		DelayedBlock[a, b, N[a, args], Evaluate[3 + Length[{args}]], TraceInternal -> True, TraceDepth -> Infinity];

	(* Inherit Messages *)
	AppendTo[Messages[b], HoldPattern[MessageName[b, tag_]] :> With[{msg = MessageName[a, tag]}, msg /; StringQ[msg]]];

	(* Inherit DefaultValues *)
	DefaultValues[b] = {
		(* arguments for default like Default[b, 2] doesn't work because of a bug *)
		HoldPattern[Default[b, args___]] :> Default[a, args],
		HoldPattern[Options[b, args___]] :> Options[a, args]
	};

	(* Inherit UpValues with pattern variable substitution (disabled by default) *)
	If[ $UpValueHack,
		expr : _[___, b, ___] /; $UpValueHack ^:= Block[{$UpValueHack = False, ret, cond},
			{ret, cond} = Block[{def, rule, upvalues,
				root = RootParent[b],
				type
			},
				If[ root === None, {Null, False},
					type = Alternatives @@@ HoldPattern[Evaluate[DeleteDuplicates @ Join[root, AllChildren @@ root]]];
					upvalues = Join @@ UpValues @@@ Cases[FixedPointList[Apply[$Parent], Hold[b]], _Hold];
					(*If[head === f, EchoFunction[InputForm]@{type, upvalues}];*)
					upvalues = MapAt[
						Replace[
							#,
							{
								Verbatim[Pattern][p_, c : Evaluate[type]] :> RuleCondition[Pattern @@ Hold[p, ParentType[c]]],
								c : Evaluate[type] :> _ ? (ParentTest[c])
							},
							{2}
						] &,
						upvalues,
						{All, 1}
					];
					def = SelectFirst[upvalues, MatchQ[Unevaluated[expr], #[[1]]] &];

					If[ MissingQ[def],
						{Null, False},
						Replace[def, (lhs_ :> rhs_) :> With[{
							newRhs = Unevaluated[Unevaluated[rhs]] /. HoldPattern[a] :> b
						},
							rule = RuleDelayed @@ Unevaluated @ {
								lhs,
								Block[{$UpValueHack = True}, DelayedBlock[a, b, newRhs]]};
							(*If[head === g, Echo[InputForm[{def, rule, Hold[newRhs]}]]];*)
							{Replace[Unevaluated[expr], rule], True}
						]]
					]
				]
			];

			ret /; cond
		],

		(* No pattern variable substitution *)
		head_[left___, b, right___] /;
			MatchQ[
				Unevaluated[head[left, a, right]],
				Alternatives @@ Keys @ UpValues[a]
			] ^:= DelayedBlock[a, b, head[left, a, right]]
	];

	(* Inherit OwnValues *)
	b /;
		MatchQ[
			Unevaluated[a],
			Alternatives @@ Keys @ OwnValues[a]
		] := a;

	(* Attributes are copied, no way to inherit it that I know of *)
	Attributes[b] = Attributes[a];
)


NewInstance[cmd : "$New" | "$Extend", self_, src_, initArgs___] := Enclose @ With[
{
    super = If[cmd === "$New", self, self["$Class"]]
},
With[{
    ref = Replace[Unevaluated[src], {
        name_String :> Unique[name <> "$"],
        Automatic | Except[_ ? Developer`SymbolQ] :> Unique[StringDelete[ToString[Unevaluated[super]], Except[WordCharacter | "$"]] <> "$"]
    }]
},
	InheritDefinitions[self, ref];
	SetAttributes[ref, {Temporary}];

    (* every instance is also a class, initialize as class first *)
    Confirm @ Class[If[cmd === "$New", Unevaluated["$Init"[ref, super]], Unevaluated["$Init"[ref, super, initArgs]]]];

	ref["$Parent"] = self;

    ref["$Label"] = Replace[Unevaluated[src], {
        Automatic :> ToString[Unevaluated[self]],
        sym_ ? Developer`SymbolQ :> SymbolName[Unevaluated[sym]],
        _ :> ToString[Unevaluated[src]]
    }];

    ref["$AllProperties"] := MissingUnion[{ref["$Properties"], If[self === Class, {}, self["$AllProperties"]]}];
    ref["$AllClassMethods"] := MissingUnion[{ref["$ClassMethods"], If[self === Class, {}, self["$AllClassMethods"]]}];
	ref["$AllStaticMethods"] := MissingUnion[{ref["$StaticMethods"], If[self === Class, {}, self["$AllStaticMethods"]]}];

    If[ cmd === "$New",

        (* methods *)
        ref[method_String[args : PatternSequence[arg_, ___] | ___], opts___] /; ClassMethodQ[method, self] && Unevaluated[arg] =!= ref && Unevaluated[arg] =!= ref["$Parent"] :=
            If[self["$Parent"] === Class, self[Unevaluated[method[self, args]], opts], self["$Parent"][Unevaluated[method[self, args]], opts]];

		If[ self =!= Class,
            ref[method_String[args___] /; ! StaticMethodQ[method, self], opts___] := self[method[ref, args], opts]
        ];

        (* properties *)
	    ref[prop_String, opts___] /; PropertyQ[prop, ref] := self[prop[ref], opts];

        If[ self =!= Class,
			ref[def : _String | _String[___]] := self[def]
		];

		(* initialize *)
        Confirm @ self[Unevaluated["$Init"[ref, initArgs]]];

		(* missing method fallback *)
        If[ self === Class,
            ref[method_String[args___], opts___] := Which[
				method === "$Init",
				ref,
				ClassMethodQ[method, ref] && (Length[Unevaluated[{args}]] == 0 || MatchQ[Extract[Unevaluated[{args}], 1, Unevaluated], ref]),
				ref[method[ref, args], opts],
				True,
				Missing[method]
			];
			ref[prop_String] := Missing[prop]
        ];

		(* default class constructor is a Class constructor, absence of defined $Init would result in calling it twice, with and without initArgs *)
		HoldPattern[ref["$Init"[obj_, args___]]] := Class["$Init"[obj, ref, args]];
        ,

		(* else Extend *)
        ref[method_String[ref, args___], opts___] /; ClassMethodQ[method, self] := self[Unevaluated[method[ref, args]], opts];
        ref[method_String[args : PatternSequence[arg_, ___] | ___], opts___] /; ClassMethodQ[method, self] && Unevaluated[arg] =!= ref && Unevaluated[arg] =!= self :=
            ref[Unevaluated[method[ref, args]], opts];

    ];

    If[ self["$Parent"] === Class,
        MakeBoxes[ref, form___] ^:= self["$Format"[ref, form]],
        MakeBoxes[ref, form___] ^:= self["$Class"]["$Format"[ref, form]]
    ];

	(* Destructor *)
	Remove[ref] ^:= (ref["$Destroy"[]]; Quiet[Scan[Remove, AllChildren[ref]]; Block[{ref}, Remove[ref]]; Remove[ref], Remove::remal]);

    ref
]]

Class["$Init"[self_, class_, initValues___]] := Block[{
    initRules = Replace[{initValues}, {lhs : Except[_Rule | _RuleDelayed] :> lhs -> None}, {1}],
    definitions = {}
},
    self["$Class"] = class;
    self["$Test"] = ClassTest[self];
    self["$Type"] = _Symbol ? (self["$Test"]);
    self["$Icon"] = None;
	self["$Properties"] = {};
    self["$ClassMethods"] = {};
	self["$StaticMethods"] = {};

    self[(cmd : "$New" | "$Extend") | (cmd : "$New" | "$Extend")[initArgs___], src_ : Automatic] :=
        NewInstance[cmd, self, Unevaluated[src], initArgs];

	self["$Format"[obj_, form___]] :=
        BoxForm`ArrangeSummaryBox[
	        obj["$Label"],
	        obj,
	        obj["$Icon"],
	        {
				{BoxForm`SummaryItem[{"Class: ", ToString[obj["$Class"]]}]},
	            {BoxForm`SummaryItem[{"Parent: ", ToString[obj["$Parent"]]}]}
	        },
	        {{BoxForm`SummaryItem[{"Symbol: ", SymbolName[obj]}]}},
	        form
	    ];

    Scan[
        Replace[rule_[lhs_, rhs_] :> (
            AppendTo[definitions, lhs];
            Replace[rule, {Rule -> Set, RuleDelayed -> SetDelayed}][self[lhs], rhs]
        )],
        initRules
    ];
    self["$InitDefinitions"] = definitions;

    Normal[self] ^:= self["$Normal"[]];
    N[self, args___] := self["$N"[args]];

    (* Sugar *)
    Composition[self, calls : PatternSequence[_, __]] ^:= Fold[Function[Null, #1[Unevaluated[#2]], HoldRest], self, Unevaluated[{calls}]];

    self
]


Class["$Init"[Class, Class, "$Parent" -> Class]];

Class[class_, values___] := (Class[Unevaluated["$New"[class, values]], Unevaluated[class]])

Class[class_ -> parent_ ? Developer`SymbolQ, values___] :=
    HoldPattern[parent[class]] = parent["$Extend"[values], Unevaluated[class]]


ClassTest[self_][x_] := With[{super = x["$Parent"]}, super =!= Unevaluated[x["$Parent"]] && (MatchQ[super, self] || super =!= Class && ClassTest[self][super])]
ClassQ[x_] := Unevaluated[x] === Class || Developer`SymbolQ[Unevaluated[x]] && ClassQ[x["$Parent"]]
ClassQ[___] := False
PropertyQ[prop_, self_] := ListQ[self["$AllProperties"]] && MemberQ[self["$AllProperties"], prop]
ClassMethodQ[method_, self_] := ListQ[self["$AllClassMethods"]] && MemberQ[self["$AllClassMethods"], method]
StaticMethodQ[method_, self_] := ListQ[self["$AllStaticMethods"]] && MemberQ[self["$AllStaticMethods"], method]

SetAttributes[{PropertyMethod, StaticMethod, ClassMethod}, HoldFirst]
PropertyMethod[set : _[class_[method_[___], ___], _]] := (class["$Properties"] //= Append[method]; set)
StaticMethod[set : _[class_[method_[___], ___], _]] := (class["$StaticMethods"] //= Append[method]; set)
ClassMethod[set : _[class_[method_[___], ___], _]] := (class["$ClassMethods"] //= Append[method]; set)


(* ::Section::Closed:: *)
(*Package Footer*)


End[];
EndPackage[];
