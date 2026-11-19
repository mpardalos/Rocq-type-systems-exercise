Inductive Expr: Set :=
| ELitNat (n: nat)
| ELitBool (b: bool)
| EVar (v: nat)
| EAnd (lhs rhs: Expr)
| EMax (lhs rhs: Expr)
| EIf (cond ifT ifF: Expr)
.

Variant Value: Set :=
| VNat (n: nat)
| VBool (b: bool)
.

Fixpoint eval (sigma: nat -> option Value) (e: Expr): option Value :=
  match e with
  | ELitNat n => Some (VNat n)
  | ELitBool b => Some (VBool b)
  | EVar v => sigma v
  | EAnd lhs rhs =>
    match eval sigma lhs, eval sigma rhs with
    | Some (VBool l), Some (VBool r) => Some (VBool (andb l r))
    | _, _ => None
    end
  | EMax lhs rhs =>
    match eval sigma lhs, eval sigma rhs with
    | Some (VNat l), Some (VNat r) => Some (VNat (max l r))
    | Some (VBool l), Some (VBool r) => Some (VBool (orb l r))
    | _, _ => None
    end
  | EIf cond ifT ifF =>
    match eval sigma cond with
    | Some (VBool true) => eval sigma ifT
    | Some (VBool false) => eval sigma ifF
    | _ => None
    end
  end.

(* Should some of it be left as exercise? *)
Inductive SStepEval (sigma: nat -> option Value): Expr -> Expr -> Prop :=
| SSEVarNat (v: nat) (n: nat): sigma v = Some (VNat n) -> SStepEval sigma (EVar v) (ELitNat n)
| SSEVarBool (v: nat) (b: bool): sigma v = Some (VBool b) -> SStepEval sigma (EVar v) (ELitBool b)
| SSEAndL (lhs lhs' rhs: Expr): SStepEval sigma lhs lhs' -> SStepEval sigma (EAnd lhs rhs) (EAnd lhs' rhs)
| SSEAndR (lhs rhs rhs': Expr): SStepEval sigma rhs rhs' -> SStepEval sigma (EAnd lhs rhs) (EAnd lhs rhs')
| SSEAnd (bl br: bool): SStepEval sigma (EAnd (ELitBool bl) (ELitBool br)) (ELitBool (andb bl br))
| SSEMaxL (lhs lhs' rhs: Expr): SStepEval sigma lhs lhs' -> SStepEval sigma (EMax lhs rhs) (EMax lhs' rhs)
| SSEMaxR (lhs rhs rhs': Expr): SStepEval sigma rhs rhs' -> SStepEval sigma (EMax lhs rhs) (EMax lhs rhs')
| SSEMaxBool (bl br: bool): SStepEval sigma (EMax (ELitBool bl) (ELitBool br)) (ELitBool (orb bl br))
| SSEMaxNat (nl nr: nat): SStepEval sigma (EMax (ELitNat nl) (ELitNat nr)) (ELitNat (max nl nr))
| SSEIfC (cond cond' ifT ifF: Expr): SStepEval sigma cond cond' -> SStepEval sigma (EIf cond ifT ifF) (EIf cond' ifT ifF)
| SSEIfT (cond ifT ifT' ifF: Expr): SStepEval sigma ifT ifT' -> SStepEval sigma (EIf cond ifT ifF) (EIf cond ifT' ifF)
| SSEIfF (cond ifT ifF ifF': Expr): SStepEval sigma ifF ifF' -> SStepEval sigma (EIf cond ifT ifF) (EIf cond ifT ifF')
| SSEIf (b: bool) (ifT ifF: Expr): SStepEval sigma (EIf (ELitBool b) ifT ifF) (if b then ifT else ifF)
.

Variant TypeTag: Set := TNat | TBool.

Inductive ValueType: Value -> TypeTag -> Prop :=
| VTNat (n: nat): ValueType (VNat n) TNat
| VTBool (b: bool): ValueType (VBool b) TBool
.

(* Do not modify anything above this point *)

Inductive ExprType (gamma: nat -> option TypeTag): Expr -> TypeTag -> Prop :=
| ETLitNat (n: nat): ExprType gamma (ELitNat n) TNat
| ETLitBool (b: bool): ExprType gamma (ELitBool b) TBool
| ETVar (v: nat) (t: TypeTag): gamma v = Some t -> ExprType gamma (EVar v) t
(* TODO: complete type statement *)
.

(* TODO: express and prove theorem, modifying any part of ExprType is allowed *)
(* the statement is obviously wrong, but gives the idea that your theorem should express *)
Fail Lemma CorrectType:
  forall (sigma: nat -> option Value) (e: Expr) (t: TypeTag),
  ExprType sigma e t -> ValueType (eval sigma e) t
.
