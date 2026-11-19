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
  | EMax lhs rhs =>
    match eval sigma lhs, eval sigma rhs with
    | Some (VNat l), Some (VNat r) => Some (VNat (l + r))
    | Some (VBool l), Some (VBool r) => Some (VBool (orb l r))
    | _, _ => None
    end
  | EAnd lhs rhs =>
    match eval sigma lhs, eval sigma rhs with
    | Some (VBool l), Some (VBool r) => Some (VBool (andb l r))
    | _, _ => None
    end
  | EIf cond ifT ifF =>
    match eval sigma cond with
    | Some (VBool true) => eval sigma ifT
    | Some (VBool false) => eval sigma ifF
    | _ => None
    end
  end.

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
