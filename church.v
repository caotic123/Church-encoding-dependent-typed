From Coq Require Import ssreflect ssrfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Vectors.VectorDef.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Compare_dec.

Inductive A_nat (A : Type) (f : A -> A) : A -> Type := 
                              |As : forall {x : _}, A_nat f x -> A_nat f (f x)
                              |AZero : forall (x_ : _), A_nat f x_.

Definition FZero {T} (x : T) (f : T -> T) : T := x.
Definition Sn {T} (f : T -> (T -> T) -> T) (x : T) (a : T -> T) : T := f (a x) a.
Definition Sn_arith {T} (f : (T -> T) -> T) (a : (T -> T)) := f a.

Definition one {X} (t : X) (w : X -> X) := (Sn FZero t w).
Definition A_one {X} (t : X) (w : X -> X) := (As (AZero w t)).

Definition ind_r {B} {A : B} {f : B -> B} (x : A_nat f A) := A.

Inductive Maybe (A : Type) := |Surely : A -> Maybe A | Nothing. 

Fixpoint n_ {A : Type} {f : A -> A} {c : A} (a : A_nat f c) :=
  match a with
    |As s => n_ s
    |AZero _ v => v
  end.

Compute Sn.
Inductive N_corrseq {T} (G : T -> T) : forall (x : T), A_nat G x -> (T -> (T -> T) -> T) -> Type  :=
 |Eq_Correspodence : forall {q} {y} {d : A_nat G y}, (ind_r d) = q (n_ d) G -> N_corrseq d q -> N_corrseq (As d) (Sn q)  
 |Base_case : forall (y : T) (b : T -> (T -> T) -> T), (ind_r (AZero G y)) = b (n_ (AZero G y)) G -> N_corrseq (As (AZero G y)) (Sn FZero).
 
Theorem A_one_eq_one : forall {A} (t : A) (k : A -> A), one t k = ind_r (A_one t k).
intros.
unfold A_one.
unfold one.
compute.
reflexivity.
Qed.

Definition Sn_nat {A : Type} {f : A -> A} {c : A} (a : A_nat f c) : A -> (A -> A) -> A :=
  let fix sn_ {c : A} (a : A_nat f c) := (match a with
    |@As _ _ d xs => Sn (sn_ xs)
    |@AZero _ _ v => FZero
  end) in (sn_ a). 

Compute Sn_nat.
Compute ind_r (As (AZero (plus 1) 0)).
Compute (Sn_arith (Sn_nat (As (AZero (plus 1) 0)) 0)) (plus 1).
Compute (fun {y v} (s' : A_nat y v) => ind_r (As (As s')) = Sn_nat (As (As s')) (n_ (As (As s'))) y) _ _ (AZero (plus 1) 0).

Compute (fun {y v} (s' : A_nat y v) => Sn_nat s' (n_ s') y = v) _ _ (AZero (plus 1) 0).

Definition one_nat_correspond : forall {A : Type} (w : A) (n : A -> A), N_corrseq (As (As (As (AZero n w)))) (Sn (Sn (Sn FZero))).
 refine (fun {A : Type} (w : A) (n : A -> A) => (Eq_Correspodence _ (Eq_Correspodence _ (@Base_case _ n w FZero eq_refl)))).
compute; by [].
trivial.
Qed.

Theorem functor_apply_nat : forall {T} {x : T} {k : T -> T} (s' : A_nat k x), x = Sn_nat s' (n_ s') k -> k x = k x.
move => A p d z; case => P.
by [].
Qed.

Definition just_partial {A} {f : A -> A} {x' : A} (x : A_nat f x') : Maybe (A_nat f x') :=
  match x with
    |@As _ _ _ s => Surely (As s)
    |AZero _ _ => Nothing _
  end.

Theorem naturals_are_parcials : forall {A} {f : A -> A} (c : A) (x : A_nat f c), just_partial x = Surely x \/ just_partial x = Nothing _.
move => s k g' v'.
destruct v'.
apply : or_introl.
trivial.
apply : or_intror.
trivial.
Qed.

Compute (fun (A : Type) (d : A -> A) (x : A) (f : A_nat d x) => 
 Sn (Sn_nat f) (n_ f) d = d (Sn_nat f (n_ f) d)) _ _ _ (As (AZero (plus 2) 0)).

(*P = (Sn x) f.
P (f x) = f (P x) *)

Fixpoint r_nat {A : Type} (a : nat) : A -> (A -> A) -> A :=
  match a with
    |S n => fun (x0 : A) (a0 : A -> A) => r_nat n (a0 x0) a0
    |0 => fun (x0 : A) (_ : A -> A) => x0
  end. 

Theorem nat_homomorphism : forall T (f : T -> T) (h : T) (x : A_nat f h) (t' : T), (Sn_nat x (f t') f) = f ((Sn_nat x) t' f).
move => k d g'; elim => [H' h HP].
move => t; by move : HP; by apply.
by [].
Qed. 


Theorem apply_inSnat_Sym : forall (T : Type) (f' : T -> T) (y : T) (v' : A_nat f' y), Sn_nat v' (f' (n_ v')) f' = f' (Sn_nat v' (n_ v') f').
intros.
induction v'.
set nat_proof := (nat_homomorphism (As v') (n_ (As v'))).
rewrite nat_proof; by symmetry.
trivial.
Qed.

Theorem afterAs_is_composition : forall (A : Type) (d : A -> A) (x : A) (f : A_nat d x), Sn_nat f (n_  f) d = x -> Sn_nat (As f) (n_ (As f)) d = d x.
intros.
apply eq_sym in H.
simpl; simpl in H.
replace (d x) with (d (Sn_nat f (n_ f) d)).
unfold Sn.
apply apply_inSnat_Sym.
apply eq_sym in H.
trivial; by replace (Sn_nat f (n_ f) d) with x by H.
Qed.

Theorem nat_composition_is_just_application : forall {A} {c : A} {k : A -> A} (s' : A_nat k c), (Sn_nat s' (n_ s') k = c).
move => T c d f.
induction f.
 + apply afterAs_is_composition; symmetry; rewrite IHf; by apply : eq_refl.
 + by [].
Qed.

Theorem nextNatEqH : forall {A} {c : A} {k : A -> A} (s' : A_nat k c), ind_r s' = Sn_nat s' (n_ s') k -> ind_r (As s') = Sn_nat (As s') (n_ (As s')) k.
intros.
unfold ind_r; unfold ind_r in H.
set certification_of_just_composition := nat_composition_is_just_application (As s').
by []; by symmetry; by simpl.
Qed.

Fixpoint NAT_case_Correspodence {N} {x : N} {y : N -> N} (b : A_nat y x) {struct b} : N_corrseq (As b) (Sn_nat (As b)).
  refine (match b as q return N_corrseq (As q) (Sn_nat (As q)) with
    |@As _ _ a s => @Eq_Correspodence _ y (Sn_nat (As s)) (y a) (As s) _ (NAT_case_Correspodence N a y s)
    |@AZero _ _ x_  => @Base_case N y x_ (Sn_nat (AZero _ _)) eq_refl
  end).

elim :s => [H s' q].
move : q.
elim : b => [D s f g].
destruct f;destruct g.
reflexivity.
reflexivity.
move => S n.
move : n; by apply nextNatEqH.
auto; by compute.
assumption.
trivial.
Qed.

Definition add {A : Type} (fc : (A -> (A -> A) -> A) -> ((A -> (A -> A) -> A) -> (A -> (A -> A) -> A)) -> (A -> (A -> A) -> A)) (b : (A -> (A -> A) -> A)) := fc b (fun f => Sn f).

Compute (add FZero FZero) 0 (plus 1).

Theorem Zero_add_0_is_0_church_encoding : forall {Z} (x : Z -> Z) (y : Z), (add FZero FZero) y x = y.
compute; by [].
Show Proof.
Qed.

Fixpoint applications_func_Anat {T} {y : T -> T} {x g : T} (c : A_nat y x) (y' : A_nat y g) : T :=
  match y' with
    |As s => y g
    |AZero _ _ => g
  end.

Record IndPair (A B : Set) : Set := Do_Pair {
  fst_pair : A;
  snd_pair : B;
  }.

Notation "{ | x | | y | }" := (forall r : Type, (x -> y -> r) -> r) (at level 100, right associativity).

Definition Pair (A : Type) (B : Type) (x : A) (y : B) : { |A| |B| } := (fun (r : Type) (f : A -> B -> r) => f x y).
Notation "| x | | y |" := (Pair x y) (at level 100, right associativity, only parsing).

Definition fst {A T} (pair : forall r : Type, (A -> T -> r) -> r) :=
  pair A (fun x y => x).

Definition snd {A T} (pair : forall r : Type, (A -> T -> r) -> r) :=
  pair T (fun x y => y).

Theorem pair_is_correspond : forall {A B : Set} (x : A) (y : B), fst_pair (Do_Pair x y) = fst (|x| |y|) /\ snd_pair (Do_Pair x y) = snd (|x| |y |).
move => a b k' c'.
apply : conj.
reflexivity; by unfold fst_pair.
reflexivity; by unfold snd_pair.
Show Proof.
Qed.

(*that's proof can be easily made in gallinia way*)
Definition pair_is_correspond2 {A B : Set} (x : A) (y : B) : fst_pair (Do_Pair x y) = fst (|x| |y|) /\ snd_pair (Do_Pair x y) = snd (|x| |y |) :=
  conj (eq_refl (fst_pair (Do_Pair x y))) (eq_refl (snd_pair (Do_Pair x y))).

Inductive bool {T' : Type} : T' -> Type :=
                 |true : forall (a b : T'), bool a
                 |false : forall (a b : T'), bool b.

Definition church_true {A : Type} := (fun x y : A => x).
Definition church_false {A : Type} := (fun x y : A => y).

Definition v'_bool {A} {y : A} (b : bool y) := y.

(*church_bool_inductive_bool_correspond is a extremely easily proof*)
Theorem church_bool_inductive_bool_correspond : forall {T} {y z : T}, v'_bool (true y z) = church_true y z /\ v'_bool (false y z) = church_false y z.
intuition.
Qed.

(*bool_sym b' b = bool b' c = bool b', (b = c) -> (c = b). 
  just move => H C P d. by elim : d. Qed. *) 

Definition revert_boolean {A : Type} {y : A} (x : bool y) : bool y := 
  match x with
    |true a b => false b a
    |false a b => true b a
  end.

(*if x then q else q' so = if not x then q' else q) *)

Theorem dif_p_p : forall (A : Type) {x : A} (p : bool x), v'_bool p = v'_bool (revert_boolean p).
move => p k'.
case; by [].
Qed. 

Definition cmp_bool {A} {x' : A} (b : bool x') : A :=
  match b with
    |true a b => a
    |false a b => b
  end.
   
Definition just_compare_boolean {A} (x' y' : A) (x : bool x') (y : bool y') : bool x' :=
  match (x, y) with
    |(true _ _ , false _ _) => true x' y'
    |(false _ _, false _ _) => true x' y'
    |_ => false y' x'
  end.
   

Theorem eq_p_p : forall {A} {x y : A} (p : bool x), (p = true x y) -> (p <> false y x).
intros.
destruct p.
induction H.
discriminate.
discriminate H.
Qed. 

Theorem or_dif : forall {A} (x y : A) (b : bool x) (c : bool x), (b = true x y \/ b = false y x) /\ (c = true x y \/ c = false y x) -> (b <> c) -> (c = true x y /\ b = false y x) \/ (c = false y x /\ b = true x y).
intros.
destruct H.
induction H.
induction H1.
apply eq_sym in H.
replace b with (true x y) in H0 by H ;replace c with (true x y) in H0 by H.
move : H0; by case; by reflexivity.
apply : or_intror.
pose (conj H1 H); by assumption.
case : H1 H.
move => a b'.
apply : or_introl; by pose (conj a b'); by assumption.
move => a' b'; apply : or_introl; apply : conj.
case : H0.
apply eq_sym in a'.
rewrite b'; rewrite a'.
apply : eq_refl.
replace b with (false y x) by a'.
trivial.
Qed.

Definition t_list (T : Type) := (T -> T -> T) -> T -> T.
Definition nil {A : Type} (f : A -> A -> A) (d : A) := d.
Definition cons {A : Type} (v' : A) (c_cons : t_list _) (f : A -> A -> A) (v'' : A) :=
  f v' (c_cons f v'').
  

Inductive list (A : Type) (f : A -> A -> A) : A -> Type :=
  |Acons : forall (x : A) (y' : A) (cons' : list f y'), list f (f x y')
  |Anil : forall (x: A) (y : A), list f (f x y).

(*Fixpoint foldable_nat_list {f : nat -> nat -> nat} {y : nat} (A : list f y) := 
  match A with 
   |Acons x y => x + (foldable_nat_list
   |Anil _ x y => x + y
  end. *)

Compute Acons 4 (Acons 2 (Anil (plus) 3 3)). 

Definition v'_list {X} {f : X -> X -> X} {y : X} (A : list f y) := y.
 
Compute v'_list (Acons 2 (Anil (plus) 2 3)).
Compute (cons 2 (cons 2 nil)) (plus) 0. 

Fixpoint curry_list {A} {y : A} {z' : A -> A -> A} (l : list z' y) : t_list A := 
match l return t_list A with
  |Acons x y => cons x (@curry_list _ _ _ y)
  |Anil _ x _  => cons x nil
end.

Fixpoint minimal_case {A} {y' : A} {functor : A -> A -> A} (a : list functor y') {struct a} : A :=
  match a with
    |Acons x y => @minimal_case _ _ _ y
    |Anil _ _ y => y
   end.

Definition list_correspodence {A} {y : A} {z' : A -> A -> A} (xs : list z' y) : A := 
  (@curry_list _ _ _ xs) z' (@minimal_case _ _ _ xs).

Compute (Acons 3 (Acons 2 (Anil (plus) 2 3))).

Compute (list_correspodence ((Acons 2 (Anil (fun x y => if (leb x y) then y else x) 0 2)))).
Compute (fun {A} {Y : A} (z: A -> A -> A) (x : list z Y) (v' : A) => 
 (v'_list x) = (list_correspodence x)) _ _ _ (Acons 4 (Acons 2 (Anil (fun x y => if (leb y x) then y else x) 0 3))).

Theorem list_composition : forall {A} (z : A -> A -> A) (x0 x'' y' : A) (l : list z (z x0 x'')), z x0 x'' = list_correspodence l -> z (z x0 x'') y' = z (list_correspodence l) y'.
intros.
replace (z (z x0 x'') y') with (z (list_correspodence l) y').
auto.
move : H.
generalize (list_correspodence l).
intros.
replace a with (z x0 x'') by H.
trivial.
Qed.

Definition test (A : Type) (z : A -> A -> A) (d' n : A) (x : list z (z d' n)) (y' : A)
 := z (list_correspodence x) y' = list_correspodence (Acons y' x).

Theorem func_is_just_listed_appplication : forall (A : Type) (z : A -> A -> A) (d' n : A) (x : list z (z d' n)) (y' : A), z y' (list_correspodence x) = list_correspodence (Acons y' x).
intros.
reflexivity.
Qed.

Theorem test1 : forall (z: nat -> nat -> nat), v'_list (Acons 20 (Acons 2 (Anil z 3 4))) = list_correspodence (Acons 20 (Acons 2 (Anil z 3 4))).
auto.
Qed.

Theorem church_list_correspodence_ind_list : forall (A : Type) (z: A -> A -> A) (x' : A) (x : list z x'), v'_list x = list_correspodence x.
induction x.
unfold v'_list in *; unfold list_correspodence in *.
unfold curry_list in *.
unfold cons in *.
move : IHx.
unfold minimal_case in *.
generalize ((fix
    curry_list (A0 : Type) (y : A0) (z' : A0 -> A0 -> A0) 
               (l : list z' y) {struct l} : t_list A0 :=
      match l with
      | @Acons _ _ x1 y'0 y0 =>
          fun (f : A0 -> A0 -> A0) (v'' : A0) =>
          f x1 (curry_list A0 y'0 z' y0 f v'')
      | Anil _ x1 _ =>
          fun (f : A0 -> A0 -> A0) (v'' : A0) => f x1 (nil f v'')
      end) A y' z x0 z
     ((fix
       minimal_case (A0 : Type) (y'0 : A0) (functor : A0 -> A0 -> A0)
                    (a : list functor y'0) {struct a} : A0 :=
         match a with
         | @Acons _ _ _ y'1 y => minimal_case A0 y'1 functor y
         | Anil _ _ y => y
         end) A y' z x0)). (*more know in brazilian knowledge 'gambiarra'*)

move => h' H.
replace y' with h' by H.
reflexivity.
auto.
Qed.


(*Fixpoint add_ {T} {y_ : T -> T} {g t : T} (d : A_nat y_ g) (c : A_nat y_ t) {struct d} : A_nat y_ (applications_func_Anat d c).
   refine(match d as k' return A_nat y_ (y_ (applications_func_Anat k' c)) with
     |@As _ _ fg s  => (@As T y_ _ (@add_ T y_  fg _ s c))
     |AZero _ _ =>  (@As T y_ (applications_func_Anat (AZero _ _) c) c)
   end). *)




