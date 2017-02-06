(*standart Coq*)

(*Definition Var := nat.*)
Axiom Var: Type.

Axiom eps: Var -> Var -> Prop.

Definition sub (X Y:Var): Prop := forall Z:Var, (eps Z X) -> (eps Z Y).
Definition eqc (X Y:Var): Prop := forall Z:Var, (eps Z X) <-> (eps Z Y).
Notation "X == Y" := (eqc X Y) (at level 85) : type_scope.
Check (_ = _).

(*Prop 4.1(a)*)
Definition p4_1 (X Y:Var): (X == Y) <-> (sub X Y /\ sub Y X).
Proof.
unfold iff.
apply conj.
+ intro p.
  apply conj.
  exact (fun Z => proj1 (p Z)).
  exact (fun Z => proj2 (p Z)).
+ intros w Z.
  apply conj.
  exact ((proj1 w) Z).
  exact ((proj2 w) Z).
Defined.

(*Prop 4.1(b)*)
Definition eqc_ref (X : Var) : (X == X).
Proof.
unfold eqc.
intro Z.
refine (conj (fun x => x) (fun x => x)).
Defined.

(*Prop 4.1(c)*)
Theorem eqc_sym (X:Var) (Y:Var) : (X == Y) -> (Y == X).
Proof.
unfold eqc.
intros q Z.
exact (iff_sym (q Z)).
Show Proof.
Defined.

(*Prop 4.1(d)*)
Definition eqc_trans (X Y Z: Var) : (X == Y) -> (Y == Z) -> (X == Z).
Proof.
unfold eqc.
intros Q1 Q2 W.
simple refine (iff_trans (Q1 W) (Q2 W) ).
Defined.

Definition M (X : Var): Prop := ex (fun (Y:Var) => eps X Y).
Definition Pr (X : Var): Prop :=  not (M X).

(*Ex. 4.1*)
Definition ex4_1 :forall X Y, eps X Y -> M X.
Proof.
intros X Y p.
refine (@ex_intro _ _ Y p).
Defined.

Axiom exc_mid : forall (A:Prop), A \/ (not A).

(*Extensionality principle *)
(*Ex. 4.2*)
Definition set_ext (X Y: Var) :X == Y <-> (forall Z:Var, (M Z) -> (eps Z X <-> eps Z Y)).
Proof.
apply conj.
+ intros p Z _.
  exact (p Z).
+ intros p Z .
  destruct (exc_mid (M Z)).
  - simple refine (p Z H).
  - apply conj.
    intro m.
    destruct (H (@ex4_1 Z X m)).
    intro m.
    destruct (H (@ex4_1 Z Y m)).
Defined.

Axiom axT: forall A B Z, (A == B) -> ((eps A Z) <-> (eps B Z)).
(*Ex. 4.3*)
Definition set_transport (Y Z: Var) : (M Z) /\ (Z == Y) -> (M Y).
Proof.
intro w.
pose(p1w:=proj1 w).
pose(p2w:=proj2 w).
unfold M in p1w.
destruct p1w as [q j].
pose(J:= @axT Z Y q p2w ).
exact (ex4_1 _ _(proj1 J j)).
Defined.

(*
Axiom axP: forall x:Var, M(x) -> 
          (forall y:Var, M(y) -> (
           ex (fun z:Var => (M z) /\ 
          (forall u:Var, M(u) -> 
          (eps u z <-> (eps u x /\ eps u y) ) 
           )))).*)

Definition forset (Q:Var->Prop): Prop := forall x:Var, (M x) -> (Q x).
Definition exiset (Q:Var->Prop): Prop := exists x:Var, (M x) /\ (Q x).
Definition exIset (Q:Var->Prop): Prop := (exiset Q) /\ 
 (forset (fun x => 
  forset (fun y => 
  (Q x) /\ (Q y) -> x == y )
  )).
  
Definition contra (A B : Prop) : (A -> B) <-> (~B -> ~A).
Proof.
intros.
apply conj.
+ tauto.
(*+ intros f nb a.
  exact (nb (f a)).*)
+ intros g a.
  destruct (exc_mid B) as [H1|H0].
  exact H1.
  destruct (g H0 a).
Defined.
(*
Notation forsetd := (fun (Q:Var->Prop) => forall x:Var, forall mx:M x, (Q x)).
Notation exisetd := (fun (Q:Var->Prop) => exists x:Var, (M x) /\ (Q x)).
Axiom par : forsetd (fun x:Var =>
           forsetd (fun y:Var => Var)).
Axiom axP2: forsetd (fun x:Var =>
           forsetd (fun y:Var => 
           forsetd (fun u:Var => 
           (eps u (par x _ y _) <-> (u == x \/ u == y)
           )))).*)

Axiom par : forall x:Var, forall mx : M x, (forall y:Var, forall my : M y, Var).
Axiom mpar: forall x:Var, forall mx : M x, (forall y:Var, forall my : M y, (M (par x mx y my))).
Axiom axP2: forall x:Var, forall mx : M x,
           (forall y:Var, forall my : M y,
           forset (fun u:Var => 
           (eps u (par x mx y my) <-> (u == x \/ u == y)
           ))).

Definition axP: forset (fun x:Var =>
           forset (fun y:Var => 
           exiset (fun z:Var => 
           forset (fun u:Var => 
           (eps u z) <-> (u == x \/ u == y)
           )))).
Proof.
intros x mx y my.
simple refine (@ex_intro Var _ _ _).
exact (par x mx y my).
apply conj.
exact (mpar x mx y my).
exact (axP2 x mx y my).
Defined.

(*Axiom par2 : forset (fun x:Var =>
            forset (fun y:Var => Prop)).*)

(*Axiom axP: forset (fun x:Var =>
           forset (fun y:Var => 
           exiset (fun z:Var => 
           forset (fun u:Var => 
           (eps u z) <-> (u == x \/ u == y)
           )))).*)


(*Notation "'forset' B ';' A '%'  " := (forall a:A, B) (at level 0) : type_scope.
Context (A B: Prop).
Check (forset B ; A % ).*)
(*Ex. 4.4*)
Definition pair_uniq : forset (fun x:Var =>
           forset (fun y:Var => 
           exIset (fun z:Var => 
           forset (fun u:Var => 
           (eps u z) <-> (u == x \/ u == y)
           )))).
Proof.
 intros X mX Y mY.
 apply conj.
 
 exact (axP X mX Y mY ).
 intros A mA B mB U H.
 apply conj.
 + intro w.
 Check ex4_1 _ _ w. (*(@ex_intro _ _ H w)*)
   pose (s:= proj2 (proj2 U H (ex4_1 _ _ w))).
   apply s.
   pose (s2:= proj1 (proj1 U H (ex4_1 _ _ w))).
   exact (s2 w).
 + intro w.
   pose (s:= proj2 (proj1 U H (ex4_1 _ _ w))).
   apply s.
   pose (s2:= proj1 (proj2 U H (ex4_1 _ _ w))).
   exact (s2 w).
Defined.

(*Ex. 4.5*)
Definition ex4_5: forall X:Var, ((M X) <-> exiset (fun y => eps X y) ).
Proof.
intro X.
apply conj.
+ intro mX.
  unfold exiset.
  pose (pai :=  axP X mX X mX).
  simpl in pai.
  destruct pai as [c n].
  simple refine (@ex_intro Var _ c _).
  simpl.
  apply conj.
  apply (proj1 n).
  apply (proj2 (proj2 n X mX)).
  Check (eqc_ref X).
  apply or_introl.
  apply eqc_ref.
+ intro q.
  destruct q as [i j].
  simple refine (@ex_intro Var _ i _).
  exact (proj2 j).
Defined.

(*Definition contra (A B : Prop) : (A -> B) <-> (~B -> ~A).
Proof.
apply conj.
+ intros f nb a.
  exact (nb (f a)).
+ intros g a.
  destruct (exc_mid B) as [H1|H0].
  exact H1.
  destruct (g H0 a).
Defined.*)


Definition  asdfgh (P : Var -> Prop)  :forall x : Var, (~ P x -> exists a : Var, ~ P a)
:= (@ex_intro Var (fun a=> ~P(a))).

Definition doub_neg : forall P:Prop, (~~ P) -> (P).
Proof.
intro P.
destruct (exc_mid P) as [H1|H0].
+ intros _ .
  exact H1.
+ intro f.
  destruct (f H0).
Defined.

Definition modul1 (P : Var -> Prop) : (~ exists X, ~ P(X) ) <-> (forall X, P X).
Proof.
apply conj.
+ intros q X.
  destruct (exc_mid (P X)).
  exact H.
  destruct  (q (@ex_intro Var _ X H)).
+ intros g y.
  destruct y as [A B].
  exact (B (g A)).
Defined.

Definition modul2 (*zero:Var*) (P : Var -> Prop) : (exists X, P(X) ) -> (~forall X, ~P X).
Proof.
(*apply conj.
+*) intros q X.
  destruct q as [A B].
  exact (X A B).
(*+ intros g.
  simple refine (@ex_intro Var _ zero _).
  simpl.*)
Defined.

Definition modul2c (P : Var -> Prop) : (~ exists X, P(X) ) -> (forall X, ~P X).
Proof.
intros Q X m.
exact (Q (@ex_intro Var _ X m)).
Defined.

Definition modul2d (P : Var -> Prop) := proj1 (@contra (~ exists X, P(X) ) (forall X, ~P X)) (modul2c P).
Check modul2d.

Definition modul2b (P : Var -> Prop) : (~forall X, ~P X) -> (exists X, P(X) ).
Proof.
intro q.
apply doub_neg.
revert q.
exact (modul2d P).
Defined.


Definition modul3 (P : Var -> Prop) : (exists X, ~P(X) ) -> (~forall X, P X).
Proof.
intros q f.
destruct q as [X H].
exact (H (f X)).
Defined.

Definition pairclass := (forall (Y Z:Var), exists W:Var, forall U:Var, eps U W <-> U == Y \/ U == Z).

(*Axiom axN : (exiset (fun x => 
              (forset (fun y => 
               ~(eps y x)
              ))
              )).*)
Check Var.

Axiom nullclass : Var.
(*Axiom nisset : M nullclass.*)
Axiom aNC : (M nullclass) /\ forset (fun y : Var => ~ eps y nullclass).

Definition axN : (exiset (fun x => 
              (forset (fun y => 
               ~(eps y x)
              ))
              )).
Proof.
simple refine (@ex_intro Var _ nullclass _).
apply aNC.
Defined.
(*Definition nullclass2:Var.
destruct axN. case error*)
(*Definition thmns : Prop.
destruct axN.*)


Definition nullisset: M nullclass := proj1 aNC.
(*Proof.
unfold M.
(*destruct axN.*)
destruct (proj1 aNC) as [A B].
simple refine (@ex_intro Var _ A _).
simpl.
exact B.
Defined.*)


Definition thmN : (exiset (fun x => 
              (forset (fun y => 
               ~(eps y x)
              ))
              )).
Proof.
simple refine (@ex_intro Var _ nullclass _ ).
simpl.
apply conj.
exact nullisset.
Check ex4_1 nullclass.
destruct (axP nullclass nullisset nullclass nullisset).
exact (proj2 aNC).
Defined.

(*destruct axN as [nullset noe]*)

(*Null set is unique*)
Definition nsu : (exIset (fun x => 
              (forset (fun y => 
               ~(eps y x)
              ))
              )).
Proof.
unfold exIset.
apply conj.
+(* apply (@ex_intro _ _ nullclass aNC).*)
apply axN.
+ intros X mX Y mY c K.
  apply conj.
  - intro s.
    destruct (proj1 c K (ex4_1 _ _ s) s).
  - intro s.
    destruct (proj2 c K (ex4_1 _ _ s) s).
Defined.


Notation "'{' X ',' Y '}'":= (axP X _ Y _) (at level 0) : type_scope.

(*delete Check ex.
Axiom pr1 : forall (P : Var -> Prop), (ex P) -> Var.
Axiom pr2 : forall (P : Var -> Prop), forall (s:ex P), (P (pr1 P s)).
*)

Definition pr (A : Prop) (P : A -> Prop): (ex P) -> A.
Proof.
intro s.
destruct s.
exact x.
Defined.
(*
Definition pr (P : Var -> Prop): (ex P) -> Var.
Proof.
intro s.
destruct s.
Check (exc_mid (ex P)).
Check  (exists x, P x) \/ ~ (exists x, P x).
destruct (exc_mid (ex P)).
destruct s.*)




(*Ex. 4.6*)
Definition ex4_6: (exists X, (Pr X)) -> 
~pairclass.
Proof.
 pose (j:= contra (exists X:Var, Pr X) (~pairclass)).
 apply (proj2 j).
 unfold pairclass, Pr, M.

 intro t.
 apply modul1.
 pose (tt:= doub_neg pairclass t).
 unfold pairclass in tt.
 intro X.
 destruct (tt X X) as [A B].
 pose (W := proj2 (B X) (or_introl (eqc_ref X))).
 exact (@ex_intro Var _ _ W).
Defined.


(*Ex. 4.7a*)
(*Definition pair_sym : forset (fun x =>
forset (fun y =>
 (pr1 _ {x , y}) == (pr1 _ {y , x})
)
).*)



(*{|}*)

Definition E := exiset (fun x => exiset (fun y => eps x y) ).
Definition Trans (X:Var):= forset (fun u => (eps u X -> sub u X) ).

(*Check axN.
Axiom nullclass : Var.
Axiom aNC : forset (fun y : Var => ~ eps y nullclass).
*)
(*Ex.4.29c*)
Definition emptrans : Trans (nullclass).
Proof.
unfold Trans.
intros u l j.
(*destruct (aNC u l j).!!!*)
unfold sub.
destruct ((proj2 aNC) u l j).
Defined.

Axiom compl : forall X:Var, Var.
Axiom B3 : forall X, forset (fun u => eps u (compl X) <-> ~ eps u X).
(*Axiom B3 : forall X, exists Y, forset (fun u => eps u Y <-> ~ eps u X). (*complement*)*)



Definition V:= compl nullclass.
(* ================== end of file ==================
(*Prop. 4.8 Class Existence Theorem*)
Definition V2:=.
Definition Rel := sub X V2.
Definition Irr (X Y : Var) := (Rel X) /\ (forset (fun y=> eps y Y -> ~ eps (pair y y) X)).

Definition We (X Y : Var) := (Irr X Y) /\ (forall Z:Var, (sub Z Y /\ ~(Z==nullclass) ->
exiset (fun y => eps y Z /\
forset (fun v => eps v Z /\ ~(v==y) -> (eps (pair y v) X /\ ~eps (pair v y) X)
)
)
)).

Definition Ord (X:Var):=(We E X) /\ (Trans X)
(*Class of ordinal numbers*)
Definition On:=..

Definition forord (Q:Var->Prop): Prop := forall x:Var, (Ord x) -> (Q x).
Definition exiord (Q:Var->Prop): Prop := exists x:Var, (Ord x) /\ (Q x).
Definition exIord (Q:Var->Prop): Prop := (exiord Q) /\ 
 (forord (fun x => 
  forord (fun y => 
  (Q x) /\ (Q y) -> x == y )
  )).

*)
(*Prop. 4.9: Transfinite induction*)

