(*
Серия семинаров по Coq.

Домашние задания помечены комментарием с заголовком HW
и являются одним из двух:
- теоремы с доказательством admit.
- определения без тела.
Смыслом задания является приведение содержательного доказательства/определения.
 *)

(*
Иерархия типов данных в Coq такова:
Set - всякие данные (те самые сеты)
Prop - утверждения пропозициональной логики.
Type - тип для Set и Prop
Вообще, бывают Type(i) - всевозможных рангов до бесконечности, и работает
следующее:
Set : Type(1)
Prop : Type(1)
Type(i) : Type(i + 1)

TO READ: Reference manual, 4.1.1

В Coq уже встроено большое количество стандартных структур данных,
таких как bool, nat, пары и +-типы. Про них уже доказано куча классных теорем в библиотеке.
Но в образовательных целях мы переопределим их заново, а так же определим классные множества, 
про которые рассказывал Миша. *)

(* Для начала нам понадобятся собственные пропозициональные True и False *)
Inductive True' : Prop := I : True'.
Inductive False' : Prop :=.

Notation "~ A" := (A -> False') : My_scope.

Open Scope My_scope.

(* На самом деле, равенство в Coq реализовано именно так, Нет встроенного понятия равенства.
Есть только обычный дататайп и немного сахара.
Отличие от нашего Id, как и раньше, будет заключаться в домене - не Set, а Prop.

Inductive eq (A:Type) (x:A) : A -> Prop :=
    eq_refl : x = x :>A

where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.
*)

Inductive Id {A : Type} (a : A) : A -> Type :=
  id : Id a a.

Infix "==" := Id (at level 70) : My_scope.
Notation "x /= y" := (~ (x == y)) (at level 70) : My_scope.

(* Сделаем собственные пропозициональные Or и And *)

Inductive And (A B : Prop) : Prop :=
  conj' : A -> B -> And A B.

Implicit Arguments conj'.

Inductive Or (A B : Prop) : Prop :=
  inl' : A -> Or A B
| inr' : B -> Or A B.

Implicit Arguments inl'.
Implicit Arguments inr'.

Infix "/.\" := And (at level 80, right associativity) : My_scope.
Infix "\./" := Or (at level 85, right associativity) : My_scope.

(* И теперь Bool *)
Inductive Bool : Set :=
| true' : Bool
| false' : Bool.

(* Свой bool у нас есть, смоделируем собственную конструкцию if *)
Definition if' (C : Bool -> Set) (b : Bool) (c1 : C true') (c2 : C false') : C b :=
  match b with
    true' => c1
  | false' => c2
  end.

Section Elimination_proof.
  Variable C : Bool -> Set.
  Variable b : Bool.
  Variable c1 : C true'.
  Variable c2 : C false'.

  Theorem eliminate_if' : (if' C true' c1 c2) == c1 /.\ (if' C false' c1 c2) == c2.
  Proof.
    simpl.
    exact (conj' (id c1) (id c2)).
  Qed.
End Elimination_proof.

Definition Is_true (a : Bool) := if a then True' else False'.

Definition or' (a b : Bool) : Bool :=
  match a with
    true' => true'
  | false' => b
  end.

Definition and' (a b : Bool) : Bool :=
  match a with
    true' => b
  | false' => false'
  end.

Infix "||" := or' : My_scope. 
Infix "&&" := and' : My_scope. 

(* Первая содержательная теорема - коммутативность || *)
Theorem or_commutes : forall a b : Bool, a || b == b || a.
Proof.
  intros a b.
  case a, b.
  simpl.
  exact (id true').
  simpl.
  exact (id true').
  simpl.
  exact (id true').
  simpl.
  exact (id false').
Qed.
(* То же можно доказать про * *)

(* Empty set *)
(* Это, по сути, то же самое, что встроенный False, только не из Prop, а из Set. -- необитаемый тип *)
Inductive Empty : Set :=.

(* Числа Пеано *)
Inductive Nat : Set :=
| zero : Nat
| succ : Nat -> Nat.

Fixpoint natrec
         (C : Nat -> Set)
         (d : C zero)
         (e : forall (x:Nat) (y:C x), C (succ x)) (n : Nat)
  : C n :=
  match n with
    zero => d
  | succ n' => e n' (natrec C d e n')
  end.

Definition plus' (n m : Nat) : Nat :=
  natrec (fun _ => Nat) n (fun _ y => succ y) m.

Definition mul' (n m : Nat) : Nat :=
  natrec (fun _ => Nat) zero (fun _ y => plus' y n) m.

Infix "+" := plus' : My_scope.
Infix "*" := mul' : My_scope.

(* Докажем пару классных теорем про чиселки *)
Theorem zero_neutral_right : forall n : Nat, n + zero == n.
Proof.
  intros n.
  unfold plus'.
  simpl.
  exact (id n).
Qed.

(* Это было просто, видимо, тут будет так же просто, верно? А вот не совсем! *)
Theorem zero_neutral_left : forall n : Nat, zero + n == n.
Proof.
  intros n.
  unfold plus'.
  elim n.
  (* base *)
  simpl.
  exact (id zero).
  (* shift *)
  intros n0.
  intros ind_hypo.
  simpl.
  rewrite ind_hypo.
  exact (id (succ n0)).
Qed.

(* Нам пришлось воспользоваться индукцией (правило elim), чтобы доказать это утверждение. Это из-за устройства функции natrec: она матчится по второму аргументу, поэтому, если второй аргумент равен 0, то ее можно легко упростить. *)

(* Теперь теоремка повеселее. *)
Theorem plus'_commutes : forall n m, n + m == m + n.
Proof.
  intros n m.
  elim n.
  (* base *)
  simpl.
  exact (zero_neutral_left m).
  (* shift *)
  unfold plus'.
  intros n0.
  intros ind_hyp_n.
  simpl.
  rewrite <- ind_hyp_n.
  elim m.
  (* base *)
  simpl.
  exact (id (succ n0)).
  (* shift *)
  intros n1.
  intros ind_hyp_m.
  simpl.
  rewrite ind_hyp_m.
  exact (id (succ (succ (n0 + n1)))).
Qed.

(* HW: Ассоциативность сложения *)
Theorem plus'_associates : forall a b c, (a + b) + c == a + (b + c).
Proof.
  admit.
Qed.

(* HW: Коммутативность умножения *)
Theorem mul'_commutes : forall a b, a * b == b * a.
Proof.
  admit.
Qed.

(* HW: Дистрибутивность умножения по отношению к сложению *)
Theorem mul'_distributes_over_plus' : forall a b c, a * (b + c) == a * b + a * c.
Proof.
  admit.
Qed.

(* Простые пары *)
Inductive andS (A B : Set) : Set :=
  conjS : A -> B -> andS A B.

Definition fst (A B : Set) (p : andS A B) :=
  match p with conjS a _ => a end.

Definition snd (A B : Set) (p : andS A B) :=
  match p with conjS _ b => b end.

(* П-типы *)
Inductive Pi (A : Set) (B : A -> Set) : Set :=
  lambda : (forall x : A, B x) -> Pi A B.

Definition apply' (A : Set) (B : A -> Set) (g : Pi A B) (a : A) : B a :=
  match g with
    lambda f => f a
  end.

(* Мы умеем делать синтаксический сахар для наших конструкций *)

Notation "A ~> B" := (Pi A (fun _ => B)) (at level 90, right associativity) : My_scope.
Notation "~' A" := (A ~> Empty) (at level 75, right associativity) : My_scope.

Definition lambda' (A:Set) (B:Set) (f: forall a: A, B) : A ~> B :=
  lambda A (fun _ => B) f.

Definition apply'' (A:Set) (B:Set) (g: A ~> B) (a : A) : B :=
  apply' A (fun _ => B) g a.

(* Теперь докажем, что тип A -> ~~A обитаем! *)
Theorem remove_double_not_inhabitable : forall A : Set, A ~> ~'~'A.
Proof.
  intros A.
  exact (lambda' A (~'~'A)
                 (fun x => lambda' (~'A) Empty
                                  (fun y => apply'' A Empty y x))).
Qed.
(* Да, мы просто переписали Мишину конструкцию и все получилось! *)

(* + - тип *)
Inductive orS (A B : Set) : Set :=
| inlS : A -> orS A B
| inrS : B -> orS A B.

Definition when
           (A B : Set)
           (C : orS A B -> Set) 
           (p : orS A B)
           (f : forall x:A, C (inlS A B x))
           (g : forall y:B, C (inrS A B y)) : C p
  := match p with
       inlS a => f a
     | inrS b => g b
     end.

(* Sigma - тип *)
(*
На самом деле, в Coq есть сигма-тип, но на Prop-ах. Только он не встроен в язык,
как forall, а определяется через него следующим образом:

Inductive ex (A:Type) (P:A -> Prop) : Prop :=
  ex_intro : forall x:A, P x -> ex (A:=A) P.

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Мы сделаем сейчас то же самое, только Type и Prop поменяем на Set - это будет сигма-типа
*)

Inductive Sigma (A : Set) (B : A -> Set) : Set :=
  pair : forall a : A, forall b : B a, Sigma A B.

Definition split'
           (A : Set)
           (B : A -> Set)
           (C : Sigma A B -> Set)
           (d : forall a:A, forall b:B a, C (pair A B a b))
           (p : Sigma A B) : C p
  := match p with
       pair a b => d a b
     end.

Definition fst' (A : Set) (B : A -> Set) (p : Sigma A B) : A :=
  split' A B (fun _ => A) (fun x _ => x) p.

Definition snd' (A : Set) (B : A -> Set) (p : Sigma A B) : B (fst' A B p) :=
  split' A B (fun x => B (fst' A B x)) (fun _ y => y) p.

(*
Мы знаем о таком утверждении на кванторах: forall x, ~(P x) -> ~(exists x, P x)
Докажем такое утверждение для П и ∑ типов: если тип П(A, [x] ¬B(x)) обитаем, то каждому его
элементу можно привести в соответствие элемент типа ¬∑(A, B). 
*)

(* HW: Правило замены кванторов для П и ∑-типов *)
Theorem forall_exists :
  forall (A:Set) (B : A -> Set),
    (Pi A (fun x => ~'(B x))) ~> ~'(Sigma A B).
Proof.
  admit.
Qed.

(* Списки *)
(*
Списки есть в стандартной библиотеке Coq. Списки имеют 2 конструктора: nil и cons.
Однако, мы сделаем свои
 *)
Inductive List (A : Set) : Set :=
| nil' : List A
| cons' : A -> List A -> List A.

(* Дефолтный Head в Coq принимает аргумент default на случай пустого списка. *)
Definition head (A : Set) (def : A) (l : List A) : A :=
  match l with
    nil' => def
  | cons' x xs => x
  end.

(* Можно также написать head, который возвращает Maybe A *)
Inductive Maybe (A : Set) : Set :=
  Nothing : Maybe A
| Just : A -> Maybe A.

Definition head' (A : Set) (l : List A) : Maybe A :=
  match l with
    nil' => Nothing A
  | cons' x xs => Just A x
  end.

(* Однако только в Coq (и подобных ему языках) можно сделать никогда не падающий head,
принимающий доказательство непустоты списка *)
(* HW: Написать всегда работающий head со следующей сигнатурой *)
Definition head'' (A : Set) (l : List A) (pr : l /= nil' A) : A.
Proof.
  admit.
Qed.

Definition tail (A : Set) (l : List A) : List A :=
  match l with
    nil' => nil' A
  | cons' x xs => xs
  end.

Fixpoint foldr
         (A : Set)
         (C : List A -> Set)
         (c : C (nil' A))
         (e : forall (x:A) (y:List A) (z:C y), C (cons' A x y))
         (l : List A) : C l
  := match l with
       nil' => c
     | cons' a l' => e a l' (foldr A C c e l')
     end.

(*
Наконец пошла нормальная теория.
Сейчас мы введем множество абстрактных математических понятий насчет отношений.
Из этих очень абстрактных понятий мы сможем вывести массу полезнейших утверждений.
*)

(* Введем понятие *отношения* над множествами *)
Section Relation_definitions.
  Variable A : Type.
  Definition Relation (S : Type) := S -> S -> Prop.
  Variable R : Relation A.

  (* Определим основные свойства отношений, которые нам нужны *)
  Section General_Properties_of_Relations.
    Definition reflexive : Prop := forall x:A, R x x.
    Definition transitive : Prop := forall x y z:A, R x y -> R y z -> R x z.
    Definition symmetric : Prop := forall x y:A, R x y -> R y x.
    Definition antisymmetric : Prop := forall x y:A, R x y -> R y x -> x == y.
    
    (* Определение отношения эквивалентности *)
    Definition equiv := reflexive /.\ transitive /.\ symmetric.
  End General_Properties_of_Relations.

  Section Meta_relations.
    (* Определение отношения "меньше" (включения) на отношениях *)
    Definition inclusion (R1 R2: Relation A) : Prop := forall x y:A, R1 x y -> R2 x y.

    (* Равенство отношений *)
    Definition equal_rels (R1 R2: Relation A) : Prop := inclusion R1 R2 /.\ inclusion R2 R1.

  End Meta_relations.

End Relation_definitions.

(* Экстенциональность функции - очень классное свойство, которое позволяет сохранять
отношение эквивалентности между элементами при их отображении куда-то *)
Section Extensionality_definition.
  Variable A B : Type.
  Variable R1 : Relation A.
  Variable R2 : Relation B.
  
  Definition extensional (f:A -> B) := forall x y:A, R1 x y -> R2 (f x) (f y).

End Extensionality_definition.

(*
HW: Доказать следующую теорему:
Минимальное рефлексивное отношение
а) является отношением эквивалентности
б) таково, что для любого множества B и отношения эквивалентности на нем R2 любая функция f: A -> B экстенциональна по отношению к нашему отношению и отношению R2.
*)
Section Theorem_about_minimal_relations.
  Variable A : Type.
  Variable R : Relation A.
  Hypothesis reflR : reflexive A R.
  Hypothesis minR : forall S : Relation A, reflexive A S -> inclusion A R S.

  Theorem min_refl_rel_is_equiv :
    equiv A R /.\ 
    forall (B:Type) (R2:Relation B), equiv B R2 -> forall f:A -> B, extensional A B R R2 f.
  Proof.
    admit.
  Qed.
End Theorem_about_minimal_relations.

(* 
HW: Доказать, что отношения равенства отношений является отношением эквивалентности
Хинт: докажите несколько лемм про более простые свойства отношений inclusion и equal_rels 
*)
Theorem rels_equality_is_equivalence : forall T:Type, equiv (Relation T) (equal_rels T).
Proof.
  admit.
Qed.
