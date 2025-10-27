(*********************************************)
(**       Zadanie k prednáške 3             **)

(*        Import potrebných knižníc         *) 

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.


(*-------------------------------------------*)
(** Úlohy: typ - dvojica prirodzených čísel  *)
(*-------------------------------------------*)

(*-------------------------------------------*)
(* --- Pracujeme v module natpair --- *)
Module natpair.


Fixpoint length (l:natlist) : nat := 
match l with 
| [] => 0
| head :: tail => 1 + (length tail)
end.

Fixpoint append (l1 l2: natlist) : natlist :=
match l1 with
| [] => l2
| head::tail => head::(append tail l2)
end.


Notation "x ++ y" := (append x y) 
                     (at level 60, right associativity). 


Definition head (l: natlist) (default:nat) : nat := 
match l with
| [] => default
| h::t => h
end.


Definition tail (l: natlist) : natlist := 
match l with
| [] => nil
| h::t => t
end.

Fixpoint reverse l:natlist :=
match l with 
| [] => []
| hd::tl => (reverse tl)++[hd]
end.


(* --- Úlohy ---  *)

(** Úloha 3 ★: 
  Úloha: 
  Doplňte definíciu funkcie alternate, 
  ktorá prepletie dva zoznamy do jedného – 
  striedavo berie prvky z prvého a druhého zoznamu.

  Príklad:
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].

  Poznámka:
  - Niektoré prirodzené zápisy tejto funkcie 
    nespĺňajú požiadavku štrukturálnej rekurzie.
  - V takomto prípade sa pokúste použiť pattern matching nad 
    oboma zoznamami naraz pomocou viacnásobného vzoru 
    ("multiple pattern matching").
*)

Fixpoint alternate (l1 l2 : natlist) : natlist.
Admitted.


Example test_oddmembers :
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. Admitted.

(** Úloha 7 ★★:
  Úloha: Doplnte definíciu funkcie [countoddmembers], ktorá 
  spočíta počet nepárnych čísel v zozname.

  Použite už definovanú funkciu [oddmembers] a funkciu [length], 
  namiesto písania vlastnej rekurzie.

  Príklady:
    countoddmembers [1;0;3;1;4;5] = 4.
    countoddmembers [0;2;4] = 0.
    countoddmembers [] = 0.
*)

Definition countoddmembers (l : natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1 :
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. Admitted.

Example test_countoddmembers2 :
  countoddmembers [0;2;4] = 0.
Proof. Admitted.


(** Úloha 8 ★★★:
  Úloha: Dokážte, že každá involutívna funkcia je injektívna.

  Involúcia je funkcia f : nat → nat, ktorá po aplikovaní dvakrát
  vráti pôvodný prvok, t.j. f(f(n)) = n pre všetky n.

  Injektívna funkcia (one-to-one) je taká, že rôzne vstupy 
  mapuje na rôzne výstupy – žiadne "kolízie".

  Formálne:
    ∀ (f : nat → nat),
      (∀ n : nat, f (f n) = n) →
      (∀ n1 n2 : nat, f n1 = f n2 → n1 = n2).
*)

Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) ->
    (forall m n : nat, f m = f n -> m = n).
Proof.
Admitted.


(** Úloha 9 ★★:
  Úloha: Dokážte, že funkcia reverse je injektívna.  

  Nepoužívajte indukciu (to by bolo komplikované) 
  – použite rovnakú techniku ako pri predchadzajúcom 
  dôkaze. 
  - Využite aj dôkazy o zoznamoch z prednášky 
    (skopirujte ich pred dôkaz). 

  (Pozor: nemôžete použiť priamo predchádzajúcu 
  úlohu ako vetu, typy sú iné.)
*)

Theorem reverse_injective : forall (l1 l2 : natlist),
  reverse l1 = reverse l2 -> l1 = l2.
Proof.
Admitted.




Check list.          (* list : Type -> Type *)

(**
  Parameter X v definícii list sa automaticky stáva parametrom 
  konštruktorov nil a cons — teda nil a cons sú teraz 
  polymorfné konštruktory.  

  Keď ich používame, musíme im ako prvý argument 
  poskytnúť typ prvkov zoznamu, ktorý konštruujeme.
*)

(* Polymorfné konštruktory *)
Check nil.       (* forall X : Type, list X *)
Check cons.      (* forall X : Type, X -> list X -> list X *)

(* Príklady *)
Check nil nat.        
(* prázdny zoznam typu nat *)

Check cons nat 1 (cons nat 2 (nil nat)).  
(**
  Povinnosť zadávať typový argument pri každom použití 
  konštruktora zoznamu je dosť zaťažujúca;
  čoskoro uvidíme spôsoby, ako túto potrebu anotácie znížiť.
*)

(** Definujme polymorfnú funkciu repeat *)
Fixpoint repeat (X:Type) (a:X) (count : nat): list X :=
match count with
| 0 => nil X
| S m => cons X a (repeat X a m) 
end.

Compute repeat bool true 5.

Compute repeat nat 1 5.

(** Odvodenie typovej anotácie *)
(* Definujme funkcie repeat bez explicitnej typovej anotácie *)

Fixpoint repeat' X a count: list X :=
match count with
| 0 => nil X
| S m => cons X a (repeat' X a m) 
end.

Check repeat'.

(* Automatické odvodzovanie implicitných typových argumentov *)
Fixpoint repeat'' X a count: list X :=
match count with
| 0 => nil _
| S m => cons _ a (repeat'' _ a m) 
end.

Check repeat''.

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).
Check list123'.

(** Implicitné argumenty

  Je možné vyhnúť sa písaniu _ vo väčšine prípadov tak, 
  že Rocq vždy odvodí typový argument danej funkcie.

  Príkaz Arguments špecifikuje názov funkcie (alebo konštruktora)
  a potom zoznam argumentov, ktoré sa majú považovať za implicitné,
  každý uzavretý do zložených zátvoriek.
*)

(* Nastavenie implicitných argumentov pre konštruktory zoznamu *)
Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

(**
  Teraz nemusíme poskytovať žiadne typové argumenty vôbec:
*)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(**
  Alternatívne môžeme deklarovať argument ako implicitný
  priamo pri definícii funkcie, 
  tým že ho uzavrieme do zložených zátvoriek 
  namiesto zátvoriek obyčajných.
*)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

(**
  Poznámka: ani pri rekurzívnom volaní funkcie repeat'''
  nemusíme poskytovať typový argument. 
  V skutočnosti by bolo nesprávne ho uviesť,
  pretože Rocq ho neočakáva.

  Tento štýl budeme používať vždy, keď je to možné, ale
  naďalej budeme používať explicitné deklarácie Arguments pre
  konštruktory induktívnych typov.  

  Dôvod je, že označenie parametra induktívneho typu ako implicitného
  spôsobí, že sa stane implicitným pre samotný typ, 
  nielen pre jeho konštruktory.
*)
(* Pri takomto prístupe vzniká jeden menší problém. 
   Rocq niekedy nemá dostatok informácii na odvodenie typu *)

Fail Definition mynil := nil nat.

Definition mynil : list nat := nil.
Definition mynil' := @nil nat.


(** Definícia polymorfnej funkcie pre spajanie zoznamov *)

Fixpoint append {X:Type} (l1 l2: list X) : list X := 
match l1 with
| nil => l2 
| cons x xs => cons x (append xs l2)
end.

Compute append (cons 2 nil) (cons 1 nil).

(**
  Napríklad, alternatívna definícia typu zoznamu:

  Inductive list' {X:Type} : Type :=
    | nil'
    | cons' (x : X) (l : list').

  Pretože X je deklarované ako implicitné 
  pre celú induktívnu definíciu vrátane list',
  teraz je nutné písať len list', 
  či už hovoríme o zoznamoch čísel, pravdivostných hodnôt
  alebo čomkoľvek inom, namiesto list' nat alebo list' bool. 
*)


(** Zavedenie štandardnej notácie pre zoznamy*)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (append x y)
                     (at level 60, right associativity).

Check [1].
Compute [1;2]++[3;5;6].

(*===========================================*)
(*           Polymorfná verzia pair          *)

Inductive product (X:Type) (Y:Type): Type :=
| pair (m:X) (n:Y).

Check pair nat bool 3 true.
Check pair _ _ 3 true.

(* Nastavenie implicitných argumentov *)
Arguments pair {X} {Y}.

Check pair 3 true.

(* Zavedieme štandardnú notáciu pre dvojicu *)
Notation "( x , y )" := (pair x y).

(* Zavedieme štandardnú notáciu pre typ dvojica *)
Notation "X * Y" := (product X Y) : type_scope.

Check product. 
Check pair 3. 
Check pair 3 true. 
(* (3, true) : product  *)

Definition fst {X Y: Type} (p: X * Y): X := 
match p with
| (x, y) => x
end.

Check fst.


Definition snd {X Y: Type} (p: X * Y): Y := 
match p with
| (x, y) => y
end.

Check snd.

Compute (fst (1,true)).
Compute (snd (1,true)).
Compute (fst ((false,5),true)).
Compute (fst (1,true)).

Definition swap {X Y : Type} (p: X * Y): Y * X :=
match p with 
| (x,y) => (y,x)
end. 

Theorem swap_swap_p:
  forall {X Y: Type} (p: X*Y), p = swap (swap p).
Proof.
intros.
destruct p.
simpl.
reflexivity.
Qed.


(*===========================================*)
(*         Polymorfná verzia option          *)
(**
  Posledným polymorfný typ v rámci tejto prednášky 
  bude polymorfný option, ktorý zovšeobecňuje natoption 
  z predchádzajúcej časti. 

  (Definíciu umiestňujeme do modulu, pretože štandardná 
  knižnica už definuje option a práve túto použijeme 
  nižšie pri redefinícii funkcie nth_error.)
*)

Module PolymorphicOption.

  (* Polymorfná definícia option *)
  Inductive option (X: Type) : Type :=
    | Some (x : X)
    | None.

  (* Nastavenie implicitného argumentu *)
  Arguments Some {X}.
  Arguments None {X}.

End PolymorphicOption.

(* Polymorfná verzia funkcie nth_error *)

Fixpoint nth_error {X:Type} (l:list X) (n:nat): option X := 
match l with
| []     => None
| hd::tl => match n with
           | 0    => Some hd
           | S m  => nth_error tl m end
end.

Compute nth_error [] 4.
Compute nth_error [10;12;0] 1.
Compute nth_error [10;12;0] 2.
