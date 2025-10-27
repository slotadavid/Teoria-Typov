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

(*- Definícia typu a príslušných operácií -  *)

Inductive natpair: Type :=
| pair (n m :nat).
Notation "( x , y )" := (pair x y).

Definition fst (x: natpair) : nat := 
match x with
| (m, n) => m
end.

Definition snd (x: natpair) : nat := 
match x with
| (m, n) => n
end.

Definition swap (p : natpair) : natpair :=
match p with
| pair m n => pair n m 
end. 

(*- Úlohy:                                     -  *)

(** Úloha 1 ★: 
    Dokážte, že snd a fst vymenia poradie prvkov. *)
Theorem snd_fst_is_swap : forall (p : natpair),
  (snd p, fst p) = swap p.
Proof.
Admitted. 

(** Úloha 2 ★: Dokážte, 
            že fst po operácii swap je rovné snd. *)
Theorem fst_swap_is_snd : forall (p : natpair),
  fst (snd p, fst p) = snd p.
Proof.
Admitted.


End natpair.

(*-------------------------------------------*)
(** Úlohy: typ zoznam prirodzených čísel     *)
(*-------------------------------------------*)

(* --- Pracujeme v module matlist --- *)
Module natlist.

(*- Definícia typu a príslušných operácií -  *)
Inductive natlist : Type :=
| nil
| cons (n: nat) (l:natlist).

Check (nil).
Check (cons 1 (cons 3 nil)).

(* Zavedenie štandardnej notácie *)

Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "x :: l" := (cons x l) 
                     (at level 60, right associativity).

(* Funkcie z prednášky *)

Fixpoint repeat (n count :nat) : natlist := 
match count with
| 0 => []
| S m => n :: (repeat n m)
end.

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


(** Testy *)

Example test_alternate1 :
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. Admitted.

Example test_alternate2 :
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. Admitted.

Example test_alternate3 :
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. Admitted.

Example test_alternate4 :
  alternate [] [20;30] = [20;30].
Proof. Admitted.

(** Úloha 4 ★: 
  Úloha: Doplnte definíciu funkcie sum, ktorá 
  zráta prvky zoznamu. 
  Pri prázdnom zozname vráti hodnotu 0.

  Príklad:
    sum [] = 0.
    sum [1;2;3;4;5] = 15.
*)

Fixpoint sum (l:natlist) : nat .
Admitted.

Example test_sum :
  sum [1;5;4] = 10.
Proof. Admitted.


(** Úloha 5 ★★:
  Úloha: Doplnte definíciu funkcie [nonzeros], ktorá 
  z daného zoznamu odstráni všetky nuly.

  Príklad:
    nonzeros [0;1;0;2;3;0;0] = [1;2;3].
*)

Fixpoint nonzeros (l : natlist) : natlist .
Admitted.

Example test_nonzeros :
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. Admitted.

(** Úloha 6 ★★:
  Úloha: Doplnte definíciu funkcie [oddmembers], ktorá 
  z daného zoznamu vyberie iba nepárne čísla.

  Príklad:
    oddmembers [0;1;0;2;3;0;0] = [1;3].
*)

Print odd.

Fixpoint oddmembers (l : natlist) : natlist .
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




End natlist.
                        

(*---------------------------------------------*)
(** Úlohy: polymorfné funkcie vyššieho rádu    *)
(*---------------------------------------------*)


(**  
Preštudujte si našu definíciu funkcie fold 
z 2 prednášky, porovnajte ju s funkciami 
zo štandardnej knižnice:
- fold_left
- fold_right
a pouvažujte nad rozdielom.*)
Print fold_left.
Print fold_right.

(** Úloha 10 ★★:
  Úloha: Definujte funkciu sum_list, využitím fold_right 
  ktorá zráta všetky prvky zoznamu prirodzených čísel.

  Príklady:
    sum_list [1;2;3;4;5] = 15
    sum_list [] = 0
*)

Compute fold_left plus [1;2;3] 0.

Compute fold_right plus 0 [1;2;3].

Definition sum_list (l : list nat) : nat .
Admitted. 


Example test_sum_list1: sum_list [1;2;3;4;5] = 15.
Proof.
Admitted.

Example test_sum_list2: sum_list [] = 0.
Proof.
Admitted.


(** Úloha 11 ★★:
  Úloha: 
  Definujte funkciu product_list, využtím fold_left, 
  ktorá vypočíta súčin všetkých prvkov 
  zoznamu prirodzených čísel. 

  Príklady:
    product_list [1;2;3;4] = 24
    product_list [] = 1
*)


Definition product_list (l : list nat) : nat .
Admitted.


Example test_product_list1: product_list [1;2;3;4] = 24.
Proof.
Admitted.

Example test_product_list2: product_list [] = 1.
Proof.
Admitted.

(** Úloha 12 ★★:
  Úloha: Definujte funkciu filter_even_gt7,
  ktorá zo zoznamu prirodzených čísel vyberie prvky, 
  ktoré sú párne a zároveň väčšie ako 7.

  Príklady:
    filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
    filter_even_gt7 [5;2;6;19;129] = [].
*)
 

Definition filter_even_gt7 (l : list nat) : list nat .
Admitted.


Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof.
Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof.
Admitted.


(** Úloha 13 ★★★:
  Úloha: Definujte partition, ktorá 
  rozdelí zoznam podľa predikátu.

  Funkcia má tvar (signatúru):
    partition : ∀ X : Type, 
            (X → bool) → list X → (list X * list X)

  Výstupom je dvojica zoznamov, kde:
    - prvý obsahuje prvky, ktoré test spĺňajú,
    - druhý obsahuje prvky, ktoré test nespĺňajú.

  Poradie prvkov v oboch zoznamoch by malo zostať rovnaké 
  ako v pôvodnom zozname.

  Príklady:
    partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
    partition (fun x => false) [5;9;0] = ([], [5;9;0]).
*)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X .
Admitted.


Example test_partition1: 
partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof.
Admitted.

Example test_partition2: partition 
        (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof.
Admitted.


(** Úloha 14 ★★:
Úloha: Dokážte, že map distribuuje 
cez spojenie zoznamov (++).

Formálne platí:
∀ (X Y : Type) (f : X → Y) (l1 l2 : list X),
map f (l1 ++ l2) = (map f l1) ++ (map f l2)
*)

Lemma map_app : 
forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof. 
Admitted.


(** Úloha 15 ★★★:
  Úloha: Dokážte, že map a rev komutujú.  
  
  Poznámka:
  Môžete použiť vetu z predchadzajúcej úlohy.

  Formálne platí:
    ∀ (X Y : Type) (f : X → Y) (l : list X),
      map f (rev l) = rev (map f l)
*)

Theorem map_rev : 
        forall (X Y : Type) (f : X -> Y) (l : list X),
                map f (rev l) = rev (map f l).
Proof.
Admitted.


(** Úloha 16 ★★:
  Úloha: Definujte funkciu flat_map, 
  ktorá je analogická funkcii [map],
  ale namiesto jedného výsledku typu Y 
  pre každý prvok, vráti zoznam typu list Y.
  Výsledné zoznamy sa spoja do jedného zoznamu.

  Príklad:
    flat_map (fun n ⇒ [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12]
*)

Fixpoint flat_map {X Y: Type} 
  (f: X -> list Y) (l: list X): list Y .
Admitted.


Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
  Proof. 
  Admitted.
  



