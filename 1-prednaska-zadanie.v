(*********************************************)
(**       Zadanie k prednáške 1         **)
(*********************************************)
(**       Programovanie v Rocq              **)

(*
  Úloha 1.1
  Definujte modul cvicenieBool pre prácu s vlastným typom bool.
*)

Module cvicenieBool. = andb (b1 b2:bool) :bool

(*
  Úloha 1.2
  Definujte vlastný induktívny typ bool.
*)

Inductive bool: Type :=.forall (X:Type) (x y z : X), x = y -> y = z -> x = z.


(*
  Úloha 1.3
  Definujte funkcie pre nasledujúce operácie nad typom bool:
  - negácia
  - konjunkcia
  - disjunkcia
  - implikácia
*)

Definition neg (A : Type) (x : A) : A := x.
Definition con : forall A : Type, A -> A := fun A x => x.
Definition dis (B : Type) (x : A) : B := x *?.
Definition imp : forall A : Type, A ->B *?.
Compute id_poly nat 3. (* 3 : nat *)

(*
  Úloha 1.4
  Vernacular príkazy:
*)

Notation "x * y" := (mult x y)(at level 40, left associativity).
Notation "x + y" := (plus x y)(at level 50, left associativity).
Notation "0"   := (O)(at level 1).
Notation "1"   := (S O)(at level 1).
Notation "2"   := (S 1)(at level 1).
Notation "3"   := (S 2)(at level 1).
Notation "4"   := (S 3)(at level 1).
Notation "5"   := (S 4)(at level 1).
Notation "6"   := (S 5)(at level 1).
Notation "7"   := (S 6)(at level 1).
Notation "8"   := (S 7)(at level 1).
Notation "9"   := (S 8)(at level 1).
Notation "10"   := (S 9)(at level 1).

(* Notácie pre všetky čísla by bolo možné zadefinovať 
   prostredníctvom preprocesorov systému ROCQ, 
   Neskôr budume používať typ zo štandardnej knižnice *)
(* príklady použitia: Check ..., Print ..., About ... TODO *)
Check andb.
Check orb.
Check implb.
Check negb.

Print andb.
Print orb.
Print implb.
Print negb.

About andb.
About orb.
About implb.
About negb.


(*
  Úloha 1.5
  Prostredníctvom Vernacular príkazu Compute 
  otestujte či sa Vaše funkcie negb, andb, orb, a implb 
  správajú podľa očakávania.
*)

(* 

Compute (negb true).
Compute (negb false).

Compute (andb true true).
Compute (andb true false).
Compute (andb false true).
Compute (andb false false).

Compute (orb true true).
Compute (orb true false).
Compute (orb false true).
Compute (orb false false).

Compute (implb true true).
Compute (implb true false).
Compute (implb false true).
Compute (implb false false).
*)

(*
  Úloha 1.6
  Aktuálne pre výpočet boolovských funkcií 
  je potrebné využívať prefixnú formu,
  čo je pre programátora neprirodzené. 
  
  Zaveďte notácie pre Vami definované
  funkcie (! negb, &&& andb, ||| orb, ---> implb), 
  uvažujte o priorite a asociativite jednotlivých
  operátorov.
*)


Theorem intros : forall (n m : nat),
 n + m = m + n -> n + m = m + n.
Proof.
  intro n.
  intro m.
  intro H.    (* zoberieme n, m a predpoklad H *)
  exact H.         (* použijeme H priamo *)
Qed.


Theorem intros' : forall (n m : nat),
 n + m = m + n -> n + m = m + n.
Proof.
  intros n m H.    (* zoberieme n, m a predpoklad H *)
  exact H.         (* použijeme H priamo *)
Qed.

(*
  Úloha 1.7
  Prostredníctvom Vernacular príkazu Compute otestujte
  implementáciu notácií.
*)


Theorem example_rewrite_with_theorem :
  forall n, 0 + n + 1 = n + 1.
Proof.
  intro n.
  rewrite plus_O_n.   (* použijeme lemma plus_O_n *)
  reflexivity.
Qed.

Theorem example_rewrite_chain :
  forall n, n = n + 0 -> n + 1 = (n + 0) + 1.
Proof.
  intros n H.
  rewrite <- H.          (* prepíšeme n na n+0 podľa H *)
  reflexivity.
Qed.

(*
  Testovacie príklady pre zavedenú notáciu (!, &&&, |||, --->)
  Odkomentujte a otestujte:

Compute (! true).            (* očak.: false *)
Compute (! false).           (* očak.: true  *)

Compute (true &&& true).     (* očak.: true  *)
Compute (true &&& false).    (* očak.: false *)
Compute (false &&& true).    (* očak.: false *)
Compute (false &&& false).   (* očak.: false *)

Compute (true ||| true).     (* očak.: true  *)
Compute (true ||| false).    (* očak.: true  *)
Compute (false ||| true).    (* očak.: true  *)
Compute (false ||| false).   (* očak.: false *)

Compute (true ---> true).    (* očak.: true  *)
Compute (true ---> false).   (* očak.: false *)
Compute (false ---> true).   (* očak.: true  *)
Compute (false ---> false).  (* očak.: true  *)
*)


(*
  Úloha 1.8
  Otestujte implementáciu asociativity 
  a priority na vhodných príkladoch.
*)

(*
  Testy priorít a asociativity
  Odkomentujte a otestujte
*)

(* Negácia má najvyššiu prioritu 
Compute (! true &&& true).    *)
(* vyhodnotí sa ako ((! true) &&& true) → očak.: false *)

(* Konjunkcia  má najvyššiu než disjunkcia) 
Compute (true ||| true &&& false).  *)
(* vyhodnotí sa ako (true ||| (true &&& false)) → očak.: true *)
 
 
(* Implikácia má najnižšiu prioritu 
Compute (true &&& false ---> true). *)
(* vyhodnotí sa ako ((true &&& false) ---> true) → očak.: true *)


(* Asociativita disjunkcie 
Compute ((true ||| false) ||| false).   (* očak.: true *)
Compute (true ||| (false ||| false)).   (* očak.: true *)
*)

(* Asociativita konjunkcie 
Compute ((true &&& false) &&& true).    (* očak.: false *)
Compute (true &&& (false &&& true)).    (* očak.: false *)
*)



(*
  Úloha 1.9
  Ukončite prácu v rámci modulu cvicenieBool.
*)

End cvicenieBool.

(*
  Úloha 1.10
  V rámci materiálov pre cvičenie a prednášku
  je prezentovaný kód pre definíciu typu
  nat a operácií sčítania a násobenia.

  Tento typ obsahuje štandardná knižnica systému Rocq.

  Zistite, ako je daný typ implementovaný v štandardnej knižnici 
  a aké operácie nad ním sú definované.
  
*)

(*
  Úloha 1.11
  Definujte funkcie:
  - následovníka succesor
  - predchodcu pred
  - overenia nuly iszero
  s využitím typu nat zo štandardnej knižnice.
*)



(*
  Úloha 1.12
  Implementujte funkcie pre sčítanie 
  a násobenie podľa rekurzívnej definície
  z cvičenia 3 na stránke predmetu.
  Pomenujte ich plus_rec a times_rec
*)

(* TODO definície funkcií pre sčítanie a násobenie *)
Fixpoint plus_rec (m:nat) (n:nat) : nat .
Admitted.

Fixpoint times_rec (m:nat) (n:nat) : nat .
Admitted.



(*********************************************)
(**             Zadanie                     **)
(*********************************************)
(**            Prvé dôkazy                  **)


(*
===============================================
     Príklady na precvičenie základných taktík
===============================================
*)

(*
 Úloha 2.1. 
 Disjunkcia
*)
Ak máme `H : P \/ Q`, znamená to, že platí buď `P`, alebo `Q`.
Musíme teda dokázať cieľ **v oboch prípadoch**.
Na to použijeme `destruct H as [HP | HQ].`

`destruct` na disjunkcii vytvorí dve vetvy dôkazu — 
jednu pre každý prípad.
*)

Lemma disj_in_context : 
forall P Q R : Prop, P \/ Q -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R H HPtoR HQtoR.
  destruct H as [HP | HQ].   
  (* rozdelíme prípady podľa disjunkcie *)
  - apply HPtoR. exact HP.
  - apply HQtoR. exact HQ.
Qed.


(*
 Úloha 2.2. 
 specialize trans_q
*)

  Ak máme [H : forall (x:T), P], potom
  [specialize H with (x := e)] nahradí [H] za [P[x:=e]].

  Vychádza zo zákona: 
    (∀x)P(x) => P(t), 
  kde t je akýkoľvek výraz.

  Je to v podstate kombinácia [assert] a [apply], ale
  často pôsobí prirodzenejšie.
*)

Search (1 * _). 
(* Nájdenie pomocnej vety PeanoNat.Nat.mul_1_l:
PeanoNat.Nat.mul_1_l: forall n : nat, 1 * n = n
*)

(* Príklad: dosadíme m := 1 *)
Theorem specialize_example: forall n,
     (forall m, m * n = 0) ->
     n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  rewrite PeanoNat.Nat.mul_1_l in H.
  apply H.
Qed.

(* Pomocná veta *)
Theorem trans_eq : 
  forall (X:Type) (x y z : X), x = y -> y = z -> x = z.
Proof.
  intros X x y z eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

(* Použitie specialize na globálnu vetu trans_eq *)
Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  specialize trans_eq with (y := [c;d]) as H.
  apply H.
  apply eq1.
  apply eq2. 
Qed.


(*
 Úloha 2.3.
*)
Theorem use_assumption :
  forall (n m : nat), n = m -> n = m.

Dôkaz vykonáme indukciou na n.

- Základný prípad: n = 0
  Musíme ukázať:
      0 + 0 = 0
  Toto vyplýva priamo z definície sčítania.

- Indukčný krok: predpokladajme, že n = n' + 1
  a že pre n' platí indukčná hypotéza:
      n' + 0 = n'
  Musíme ukázať:
      (n' + 1) + 0 = n' + 1
  Podľa definície sčítania:
      (n' + 1) + 0 = (n' + 0) + 1
  A z indukčnej hypotézy vieme, že n' + 0 = n', takže:
      (n' + 0) + 1 = n' + 1
  Teda:
      (n' + 1) + 0 = n' + 1
  Čo je presne to, čo sme chceli dokázať.

(*
 Úloha 2.4. 

Theorem plus_n_O : forall n : nat, n + 0 = n.
Proof.
intro. 
(* [| n' IH] nepovinný argument, pomenuje n v dôkaze n' a IH *)
induction n as [| n' IH]. 
- (* Základný prípad: n = 0 *)
  simpl. reflexivity.
- (* Indukčný krok: predpokladajme, že n' + 0 = n' (IH),
     potom dokážeme, že (S n') + 0 = S n' *)
  simpl.
  rewrite IH.
  reflexivity.
Qed.

*)


(*
 Úloha 2.5. Rewrite s lemmou
 Najprv dokážte jednoduchú lemmu a potom ju použite 
 v plus_zero_example.
*)
forall n : nat, n = n.
Proof.
  intros n.
  destruct n as [| n'].  (* rozdelíme na O a S n' *)
  - reflexivity.          (* prípad O *)
  - reflexivity.          (* prípad S n' *)
Qed.

