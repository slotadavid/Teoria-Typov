(*********************************************)
(**       Zadanie k prednáške 4             **)
(*********************************************)

(*        Import potrebných knižníc         *) 

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.PeanoNat.
Require Import Init.Nat.
Require Import Stdlib.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(*-------------------------------------------*)
(** Úlohy:                                   *)
(*-------------------------------------------*)


(; (bodkočiarka)
  - aplikuje druhú taktiku na všetky vetvy po destruct

*)


(**
===========================================
      MAPA TAKTÍK – VIZUÁLNY PREHĽAD
===========================================

Cieľom je vedieť rýchlo určiť, KTORÚ taktiku
použiť v danej situácii.

────────────────────────────────────────────
1  PRÁCA S ROVNOSŤAMI
────────────────────────────────────────────
        +----------------------+
        |  Potrebujem dokázať  |
        |     x = y            |
        +----------------------+
                 │
                 ▼
     ┌────────────────────────────┐
     │ obe strany rovnaké →       │ reflexivity
     │ známa rovnosť H : x = y →  │ apply H
     │ opačný smer →              │ symmetry
     │ cez medzičlánok →          │ transitivity
     │ konštruktor rovnaký →      │ injection
     │ konštruktor rôzny →        │ discriminate
     │ chcem nahradiť v kontexte →│ subst
     └────────────────────────────┘

────────────────────────────────────────────
2  SPORY A KONTRADIKCIE
────────────────────────────────────────────
        +----------------------+
        |  V kontexte mám      |
        |  spor (False, P ∧ ¬P)|
        +----------------------+
                 │
                 ▼
     ┌────────────────────────────┐
     │ logický spor →             │ contradiction
     │ nemožná rovnosť (S n = O) →│ discriminate
     │ z False dokážem čokoľvek → │ destruct H
     └────────────────────────────┘

────────────────────────────────────────────
3  PRÁCA S KONTEXTOM
────────────────────────────────────────────
        +----------------------+
        |  Chcem upraviť alebo |
        |  použiť hypotézu     |
        +----------------------+
                 │
                 ▼
     ┌────────────────────────────┐
     │ zjednodušiť výraz →        │ simpl / simpl in H
     │ aplikovať implikáciu →     │ apply ... in
     │ konkretizovať ∀ →          │ specialize H with (...)
     │ rozbaliť definíciu →       │ unfold názov
     │ rozdeliť tvar →            │ destruct ... eqn:
     │ vrátiť premennú do cieľa → │ revert
     │ zmeniť poradie pre indukciu│ generalize dependent
     └────────────────────────────┘
────────────────────────────────────────────
4  LOGICKÉ SPOJKY (Prop)
────────────────────────────────────────────
        +----------------------+
        |  Cieľ alebo hypotéza  |
        |  má tvar P /\ Q , P \/ Q , ∃ x, P x, ~P |
        +----------------------+
                 │
                 ▼
     ┌────────────────────────────┐
     │ P /\ Q →                   │ split / destruct
     │   • cieľ: split.           │ rozdelí P /\ Q na P a Q
     │   • hypotéza H: destruct H │ H : P /\ Q → H1 : P, H2 : Q
     │     as [HP HQ].            │
     ├────────────────────────────┤
     │ P \/ Q →                   │ left / right / destruct
     │   • cieľ: vyber stranu:    │
     │           left. apply HP.  │
     │   • hypotéza H:            │
     │    destruct H as [HP | HQ].│
     ├────────────────────────────┤
     │ ∃ x, P x →                 │ exists / destruct
     │   • cieľ:                  │
     │       exists t; apply ...  │
     │   • hypotéza H:            │ 
     │     destruct H as [x Hx].  │
     ├────────────────────────────┤
     │ P -> Q →                   │ intros / apply
     │   • cieľ:                  │
     │        intros HP; apply H. │
     │   • hypotéza H:            │
     │        apply H in HP.      │
     ├────────────────────────────┤
     │ ~P (P -> False) →          │ intros; destruct
     │   • cieľ: intros HP;       │
     │           destruct HP      │
     │   • hypotéza H :           │ 
     │       ~P → apply H in HP   │
     ├────────────────────────────┤
     │ False →                    │ contradiction / destruct
     │   • hypotéza H :           │
     │      False → contradiction │
     │   • z False možno          │
     │     dokázať čokoľvek       │
     └────────────────────────────┘

────────────────────────────────────────────
PRÍKLADY:
────────────────────────────────────────────
1) Existencia v kontexte:
   H : ∃ x, P x
   → destruct H as [x Hx]. (* Hx : P x *)

2) Existencia v cieli:
   Goal: ∃ x, P x
   → exists t. (* t je konkrétny kandidát *)
   → apply H.  (* ak máme dôkaz P t *)

3) Negácia / absurdum:
   H : P /\ ~P
   → destruct H as [HP HnP].
   → contradiction. (* logický spor *)

4) Hypotéza False:
   H : False
   → contradiction. 
   (* z False možno dokázať čokoľvek *)


────────────────────────────────────────────
5  STRATÉGIA DÔKAZU
────────────────────────────────────────────
   • **Backward reasoning** – začni od cieľa
       (apply, transitivity, symmetry, intros)

   • **Forward reasoning** – začni z hypotéz
       (apply ... in, specialize, simpl in)

   • **Reorganizácia dôkazu**
       (assert, revert, generalize dependent)

   • **Riadenie vetiev**
       (destruct ... eqn:, ;, repeat)

   • **Automatické riešenie sporu**
       (discriminate, contradiction)

   • **Rozbalenie a analýza**
       (unfold, induction)
*)


(** Úloha 10 ★  
    Dokážte tranzitivitu `eqb`: ak `n =? m = true` a `m =? p = true`,
    potom `n =? p = true`. *)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof. Admitted.


(** Úloha 11 ★  
    Dokážte, že ak `filter test l = x :: lf`, tak `test x = true`. *)
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof. Admitted.


(** Úloha 12 ★  
    Dokážte, že ak `n + m = 0`, potom `n = 0` a `m = 0`. *)
Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof. Admitted.


(** Úloha 13 ★  
    Dokážte komutatívnosť konjunkcie: `P /\ Q -> Q /\ P`. *)
Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof. Admitted.


(** Úloha 14 ★  
    Dokážte asociativitu konjunkcie: `P /\ (Q /\ R) -> (P /\ Q) /\ R`. *)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof. Admitted.


(** Úloha 15 ★  
    Dokážte, že ak `n * m = 0`, potom `n = 0 \/ m = 0`. *)
Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof. Admitted.


(** Úloha 16 ★  
    Dokážte komutatívnosť disjunkcie: `P \/ Q -> Q \/ P`. *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof. Admitted.


(** Úloha 17 ★  
    Dokážte kontrapozíciu: `(P -> Q) -> (~Q -> ~P)`. *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof. Admitted.


(** Úloha 18 ★  
    Dokážte, že nemožno mať `P` aj `~P` zároveň: `~ (P /\ ~P)`. *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. Admitted.


(** Úloha 19 ★  
    Dokážte De Morganov zákon: `~ (P \/ Q) -> ~P /\ ~Q`. *)
Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof. Admitted.


(** Úloha 20 ★  
    Dokážte, že neplatí `forall n, S (pred n) = n`. *)
Lemma not_S_pred_n : ~(forall n : nat, S (pred n) = n).
Proof. Admitted.


(** Úloha 21 ★  
    Dokážte, že prázdny zoznam nie je tvaru `x :: xs`. *)
Theorem nil_is_not_cons : forall X (x : X) (xs : list X), ~ (nil = x :: xs).
Proof. Admitted.


(** Úloha 22 ★  
    Dokážte, že ekvivalencia je reflexívna: `P <-> P`. *)
Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof. Admitted.


(** Úloha 23 ★  
    Dokážte tranzitivitu ekvivalencie:  
    ak `P <-> Q` a `Q <-> R`, potom `P <-> R`. *)
Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof. Admitted.


(** Úloha 24 ★  
    Dokážte distribučný zákon: `P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R)`. *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. Admitted.


(** Úloha 25 ★  
    Dokážte, že ak `P x` platí pre všetky `x`, tak neexistuje `x`, pre ktorý `~P x`. *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. Admitted.


(** Úloha 26 ★  
    Dokážte, že existencia disjunkcie sa rozdeľuje:  
    `(exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x)`. *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof. Admitted.


(** Úloha 27 ★  
    Dokážte, že ak `n <=? m = true`, potom existuje `x` s `m = n + x`. *)
Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n+x.
Proof. Admitted.


(** Úloha 28 ★  
    Dokážte, že ak `m = n + x` pre nejaké `x`, potom `n <=? m = true`. *)
Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof. Admitted.

