---
author: Bohdan Liesnikov
institute:
- "Universität des Saarlandes"
- "Advisor: Robbert Krebbers"
- "Supervisor: Derek Dreyer"
title: Extending and Automating \text{Iris~Proof~Mode} with Ltac2
subtitle: "Master's thesis presentation"
date: November 30, 2020
classoption: "aspectratio=169"
fontsize: 12pt
navigation: empty
theme: default
colortheme: dove
fonttheme: structuresmallcapsserif
section-titles: true
listings: true
---

## Motivation

* One of the key elements of Iris success has been Iris Proof Mode \autocite{krebbersInteractiveProofsHigherorder2017}.
* In 2018, it was extended to MoSeL \autocite{krebbersMoSeLGeneralExtensible2018} -- a general framework for interactive proofs in separation logic.
* Can we do more for MoSeL?

## Motivation #1: Ltac

::: incremental

* MoSeL is implemented in Ltac
* There are many complaints about it, "PHP of tactic languages" \autocite{pedrotLtac2016}, etc.
* Why not reimplement MoSeL in a different language?
* Ltac2 is the new kid on the block
* Claims to be a sane successor to Ltac1
* Let's try it and see if we can do something cool along the way

:::

## Motivation #2: \textnormal{\LARGE \texttt{iSplit}}

* It is annoying to provide resources explicitly every time you introduce a "star".
* Same goes for \coqe{iApply}
* Prior work: Harland and Pym \autocite{harlandResourceDistributionBooleanConstraints2003} developed a solution based on Boolean flags
* Ltac1 is bad for working with evars, let's see if Ltac2 is better!

## Contributions

* Reimplement (part of) MoSeL in Ltac2
* Implement \coqe{iMatch} -- a MoSeL alternative for "\coqe{match goal}"
* Adapt solution with Boolean constraints from \autocite{harlandResourceDistributionBooleanConstraints2003}
* Put everything together to implement a simple solver

# What is Ltac2?

## ML-family language

* static types, prenex polymorphism, algebraic data types  
  ```
  Ltac2 Type ('a, 'b) sum := [Left ('a) | Right ('b)].
  Ltac2 Type rec int_list := [IntNil | IntCons (int, int_list)].
  ```
* (lambda-) functions  
  ```
  Ltac2 add_one (a : int) := Int.add a 1.
  ```
* pattern-matching
  ```
  Ltac2 rec all_gt_zero := fun (v : int_list) =>
    match v with
    | IntNil => true
    | IntCons h t => and (Int.gt h 0) (all_gt_zero t)
    end.
  ```

## Tactics and notations

* primitive tactics
  ```
  Ltac2 split_assumption () := repeat (first [split | assumption]).
  ```
* clear separation between Coq terms (\coqe{constr}) and Ltac2 terms
  ```
  Ltac2 is_conjunction (v : constr) := match! v with
  | ?p /\ ?q => true
  | _ => false
  end.
  ```
* notations and scopes
  ```
  Ltac2 Notation "is_conjunction_pretty" v(constr) := is_conjunction v.
  Ltac2 check1 () := is_conjunction constr:(True /\ False).
  Ltac2 check2 () := is_conjunction_pretty (True /\ False).
  ```

## Semantics

* Domain Specific Language (DSL) over a new tactic engine \autocite{pedrotCoqHoTTminuteTickingClockwork2016, spiwackAbstractTypeConstructing2010}
* `Control.zero : exn -> 'a`  
  throws a (catchable) exception
* `Control.plus : (unit -> 'a) -> (exn -> 'a) -> 'a`  
  inserts a new backtracking point
* `Control.case` takes apart backtracking values

```
Ltac2 regular_exn () := Control.zero (MyNewException "thrown exn").
Ltac2 catches_exn () := match Control.case (regular_exn) with
| Err e => match e with
  | MyNewException s => print (of_string s)
  end
| Val ans => let (x, k) := ans in
  Control.plus (fun _ => x) k
end
```

# iMatch

## Matching goals in Ltac1/Ltac2

* What if we have both $P$ and $Q$ in the context and the goal is exactly $P$?
  ```
  match goal with
  | [a:P, b:Q |- P] => exact a
  end
  ```
* Probably used in your faviourite automation tactic: `naive_solver` from stdpp library \autocite{std++developersandcontributorsStdpp}, one of the first examples in CPDT \autocite{chlipalaCertifiedProgrammingDependent2013}, etc. 

## Matching goals in MoSeL

* MoSeL stores contexts in the goal  
  \includegraphics[width=6cm]{proofstate}
* Ltac2 provides:  
  `Pattern.matches : pattern -> constr -> (ident * constr) list`  
  notation for patterns: `goal_matching`  
  proof state introspection: `match! goal` from the previous slide

## In action: silly \textnormal{\LARGE \texttt{iAssumption}}

::: columns

:::: column
```{coq}
Ltac2 i_assumption' () :=
  iMatch! goal with
  | [a : ?e -* ?f |- ?f] =>
    i_apply (imp_id a)
  | [a : ?e |- ?e] =>
    i_exact (ipm_id a)
  end.
```
::::

:::: column
\vspace{0.5em}
Example of a goal:

\texttt{"q" : Q\\
"p" : Q $\wand$ P\\
---------------------------------------*\\
P
}
::::

:::

\begin{center}
\hspace{-4em}
\coqe{do 2 (i_assumption' ())}
\end{center}


## Perks and limitations

* We can match Coq context, intuitionistic context, spatial context  
  ```
  iMatch! goal with
  | [a:P, b:Q |- _] => ...
  | [a:P, _:$\Vert$, b:Q |- _] => ...
  | [x: nat, _:$\Vert$, a:P, _:$\Vert$, b:Q |- _] => ...
  end
  ```
* No non-linearity, unfortunately  
  ```
  Ltac2 i_assumption' () :=
    iMatch! goal with
    | [a : ?e -* ?f |- _] => i_apply (imp_id a)
    | [a : ?e |- _] => i_exact (ipm_id a)
    end.
  ```

* \coqe{iLazyMatch}, \coqe{iMultiMatch}

# iSplit

## Proof with separating conjunction #1

$$
\infer{(A \wand B), C, A \vdash B * C}
      {}
$$

## Proof with separating conjunction #2

$$
\infer{(A \wand B), C, A \vdash B * C}
      {\infer{(A \wand B), A \vdash B}{} &
      \infer{C \vdash C}{}}
$$

## Proof with separating conjunction #3

$$
\infer{(A \wand B), C, A \vdash B * C}
      {\infer{(A \wand B), A \vdash B}
             {\infer{A \vdash A}{} &
              \infer{B \vdash B}{}} &
      \infer{C \vdash C}
            {}}
$$

## The culprit rule

$$
\infer{\Gamma \vdash \phi_1 \ast \phi_2}
        {\Gamma_1 \vdash \phi_1 &
         \Gamma_2 \vdash \phi_2}
$$

Going from the bottom up, there is no clue on how to split $\Gamma$ into $\Gamma_1$ and $\Gamma_2$.

## Solution by Harland and Pym \autocite{harlandResourceDistributionBooleanConstraints2003}

* Don't force decision upfront
* Make sure the resources in branches are disjoint
* When the resource is used propagate the decision
* Use Boolean flags, where \true = present, \false = absent

## Solution by Harland and Pym

$$
\hspace{-20pt}
\infer{(A \wand B), C, A \vdash B \ast C}
      {}
$$

## Solution by Harland and Pym

$$
\hspace{-20pt}
\infer{(A \wand B), C, A \vdash B \ast C}
      {(A \wand B)[c_0], C[c_1], A[c_2] \vdash B &
       (A \wand B)[\neg c_0], C[\neg c_1] , A[\neg c_2] \vdash C}
$$

\vspace{3em}

\centering

\pause{Let's do the left branch.}

## Solution by Harland and Pym

$$
\infer{(A \wand B)[c_0], C [c_1], A[c_2] \vdash B}
      {}
$$

\centering

Destruct the wand, then we have to provide it an $A$ and will get a $B$ in the context.

## Solution by Harland and Pym

$$
\infer{(A \wand B)[c_0], C [c_1], A[c_2] \vdash B}
      { \Gamma_{11} \vdash A &
        \Gamma_{12}, B[c_0] \vdash B &
        c_0 = \true}
$$


\centering

## Solution by Harland and Pym

$$
\infer{(A \wand B)[\true], C [c_1], A[c_2] \vdash B}
      { \Gamma_{11} \vdash A &
        \Gamma_{12}, B[\true] \vdash B}
$$

Again, we have to split $C [c_1], A[c_2]$ in $\Gamma_{11}$ and $\Gamma_{12}$.

## Solution by Harland and Pym

$$
\hspace{-10pt}
\infer{(A \wand B)[\true], C[c_1], A[c_2] \vdash B}
      {C [{\color{purple} c'_1}\& c_1], A[{\color{purple} c'_2} \& c_2] \vdash A &
       C[{\color{purple} \neg c'_1} \& c_1], A[{\color{purple} \neg c'_2} \& c_2], B[\true] \vdash B}
$$

## Solution by Harland and Pym

$$
\hspace{-10pt}
\infer{(A \wand B)[\true], C[c_1], A[c_2] \vdash B}
      {\infer{C [c'_1\& c_1], A[ c'_2 \& c_2] \vdash A}
             {A \vdash A &
             c'_2 \& c_2 = \true & c'_1\& c_1 = \false} &
       C[\neg c'_1 \& c_1], A[\neg c'_2 \& c_2], B[\true] \vdash B}
$$

## Solution by Harland and Pym

$$
\hspace{-10pt}
\infer{(A \wand B)[\true], C[c_1], A[\true] \vdash B}
      {\infer{C [c'_1\& c_1], A[\true] \vdash A}
             {A \vdash A &
             c'_1\& c_1 = \false} &
       \infer{C[\neg c'_1 \& c_1], A[\false], B[\true] \vdash B}
             {B \vdash B &
             \neg c'_1 \& c_1 = \false}}
$$

## Solution by Harland and Pym

$$
\hspace{-10pt}
\infer{(A \wand B)[\true], C[\false], A[\true] \vdash B}
      {\infer{C [\false], A[\true] \vdash A}
             {A \vdash A} &
       \infer{C[\false], A[\false], B[\true] \vdash B}
             {B \vdash B}}
$$

This was a left branch and it needed $A \wand B$ and $A$, but not $C$.  
So $C$ has to go to the right branch.

## How to port to MoSeL

\centering

\includegraphics[width=0.5\textwidth]{ipm-diagram}

## How to port to MoSeL

* New environments, indexed by \coqe{ident} and \coqe{bool}.
* Redefine entailment predicate:
  ```
  Definition envs_entails {PROP} ($\Delta$ : envs PROP) (Q : PROP):
  ($\ulcorner$ envs_wf $\Delta \urcorner$ /\ $\intuit$ [$\wedge$] env_intuitionistic $\Delta$ * [*] env_spatial $\Delta$) -* Q
  ```
  Where \coqe{[$\wedge$]} and \coqe{[*]} ignore \false resources
* New Coq lemmas, that take expressions into account
* Ltac2 layer on top to manage expressions

<!-- ## Example: destruct "and"

$$
\infer{\entails {\IntuD} {\SpatD,i : (P_1 \wedge P_2)[c]}  Q}
      {\entails {\IntuD}
                {\SpatD , P_1[c' \& c], P_2 [\neg c' \& c]}
                {Q} &
       c' \text{ is a fresh Boolean variable}}
$$

## New Coq Lemmas

```
Lemma tac_and_destruct_split Delta i p j1 j2 c c' P P1 P2 Q :
  envs_lookup_with_constr i Delta = Some (p, c, P) →
  (IntoAnd p P P1 P2) →
  match envs_simple_replace i p
                            (Esnoc (Esnoc Enil (negb c' && c, j2) P2)
                                               (     c' && c, j1) P1)
                            Delta with
  | None => False
  | Some Delta' => envs_entails Delta' Q
  end → envs_entails Delta Q.
``` -->

## Ltac2 layer

* Values of the Boolean expressions are only decided in the end
* Perfect use-case for \coqe{evars}
* Create new evars in \coqe{iSplit}
* Unify existing evars with \true or \false in \coqe{iAssumption}
* Tactics in action: simply swap all \coqe{iSplitL}, \coqe{iSplitR} for \coqe{iSplit}.

# iSolver

## Let's put it all together

* All of these features can play together
* Match the hypotheses, destruct them
* Based on the shape of the goal, apply the right tactic
* Only handle first-order things

## Code fragment

```
Ltac2 i_solver () := iLazyMatch! goal with
  | [a : (?p /\ ?q) |- _ ] =>
    i_and_destruct_split (ipm_id a) (i_fresh) (i_fresh)
  | [a : (?p * ?q) |- _ ] =>
    i_and_destruct (ipm_id a) (i_fresh) (i_fresh)
  | [ |- (?p * ?q)] =>
    i_sep_split ()
  | [ |- (?p -* ?q)] =>
    i_intro_ident (i_fresh)
  | ...
  end
```

\color{gray} Real syntax is a bit noisier

## What can it solve?

```
Lemma test_very_nested P1 P2 P3 P4 P5 :
  $\intuit$ P1 -* $\intuit$ (P1 -* P2) -* (P2 -* P2 -* P3) -*
  (P3 -* P4) -* (P4 -* P5) -* P5.
Proof. i_solver (). Qed.
```

## What can it solve?

```
Lemma test_big P1 P2 P3 P4 Q (P5 : nat → PROP) `{!Affine P4, !Absorbing P2} :
  P2 * (P3 * Q) * True * P1 * P2 * (P4 * (exists x : nat, P5 x \/ P3)) * emp -*
    P1 -* (True * True) -*
  (((P2 /\ False \/ P2 /\ $\ulcorner$0 = 0$\urcorner$) * P3) * Q * P1 * True) /\
    (P2 \/ False) /\ (False → P5 0).
Proof. i_solver (). Qed.
```

Both examples from the test suite.

\color{gray}
A problem: takes long time, approx. 1 minute.  
It seems to be because of backtracking in \coqe{iMatch} and slowness of interpretation.

# Conclusion

## Ltac2 lessons

* Language with solid foundations
* Still lacking some user-facing features
* Has special semantics, but they are predictable
* Maybe do not go full in just yet

## New things in MoSeL

* Matching MoSeL proof states
* Tactics without manual resource distribution
* It was important to use Ltac2, would be **hard** to do in Ltac1
* The way to bring more automation to MoSeL? Maybe

---

\centering

Thank you for the attention!  
Happy to answer any questions

## References {.allowframebreaks}

\bibliographytrue
\printbibliography[heading=none]

## Lines of Code

* Total LOC: ~4k
* Coq proofs: ~2k
* Ltac2 functions: ~2k

<!-- Local Variables: -->
<!-- mode: markdown; reftex -->
<!-- reftex-cite-format: biblatex -->
<!-- reftex-default-bibliography: ("/home/buzzer/my-dir/ed/uni/saar/prjcts/iris/npm/tex/TacticsProofs.bib") -->
<!-- End: -->
