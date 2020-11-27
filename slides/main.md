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

# Introduction

## Motivation

* One of the key elements of Iris success has been Iris Proof Mode \autocite{krebbersInteractiveProofsHigherorder2017}.
* In 2018, it was extended to MoSeL \autocite{krebbersMoSeLGeneralExtensible2018} -- a general framework for interactive proofs in separation logic.
* Can we do more for MoSeL?

## Motivation #1: Ltac

* MoSeL is implemented in Ltac
* There are multiple complains about Ltac, people are calling it names (and for a good reason!)
* Why don't we try reimplementing MoSeL in some other tactic language?
* Ltac2 is the new kid on the block
* Claims to be a sane successor to Ltac1
* Let's try it and see if we can do something cool along the way

## Motivation #2: \textnormal{\LARGE \texttt{iSplit}}

* It is annoying to provide resources explicitly every time you introduce a star
* Same goes for \coqe{iApply}
* Prior work: \citeauthor{harlandResourceDistributionBooleanConstraints2003} developed a solution based on Boolean flags
* Ltac1 is bad for working with evars, let's see if Ltac2 is better!

# Crash course in Ltac2

## ML-family language

## Notations

## Exceptions, mutable datatypes, and others

## Semantics

# iMatch

## Matching goals in Ltac/Ltac2

## Matching goals in MoSeL

## Different environments

## iLazyMatch, iMultiMatch

# iSplit

## Problem setting

## Solution by Harland and Pym

## How to port to MoSeL

## New environments

## New Coq tactics

## iSplit in action

# iSolver

## Let's put all this together

## Scope

# Conclusion

## Ltac2 lessons

## New MoSeL proof mode

---
\printbibliography

<!-- Local Variables: -->
<!-- mode: markdown; reftex -->
<!-- reftex-cite-format: biblatex -->
<!-- reftex-default-bibliography: ("/home/buzzer/my-dir/ed/uni/saar/prjcts/iris/npm/tex/TacticsProofs.bib") -->
<!-- End: -->
