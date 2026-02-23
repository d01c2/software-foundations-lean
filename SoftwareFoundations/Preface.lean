/-!
# Preface: Introduction and Overview

Ported from Software Foundations (Logical Foundations)
<https://softwarefoundations.cis.upenn.edu/lf-current/Preface.html>
-/

/-!
## Editor's Note

This chapter preserves the original narrative as closely as possible,
while presenting it in a Lean-idiomatic style.

Tool-specific setup details and Rocq-era phrasing have been revised
where needed so the prose reads naturally in this Lean edition.
-/

/-!
## Introduction

This is the entry point to a series of electronic textbooks on various
aspects of _Software Foundations_, the mathematical underpinnings of
reliable software. Topics in the series include basic concepts of logic,
computer-assisted theorem proving, functional programming, operational
semantics, logics and techniques for reasoning about programs, static
type systems, property-based random testing, and verification of
practical C code. The exposition is intended for a broad range of
readers, from advanced undergraduates to PhD students and researchers.
No specific background in logic or programming languages is assumed,
though a degree of mathematical maturity will be helpful.

The principal novelty of the series is that it is one hundred percent
formalized and machine-checked: each text is literally a script for a
proof assistant. The books are intended to be read alongside an
interactive session, and most of the exercises are designed to be
worked in that setting.

The files in each book are organized into a sequence of core chapters,
covering about one semester's worth of material and organized into a
coherent linear narrative, plus a number of offshoot chapters covering
additional topics. All the core chapters are suitable for both upper-level
undergraduate and graduate students.

This book, _Logical Foundations_, lays groundwork for the others,
introducing the reader to the basic ideas of functional programming,
constructive logic, and mechanized proof.
-/

-- =====================================================================
-- # Overview
-- =====================================================================

/-!
Building reliable software is hard -- really hard. The scale and complexity
of modern systems, the number of people involved, and the range of demands
placed on them make it challenging to build software that is even
more-or-less correct, much less 100% correct. At the same time, the
increasing degree to which information processing is woven into every
aspect of society greatly amplifies the cost of bugs and insecurities.

Computer scientists and software engineers have responded to these
challenges by developing a host of techniques for improving software
reliability, ranging from recommendations about managing software project
teams to design philosophies for libraries and programming languages to
mathematical techniques for specifying and reasoning about properties of
software and tools for helping validate these properties. The
_Software Foundations_ series is focused on this last set of tools.

This volume weaves together three conceptual threads:

1. basic tools from logic for making and justifying precise claims about programs;
2. the use of proof assistants to construct rigorous logical arguments;
3. functional programming, both as a method of programming that simplifies
   reasoning about programs and as a bridge between programming and logic.
-/

-- ## Logic

/-!
Logic is the field of study whose subject matter is proofs -- unassailable
arguments for the truth of particular propositions.

In particular, the fundamental tools of inductive proof are ubiquitous in
all of computer science. You have likely seen them before, perhaps in a
course on discrete math or analysis of algorithms, but this course examines
them in significantly more depth.
-/

-- ## Proof Assistants

/-!
The flow of ideas between logic and computer science has not been
unidirectional: computer science has also made important contributions to
logic. One of these has been the development of software tools for helping
construct proofs of logical propositions. These tools fall into two broad
categories:

1. Automated theorem provers provide push-button operation: you give them
   a proposition and they return either true or false (or sometimes
   "don't know: ran out of time").
2. Proof assistants are hybrid tools that automate routine parts of proof
   development while depending on human guidance for difficult parts.

This volume uses the second style throughout.
-/

-- ## Functional Programming

/-!
The term functional programming refers both to a collection of programming
idioms that can be used in almost any language and to a family of
programming languages designed to emphasize these idioms.

The most basic tenet of functional programming is that, as much as possible,
computation should be pure, in the sense that the only effect of execution
should be to produce a result. This tends to make programs easier to
understand and reason about, particularly in concurrent settings where
shared mutable state is a common source of subtle bugs.

Another practical benefit is that functional programs are often easier to
parallelize and distribute, because independent computations can be moved
and replicated with fewer concerns about hidden side effects.

For purposes of this course, functional programming has yet another key
attraction: it serves as a bridge between logic and computer science.
-/

-- ## Further Reading

/-!
This text is intended to be self-contained, but readers looking for deeper
treatment of particular topics will find suggestions for further reading in
the `Postscript` chapter.
-/
