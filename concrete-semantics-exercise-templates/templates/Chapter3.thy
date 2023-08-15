theory Chapter3
imports "HOL-IMP.BExp"
        "HOL-IMP.ASM"
        "Short_Theory"
begin

text\<open>
\section*{Chapter 3}

\exercise
To show that @{const asimp_const} really folds all subexpressions of the form
@{term "Plus (N i) (N j)"}, define a function
\<close>

fun optimal :: "aexp \<Rightarrow> bool" where
(* your definition/proof here *)

text\<open>
that checks that its argument does not contain a subexpression of the form
@{term "Plus (N i) (N j)"}. Then prove that the result of @{const asimp_const}
is optimal:
\<close>

lemma "optimal (asimp_const a)"
(* your definition/proof here *)

text\<open>
This proof needs the same \<open>split:\<close> directive as the correctness proof of
@{const asimp_const}. This increases the chance of nontermination
of the simplifier. Therefore @{const optimal} should be defined purely by
pattern matching on the left-hand side,
without \<open>case\<close> expressions on the right-hand side.
\endexercise


\exercise
In this exercise we verify constant folding for @{typ aexp}
where we sum up all constants, even if they are not next to each other.
For example, @{term "Plus (N 1) (Plus (V x) (N 2))"} becomes
@{term "Plus (V x) (N 3)"}. This goes beyond @{const asimp}.
Below we follow a particular solution strategy but there are many others.

First, define a function \<open>sumN\<close> that returns the sum of all
constants in an expression and a function \<open>zeroN\<close> that replaces all
constants in an expression by zeroes (they will be optimized away later):
\<close>

fun sumN :: "aexp \<Rightarrow> int" where
(* your definition/proof here *)

fun zeroN :: "aexp \<Rightarrow> aexp" where
(* your definition/proof here *)

text\<open>
Next, define a function \<open>sepN\<close> that produces an arithmetic expression
that adds the results of @{const sumN} and @{const zeroN}. Prove that
\<open>sepN\<close> preserves the value of an expression.
\<close>

definition sepN :: "aexp \<Rightarrow> aexp" where
(* your definition/proof here *)

lemma aval_sepN: "aval (sepN t) s = aval t s"
(* your definition/proof here *)

text\<open>
Finally, define a function \<open>full_asimp\<close> that uses @{const asimp}
to eliminate the zeroes left over by @{const sepN}.
Prove that it preserves the value of an arithmetic expression.
\<close>

definition full_asimp :: "aexp \<Rightarrow> aexp" where
(* your definition/proof here *)

lemma aval_full_asimp: "aval (full_asimp t) s = aval t s"
(* your definition/proof here *)



text\<open>
\endexercise


\exercise\label{exe:subst}
Substitution is the process of replacing a variable
by an expression in an expression. Define a substitution function
\<close>

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
(* your definition/proof here *)

text\<open>
such that @{term "subst x a e"} is the result of replacing
every occurrence of variable \<open>x\<close> by \<open>a\<close> in \<open>e\<close>.
For example:
@{lemma[display] "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')" by simp}

Prove the so-called \concept{substitution lemma} that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
\<close>

lemma subst_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
(* your definition/proof here *)

text\<open>
As a consequence prove that we can substitute equal expressions by equal expressions
and obtain the same result under evaluation:
\<close>
lemma "aval a1 s = aval a2 s
  \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
(* your definition/proof here *)

text\<open>
\endexercise

\exercise
Take a copy of theory @{short_theory "AExp"} and modify it as follows.
Extend type @{typ aexp} with a binary constructor \<open>Times\<close> that
represents multiplication. Modify the definition of the functions @{const aval}
and @{const asimp} accordingly. You can remove @{const asimp_const}.
Function @{const asimp} should eliminate 0 and 1 from multiplications
as well as evaluate constant subterms. Update all proofs concerned.
\<close>

text\<open>
\endexercise

\exercise
Define a datatype \<open>aexp2\<close> of extended arithmetic expressions that has,
in addition to the constructors of @{typ aexp}, a constructor for
modelling a C-like post-increment operation $x{++}$, where $x$ must be a
variable. Define an evaluation function \<open>aval2 :: aexp2 \<Rightarrow> state \<Rightarrow> val \<times> state\<close>
that returns both the value of the expression and the new state.
The latter is required because post-increment changes the state.

Extend \<open>aexp2\<close> and \<open>aval2\<close> with a division operation. Model partiality of
division by changing the return type of \<open>aval2\<close> to
@{typ "(val \<times> state) option"}. In case of division by 0 let \<open>aval2\<close>
return @{const None}. Division on @{typ int} is the infix \<open>div\<close>.
\<close>

text\<open>
\endexercise

\exercise
The following type adds a \<open>LET\<close> construct to arithmetic expressions:
\<close>

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

text\<open>The @{const LET} constructor introduces a local variable:
the value of @{term "LET x e\<^sub>1 e\<^sub>2"} is the value of \<open>e\<^sub>2\<close>
in the state where \<open>x\<close> is bound to the value of \<open>e\<^sub>1\<close> in the original state.
Define a function @{const lval} \<open>::\<close> @{typ "lexp \<Rightarrow> state \<Rightarrow> int"}
that evaluates @{typ lexp} expressions. Remember @{term"s(x := i)"}.

Define a conversion @{const inline} \<open>::\<close> @{typ "lexp \<Rightarrow> aexp"}.
The expression \mbox{@{term "LET x e\<^sub>1 e\<^sub>2"}} is inlined by substituting
the converted form of \<open>e\<^sub>1\<close> for \<open>x\<close> in the converted form of \<open>e\<^sub>2\<close>.
See Exercise~\ref{exe:subst} for more on substitution.
Prove that @{const inline} is correct w.r.t.\ evaluation.
\endexercise


\exercise
Show that equality and less-or-equal tests on \<open>aexp\<close> are definable
\<close>

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
(* your definition/proof here *)

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
(* your definition/proof here *)

text\<open>
and prove that they do what they are supposed to:
\<close>

lemma bval_Le: "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
(* your definition/proof here *)

lemma bval_Eq: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
(* your definition/proof here *)

text\<open>
\endexercise

\exercise
Consider an alternative type of boolean expressions featuring a conditional:\<close>

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

text\<open>First define an evaluation function analogously to @{const bval}:\<close>

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
(* your definition/proof here *)

text\<open>Then define two translation functions\<close>

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
(* your definition/proof here *)

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
(* your definition/proof here *)

text\<open>and prove their correctness:\<close>

lemma "bval (if2bexp exp) s = ifval exp s"
(* your definition/proof here *)

lemma "ifval (b2ifexp exp) s = bval exp s"
(* your definition/proof here *)

text\<open>
\endexercise

\exercise
We define a new type of purely boolean expressions without any arithmetic
\<close>

datatype pbexp =
  VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

text\<open>
where variables range over values of type @{typ bool},
as can be seen from the evaluation function:
\<close>

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x"  |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

text\<open>Define a function that checks whether a boolean exression is in NNF
(negation normal form), i.e., if @{const NOT} is only applied directly
to @{const VAR}s:\<close>

fun is_nnf :: "pbexp \<Rightarrow> bool" where
(* your definition/proof here *)

text\<open>
Now define a function that converts a \<open>bexp\<close> into NNF by pushing
@{const NOT} inwards as much as possible:
\<close>

fun nnf :: "pbexp \<Rightarrow> pbexp" where
(* your definition/proof here *)

text\<open>
Prove that @{const nnf} does what it is supposed to do:
\<close>

lemma pbval_nnf: "pbval (nnf b) s = pbval b s"
(* your definition/proof here *)

lemma is_nnf_nnf: "is_nnf (nnf b)"
(* your definition/proof here *)

text\<open>
An expression is in DNF (disjunctive normal form) if it is in NNF
and if no @{const OR} occurs below an @{const AND}. Define a corresponding
test:
\<close>

fun is_dnf :: "pbexp \<Rightarrow> bool" where
(* your definition/proof here *)

text\<open>
An NNF can be converted into a DNF in a bottom-up manner.
The critical case is the conversion of @{term (sub) "AND b1 b2"}.
Having converted \<open>b\<^sub>1\<close> and \<open>b\<^sub>2\<close>, apply distributivity of @{const AND}
over @{const OR}. If we write @{const OR} as a multi-argument function,
we can express the distributivity step as follows:
\<open>dist_AND (OR a\<^sub>1 ... a\<^sub>n) (OR b\<^sub>1 ... b\<^sub>m)\<close>
= \<open>OR (AND a\<^sub>1 b\<^sub>1) (AND a\<^sub>1 b\<^sub>2) ... (AND a\<^sub>n b\<^sub>m)\<close>. Define
\<close>

fun dist_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
(* your definition/proof here *)

text\<open>and prove that it behaves as follows:\<close>

lemma pbval_dist: "pbval (dist_AND b1 b2) s = pbval (AND b1 b2) s"
(* your definition/proof here *)

lemma is_dnf_dist: "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (dist_AND b1 b2)"
(* your definition/proof here *)

text\<open>Use @{const dist_AND} to write a function that converts an NNF
  to a DNF in the above bottom-up manner.
\<close>

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
(* your definition/proof here *)

text\<open>Prove the correctness of your function:\<close>

lemma "pbval (dnf_of_nnf b) s = pbval b s"
(* your definition/proof here *)

lemma "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
(* your definition/proof here *)

text\<open>
\endexercise


\exercise\label{exe:stack-underflow}
A \concept{stack underflow} occurs when executing an \<open>ADD\<close>
instruction on a stack of size less than 2. In our semantics
a term @{term "exec1 ADD s stk"} where @{prop "length stk < 2"}
is simply some unspecified value, not an error or exception --- HOL does not have those concepts.
Modify theory @{short_theory "ASM"}
such that stack underflow is modelled by @{const None}
and normal execution by \<open>Some\<close>, i.e., the execution functions
have return type @{typ "stack option"}. Modify all theorems and proofs
accordingly.
Hint: you may find \<open>split: option.split\<close> useful in your proofs.
\<close>

text\<open>
\endexercise

\exercise\label{exe:register-machine}
This exercise is about a register machine
and compiler for @{typ aexp}. The machine instructions are
\<close>
type_synonym reg = nat
datatype instr = LDI val reg | LD vname reg | ADD reg reg

text\<open>
where type \<open>reg\<close> is a synonym for @{typ nat}.
Instruction @{term "LDI i r"} loads \<open>i\<close> into register \<open>r\<close>,
@{term "LD x r"} loads the value of \<open>x\<close> into register \<open>r\<close>,
and @{term[names_short] "ADD r\<^sub>1 r\<^sub>2"} adds register \<open>r\<^sub>2\<close> to register \<open>r\<^sub>1\<close>.

Define the execution of an instruction given a state and a register state;
the result is the new register state:\<close>

type_synonym rstate = "reg \<Rightarrow> val"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
(* your definition/proof here *)

text\<open>
Define the execution @{const[source] exec} of a list of instructions as for the stack machine.

The compiler takes an arithmetic expression \<open>a\<close> and a register \<open>r\<close>
and produces a list of instructions whose execution places the value of \<open>a\<close>
into \<open>r\<close>. The registers \<open>> r\<close> should be used in a stack-like fashion
for intermediate results, the ones \<open>< r\<close> should be left alone.
Define the compiler and prove it correct:
\<close>

theorem "exec (comp a r) s rs r = aval a s"
(* your definition/proof here *)

text\<open>
\endexercise

\exercise\label{exe:accumulator}
This exercise is a variation of the previous one
with a different instruction set:
\<close>

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

text\<open>
All instructions refer implicitly to register 0 as a source or target:
@{const LDI0} and @{const LD0} load a value into register 0, @{term "MV0 r"}
copies the value in register 0 into register \<open>r\<close>, and @{term "ADD0 r"}
adds the value in register \<open>r\<close> to the value in register 0;
@{term "MV0 0"} and @{term "ADD0 0"} are legal. Define the execution functions
\<close>

fun exec01 :: "instr0 \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
(* your definition/proof here *)

text\<open>
and @{const exec0} for instruction lists.

The compiler takes an arithmetic expression \<open>a\<close> and a register \<open>r\<close>
and produces a list of instructions whose execution places the value of \<open>a\<close>
into register 0. The registers \<open>> r\<close> should be used in a stack-like fashion
for intermediate results, the ones \<open>\<le> r\<close> should be left alone
(with the exception of 0). Define the compiler and prove it correct:
\<close>

theorem "exec0 (comp0 a r) s rs 0 = aval a s"
(* your definition/proof here *)

text\<open>
\endexercise
\<close>

end

